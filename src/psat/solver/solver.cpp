// Solver setup, clause input, the main search loop, schedules (restarts, modes, rephasing) and
// limits.

#include "psat/solver/solver.hpp"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <new>
#include <stdexcept>

#include <sys/resource.h>

#include "psat/io/proof.hpp"

namespace psat {

Solver::Solver(const Options& opts) : opts_(opts) {
  start_ = std::chrono::steady_clock::now();
  rng_ = static_cast<uint64_t>(opts_.seed) * 0x9E3779B97F4A7C15ull + 0x2545F4914F6CDD1Dull;
  ema_fast_.init(static_cast<double>(opts_.emafast));
  ema_slow_.init(static_cast<double>(opts_.emaslow));
  stable_ = opts_.stable == 2;
  mode_limit_conflicts_ = static_cast<uint64_t>(opts_.modeinit);
  rephase_limit_ = static_cast<uint64_t>(opts_.rephaseint);
  reduce_limit_ = static_cast<uint64_t>(opts_.reduceint);
  restart_limit_ = static_cast<uint64_t>(opts_.restartint);
  eliminate_limit_ = static_cast<uint64_t>(opts_.eliminateinit);
  tier1_ = static_cast<uint32_t>(opts_.tier1);
  tier2_ = std::max(tier1_, static_cast<uint32_t>(opts_.tier2));
  vivify_limit_ = static_cast<uint64_t>(opts_.vivifyint);
  if (stable_) reluctant_.init(static_cast<uint64_t>(opts_.reluctantint), static_cast<uint64_t>(opts_.reluctantlim));
}

Solver::~Solver() = default;

double Solver::seconds() const {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - start_).count();
}

void Solver::reserve(int max_var) {
  if (max_var > kMaxVar) throw std::invalid_argument("too many variables");
  if (max_var > static_cast<int>(num_vars_)) grow_vars(static_cast<uint32_t>(max_var));
}

void Solver::reserve_clauses(int64_t clauses) {
  if (clauses <= 0 || clauses > (int64_t{1} << 28)) return;
  const size_t n = static_cast<size_t>(clauses);
  // Untouched reserved pages cost no physical memory; this avoids the 2-3x peak of growth.
  arena_.reserve(std::min<size_t>(arena_.size() + n * (kHeaderWords + 4), kMaxArenaWords));
  clauses_.reserve(clauses_.size() + n);
}

void Solver::grow_vars(uint32_t n) {
  const uint32_t old = num_vars_;
  vals_.resize(2 * size_t{n}, 0);
  vdata_.resize(n, VarData{0, kNoReason, 0});
  saved_.resize(n, opts_.phase ? 1 : -1);
  target_.resize(n, 0);
  best_.resize(n, 0);
  watches_.resize(2 * size_t{n});
  flags_.resize(n, 0);
  links_.resize(n);
  bumped_.resize(n, 0);
  score_.resize(n, 0.0);
  heap_.resize(n);
  levels_.resize(size_t{n} + 1);
  level_stamp_.resize(size_t{n} + 1, 0);
  eliminated_.resize(n, 0);
  touched_.resize(n, 1);
  marks_.resize(2 * size_t{n}, 0);
  trail_.reserve(n);
  num_vars_ = n;
  // New variables join the decision queue / heap; a nonzero seed shuffles their order.
  std::vector<Var> fresh;
  fresh.reserve(n - old);
  for (Var v = old; v < n; ++v) fresh.push_back(v);
  if (opts_.seed) {
    for (size_t i = fresh.size(); i > 1; --i) {
      rng_ ^= rng_ << 13;
      rng_ ^= rng_ >> 7;
      rng_ ^= rng_ << 17;
      std::swap(fresh[i - 1], fresh[rng_ % i]);
    }
  }
  for (Var v : fresh) {
    queue_enqueue_last(v);
    if (stable_) heap_.push(v);
  }
}

void Solver::add(int lit) {
  if (lit) {
    if (lit == INT32_MIN || std::abs(lit) > kMaxVar) throw std::invalid_argument("literal out of range");
    adding_.push_back(lit);
    return;
  }
  add_original_clause();
  adding_.clear();
}

void Solver::add_clause(const int* lits, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    if (lits[i] == 0 || lits[i] == INT32_MIN || std::abs(lits[i]) > kMaxVar) {
      throw std::invalid_argument("literal out of range");
    }
  }
  adding_.assign(lits, lits + n);
  add_original_clause();
  adding_.clear();
}

void Solver::on_root_fixed(Lit l) {
  ++fixed_;
  ++stats_.fixed;
  touched_[var_of(l)] = 1;
  if (proof_) proof_->add_unit(l);
}

void Solver::add_original_clause() {
  ++stats_.original_clauses;
  if (level() > 0) backtrack(0);
  model_valid_ = false;
  if (inconsistent_) return;
  int max_v = 0;
  for (int d : adding_) max_v = std::max(max_v, std::abs(d));
  if (max_v > static_cast<int>(num_vars_)) grow_vars(static_cast<uint32_t>(max_v));
  for (int d : adding_) {
    if (eliminated_[static_cast<size_t>(std::abs(d) - 1)]) {
      throw std::logic_error("adding a clause on an eliminated variable is not supported yet (use --no-eliminate)");
    }
  }
  clause_buf_.clear();
  for (int d : adding_) clause_buf_.push_back(from_dimacs(d));
  std::sort(clause_buf_.begin(), clause_buf_.end());
  const size_t before = clause_buf_.size();
  clause_buf_.erase(std::unique(clause_buf_.begin(), clause_buf_.end()), clause_buf_.end());
  bool changed = clause_buf_.size() != before;
  // Sorted: a literal and its negation are adjacent.
  for (size_t i = 1; i < clause_buf_.size(); ++i) {
    if (clause_buf_[i] == negate(clause_buf_[i - 1])) return;  // tautology
  }
  size_t j = 0;
  for (size_t i = 0; i < clause_buf_.size(); ++i) {
    const int8_t v = value(clause_buf_[i]);
    if (v > 0) return;  // satisfied by a root-level unit
    if (v < 0) {
      changed = true;
      continue;
    }
    clause_buf_[j++] = clause_buf_[i];
  }
  clause_buf_.resize(j);
  if (changed && proof_ && !clause_buf_.empty()) proof_->add(clause_buf_.data(), clause_buf_.size());
  if (clause_buf_.empty()) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return;
  }
  if (clause_buf_.size() == 1) {
    assign(clause_buf_[0], kNoReason);
    return;
  }
  if (clause_buf_.size() == 2) {
    pending_binaries_.push_back(clause_buf_[0]);
    pending_binaries_.push_back(clause_buf_[1]);
    ++binaries_irredundant_;
    return;
  }
  new_clause(clause_buf_.data(), static_cast<uint32_t>(clause_buf_.size()), false, 0, false);
}

void Solver::connect_pending() {
  if (watched_clauses_ == clauses_.size() && pending_binaries_.empty()) return;
  std::vector<uint32_t> count(2 * size_t{num_vars_}, 0);
  for (const Lit l : pending_binaries_) ++count[l];
  for (size_t i = watched_clauses_; i < clauses_.size(); ++i) {
    const Lit* lits = clause(clauses_[i]).lits();
    ++count[lits[0]];
    ++count[lits[1]];
  }
  for (size_t l = 0; l < count.size(); ++l) {
    if (count[l]) watches_[l].reserve(watches_[l].size() + count[l]);
  }
  for (size_t i = 0; i < pending_binaries_.size(); i += 2) {
    const Lit a = pending_binaries_[i], b = pending_binaries_[i + 1];
    watches_[a].push_back(Watch{b, kBinaryTag});
    watches_[b].push_back(Watch{a, kBinaryTag});
  }
  for (size_t i = watched_clauses_; i < clauses_.size(); ++i) watch_clause(clauses_[i]);
  watched_clauses_ = clauses_.size();
  pending_binaries_.clear();
  pending_binaries_.shrink_to_fit();
}

uint32_t Solver::new_clause(const Lit* lits, uint32_t size, bool redundant, uint32_t glue, bool watch) {
  const size_t ref = arena_.size();
  if (ref + kHeaderWords + size > kMaxArenaWords) throw std::bad_alloc();
  if (ref + kHeaderWords + size > arena_.capacity()) {
    // Grow by a quarter (not doubled by the vector): the old and new blocks coexist while the
    // arena is copied, and the arena is the largest structure on big formulas.
    const size_t want = std::max(ref + kHeaderWords + size, arena_.capacity() + arena_.capacity() / 4 + 1024);
    arena_.reserve(std::min<size_t>(want, kMaxArenaWords));
  }
  arena_.resize(ref + kHeaderWords + size);
  Clause& c = clause(static_cast<uint32_t>(ref));
  c.size = size;
  c.glue = std::min<uint32_t>(glue, (1u << 20) - 1);
  c.used = redundant ? (glue <= tier2_ ? 2 : 1) : 0;
  c.keep = redundant && glue <= tier1_;
  c.reason = 0;
  c.garbage = 0;
  c.redundant = redundant;
  c.vivified = 0;
  c.spare = 0;
  c.pos = 2;
  std::copy(lits, lits + size, c.lits());
  clauses_.push_back(static_cast<uint32_t>(ref));
  if (redundant) {
    ++redundant_;
  } else {
    ++irredundant_;
  }
  if (watch) {
    watch_clause(static_cast<uint32_t>(ref));
    watched_clauses_ = clauses_.size();
  }
  return static_cast<uint32_t>(ref);
}

void Solver::watch_clause(uint32_t ref) {
  const Lit* l = clause(ref).lits();
  watches_[l[0]].push_back(Watch{l[1], ref});
  watches_[l[1]].push_back(Watch{l[0], ref});
}

void Solver::add_binary(Lit a, Lit b, bool redundant) {
  const uint32_t tag = kBinaryTag | (redundant ? 1u : 0u);
  watches_[a].push_back(Watch{b, tag});
  watches_[b].push_back(Watch{a, tag});
  if (redundant) {
    ++binaries_redundant_;
  } else {
    ++binaries_irredundant_;
  }
}

int Solver::val(int lit) const {
  const int v = std::abs(lit);
  if (v == 0 || v > static_cast<int>(num_vars_)) return -lit;
  const int8_t x = model_valid_ ? model_[static_cast<size_t>(v - 1)] : vals_[2 * static_cast<size_t>(v - 1)];
  const bool truth = (x > 0) == (lit > 0);
  return truth ? lit : -lit;
}

int Solver::solve() {
  unknown_reason_ = "";
  if (!adding_.empty()) throw std::logic_error("solve() called with an unterminated clause");
  if (inconsistent_) return kUnsat;
  connect_pending();
  if (opts_.lucky && !lucky_tried_) {
    lucky_tried_ = true;
    lucky_limit_ = stats_.vivify_ticks + 8 * (arena_.size() / 8 + num_vars_) + 100000;
    if (lucky()) {
      extend_model();
      if (opts_.verbose) std::printf("c lucky assignment found\n");
      if (proof_) proof_->flush();
      return kSat;
    }
  }
  const int res = search();
  if (proof_) proof_->flush();
  return res;
}

int Solver::search() {
  for (;;) {
    if (!propagate()) {
      if (level() == 0 || !analyze()) {  // (analyze: the conflict can be at the root)
        inconsistent_ = true;
        if (proof_) proof_->add_empty();
        return kUnsat;
      }
    } else if (trail_.size() + inactive_ == num_vars_) {
      extend_model();
      return kSat;
    } else if (check_limits()) {
      return kUnknown;
    } else if (restarting()) {
      restart();
    } else if (rephasing()) {
      rephase();
    } else if (reducing()) {
      reduce();
    } else if (switching()) {
      switch_mode();
    } else if (eliminating()) {
      eliminate();
      if (inconsistent_) return kUnsat;
      if (propagate()) debug_check("eliminate");
    } else if (opts_.sweep && !sweep_initial_done_ && level() == 0) {
      // One sweep before the first decision (after the first elimination round), as Kissat's
      // preprocessing does: miters give up many equivalences early.
      sweep_initial_done_ = true;
      sweep(1'000'000 + arena_.size() / 2);
      if (inconsistent_) return kUnsat;
    } else if (vivifying()) {
      vivify();
      if (inconsistent_) return kUnsat;
      debug_check("vivify");
    } else if (level() == 0 && fixed_ > last_simplify_fixed_ &&
               stats_.ticks >= simplify_ticks_limit_) {
      simplify_root();
    } else {
      decide();
    }
  }
}

// Debugging aid (PSAT_DEBUG set in the environment): watch invariants at a fully propagated root.
void Solver::debug_check(const char* where) {
  if (!opts_.invariants || level() != 0 || propagated_ != trail_.size()) return;
  auto fail = [&](const char* what, uint32_t ref) {
    std::fprintf(stderr, "c DEBUG after %s: %s (clause %u, conflicts %llu)\n", where, what, ref,
                 static_cast<unsigned long long>(stats_.conflicts));
    std::abort();
  };
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    const Lit* l = c.lits();
    for (int w = 0; w < 2; ++w) {
      bool found = false;
      for (const Watch& x : watches_[l[w]]) found = found || (!x.binary() && x.ref == ref);
      if (!found) fail("watched literal without watch", ref);
    }
    bool sat = false, unassigned = false;
    for (uint32_t k = 0; k < c.size; ++k) {
      sat = sat || vals_[l[k]] > 0;
      unassigned = unassigned || vals_[l[k]] == 0;
    }
    if (!sat && (vals_[l[0]] < 0 || vals_[l[1]] < 0)) fail("false watched literal in unsatisfied clause", ref);
    if (!sat && !unassigned) fail("falsified clause", ref);
    for (uint32_t k = 0; k < c.size; ++k) {
      if (eliminated_[var_of(l[k])]) {
        std::fprintf(stderr, "c DEBUG clause %u size %u redundant %u glue %u vivified %u:", ref, c.size, c.redundant,
                     c.glue, c.vivified);
        for (uint32_t m = 0; m < c.size; ++m) std::fprintf(stderr, " %d%s", to_dimacs(l[m]), eliminated_[var_of(l[m])] ? "*" : "");
        std::fprintf(stderr, "\n");
        fail("eliminated variable in clause", ref);
      }
    }
  }
  for (Lit a = 0; a < 2 * num_vars_; ++a) {
    for (const Watch& w : watches_[a]) {
      if (!w.binary()) continue;
      if (vals_[a] < 0 && vals_[w.blit] <= 0) fail("binary clause not propagated", a);
    }
  }
}

bool Solver::check_limits() {
  if (terminate_ && terminate_->load(std::memory_order_relaxed)) {
    unknown_reason_ = "interrupted";
    return true;
  }
  if (conflict_limit_ >= 0 && stats_.conflicts >= static_cast<uint64_t>(conflict_limit_)) {
    unknown_reason_ = "conflict limit";
    return true;
  }
  if ((++limit_check_ & 1023) != 0) return false;
  if (time_limit_ > 0 && seconds() >= time_limit_) {
    unknown_reason_ = "time limit";
    return true;
  }
  if (memory_limit_ && (limit_check_ & 65535) == 0 && memory_bytes() > memory_limit_) {
    unknown_reason_ = "memory limit";
    return true;
  }
  return false;
}

double Solver::peak_rss_mb() {
  struct rusage u {};
  if (getrusage(RUSAGE_SELF, &u) != 0) return 0;
#ifdef __APPLE__
  return static_cast<double>(u.ru_maxrss) / (1 << 20);  // bytes
#else
  return static_cast<double>(u.ru_maxrss) / 1024;  // kilobytes
#endif
}

size_t Solver::memory_bytes() const {
  size_t bytes = arena_.capacity() * 4 + clauses_.capacity() * 4;
  bytes += vals_.capacity() + vdata_.capacity() * sizeof(VarData) + 3 * saved_.capacity();
  bytes += trail_.capacity() * 4 + flags_.capacity() + links_.capacity() * sizeof(Link) + bumped_.capacity() * 8;
  bytes += score_.capacity() * 8 + num_vars_ * 4 + levels_.capacity() * sizeof(LevelInfo) + level_stamp_.capacity() * 8;
  bytes += watches_.capacity() * sizeof(std::vector<Watch>);
  for (const auto& ws : watches_) bytes += ws.capacity() * sizeof(Watch);
  return bytes;
}

// --- restarts --------------------------------------------------------------------------------

bool Solver::restarting() const {
  if (level() == 0) return false;
  if (stable_) return reluctant_.trigger;
  if (stats_.conflicts < restart_limit_) return false;
  const double margin = 1.0 + static_cast<double>(opts_.restartmargin) / 100.0;
  return ema_fast_.value > margin * ema_slow_.value;
}

bool Solver::backtrack_to_root() {
  backtrack(0);
  if (propagated_ < trail_.size() && !propagate()) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return false;
  }
  return true;
}

void Solver::restart() {
  ++stats_.restarts;
  update_target_and_best(static_cast<uint32_t>(trail_.size()));
  const uint32_t keep = reuse_trail_level();
  stats_.reused_levels += keep;
  backtrack(keep);
  reluctant_.trigger = false;
  restart_limit_ = stats_.conflicts + focused_restart_interval();
}

// Conflicts before the next focused-mode restart may be considered. Right after a restart the
// fast glue average is still above the slow one, so with a fixed interval of 1 restarts come in
// bursts (one per conflict); with --restartgrow the interval grows with the decimal logarithm of
// the restart count (1 below 91 restarts, 2 below 991, ...), as long runs need fewer of them.
uint64_t Solver::focused_restart_interval() const {
  uint64_t delta = static_cast<uint64_t>(opts_.restartint);
  if (opts_.restartgrow) {
    for (uint64_t r = stats_.restarts + 9; r >= 100; r /= 10) ++delta;
  }
  return delta;
}

// Trail reuse (van der Tak, Ramos & Heule 2011): the decisions of levels 1..k whose variables rank
// above the next decision variable (EVSIDS score, or VMTF enqueue time) would be taken again in
// the same order, so the restart keeps them instead of propagating them again.
uint32_t Solver::reuse_trail_level() {
  if (!opts_.reusetrail || level() == 0) return 0;
  const Var next = stable_ ? next_stable() : next_focused();
  uint32_t keep = 0;
  while (keep < level()) {
    const Var d = var_of(trail_[control_[keep]]);  // the decision of level keep + 1
    if (stable_ ? !(score_[d] > score_[next]) : !(bumped_[d] > bumped_[next])) break;
    ++keep;
  }
  return keep;
}

void Solver::update_conflict_statistics(uint32_t glue) {
  ema_fast_.update(glue);
  ema_slow_.update(glue);
  if (stable_ && opts_.reluctant) reluctant_.tick();
}

// --- modes -----------------------------------------------------------------------------------

bool Solver::switching() const {
  if (opts_.stable != 1) return false;
  if (mode_count_ == 0) return stats_.conflicts >= mode_limit_conflicts_;
  return stats_.ticks >= mode_limit_ticks_;
}

void Solver::switch_mode() {
  const uint64_t spent = stats_.ticks - mode_start_ticks_;
  if (mode_count_ == 0) mode_ticks_base_ = std::max<uint64_t>(spent, 1000);
  ++mode_count_;
  ++stats_.switched;
  update_target_and_best(static_cast<uint32_t>(trail_.size()));
  backtrack(0);
  stable_ = !stable_;
  // Focused and stable phases of a pair get the same ticks; each pair is longer by modegrowth
  // (geometric), or the length is the base times the square of the pair number (quadratic, closer
  // to Kissat: over long runs the modes keep alternating instead of one phase taking most time).
  double length = static_cast<double>(mode_ticks_base_);
  if (opts_.modeschedule == 1) {
    const double pair = static_cast<double>(mode_count_ / 2 + 1);
    length *= pair * pair;
  } else {
    const double growth = static_cast<double>(opts_.modegrowth) / 100.0;
    for (uint64_t pair = mode_count_ / 2; pair > 0; --pair) length *= growth;
  }
  mode_limit_ticks_ = stats_.ticks + static_cast<uint64_t>(std::min(length, 1e18));
  mode_start_ticks_ = stats_.ticks;
  target_assigned_ = 0;
  if (stable_) {
    rebuild_heap();
    reluctant_.init(static_cast<uint64_t>(opts_.reluctantint), static_cast<uint64_t>(opts_.reluctantlim));
  } else {
    queue_search_ = queue_last_;
    restart_limit_ = stats_.conflicts + focused_restart_interval();
  }
  if (opts_.verbose >= 2) {
    std::printf("c [%.2f s] switched to %s mode after %llu conflicts\n", seconds(), stable_ ? "stable" : "focused",
                static_cast<unsigned long long>(stats_.conflicts));
  }
}

// --- rephasing -------------------------------------------------------------------------------

void Solver::rephase() {
  ++stats_.rephased;
  ++rephase_count_;
  const int8_t initial = opts_.phase ? 1 : -1;
  // Cycle: best, walk, original, best, walk, inverted (without walk: best, original, best, inverted).
  static const char kWithWalk[] = "BWOBWI";
  static const char kWithoutWalk[] = "BOBI";
  const char kind = opts_.walk ? kWithWalk[(rephase_count_ - 1) % 6] : kWithoutWalk[(rephase_count_ - 1) % 4];
  switch (kind) {
    case 'B':
      for (Var v = 0; v < num_vars_; ++v) {
        if (best_[v]) saved_[v] = best_[v];
      }
      break;
    case 'W':
      walk();
      break;
    case 'O':
      std::fill(saved_.begin(), saved_.end(), initial);
      break;
    default:
      std::fill(saved_.begin(), saved_.end(), static_cast<int8_t>(-initial));
      break;
  }
  std::copy(saved_.begin(), saved_.end(), target_.begin());
  target_assigned_ = 0;
  best_assigned_ = 0;
  rephase_limit_ = stats_.conflicts + static_cast<uint64_t>(opts_.rephaseint) * rephase_count_;
}

void Solver::update_target_and_best(uint32_t consistent) {
  const bool use_target = opts_.target == 2 || (opts_.target == 1 && stable_);
  if (use_target && consistent > target_assigned_) {
    for (uint32_t i = 0; i < consistent; ++i) {
      const Lit l = trail_[i];
      target_[var_of(l)] = is_negative(l) ? -1 : 1;
    }
    target_assigned_ = consistent;
  }
  if (consistent > best_assigned_) {
    for (uint32_t i = 0; i < consistent; ++i) {
      const Lit l = trail_[i];
      best_[var_of(l)] = is_negative(l) ? -1 : 1;
    }
    best_assigned_ = consistent;
  }
}

// --- statistics ------------------------------------------------------------------------------

void Solver::print_statistics(std::FILE* out) const {
  const double t = seconds();
  auto rate = [t](uint64_t x) { return t > 0 ? static_cast<double>(x) / t : 0.0; };
  auto pct = [](uint64_t a, uint64_t b) { return b ? 100.0 * static_cast<double>(a) / static_cast<double>(b) : 0.0; };
  auto ull = [](uint64_t x) { return static_cast<unsigned long long>(x); };
  std::fprintf(out, "c\nc ---- statistics ----\n");
  std::fprintf(out, "c conflicts      %14llu  %10.0f /s  (stable %.0f%%)\n", ull(stats_.conflicts), rate(stats_.conflicts),
               pct(stats_.stable_conflicts, stats_.conflicts));
  std::fprintf(out, "c decisions      %14llu  %10.0f /s\n", ull(stats_.decisions), rate(stats_.decisions));
  std::fprintf(out, "c propagations   %14llu  %10.0f /s\n", ull(stats_.propagations), rate(stats_.propagations));
  std::fprintf(out, "c ticks          %14llu\n", ull(stats_.ticks));
  std::fprintf(out, "c restarts       %14llu  reused levels %llu  rephased %llu  mode switches %llu\n",
               ull(stats_.restarts), ull(stats_.reused_levels), ull(stats_.rephased), ull(stats_.switched));
  std::fprintf(out, "c chronological  %14llu  backtracks to the conflict level %llu  missed implications %llu\n",
               ull(stats_.chrono_backtracks), ull(stats_.chrono_conflict_backtracks), ull(stats_.chrono_missed));
  std::fprintf(out, "c reductions     %14llu  reduced %llu  root simplifications %llu\n", ull(stats_.reductions),
               ull(stats_.reduced_clauses), ull(stats_.simplified_root));
  std::fprintf(out, "c collections    %14llu  full %llu  arena %.1f MB, collected %.1f MB\n", ull(stats_.collections),
               ull(stats_.collections_full), static_cast<double>(arena_.size()) * 4 / 1e6,
               static_cast<double>(stats_.collected_words) * 4 / 1e6);
  std::fprintf(out, "c learned        %14llu  units %llu  binary %llu  avg size %.1f  minimized %.1f%%  eager subsumed %llu\n",
               ull(stats_.learned), ull(stats_.learned_units), ull(stats_.learned_binary),
               stats_.learned ? static_cast<double>(stats_.learned_literals) / static_cast<double>(stats_.learned) : 0.0,
               pct(stats_.minimized_literals, stats_.learned_literals + stats_.minimized_literals),
               ull(stats_.eager_subsumed));
  std::fprintf(out,
               "c eliminations   %14llu  eliminated %llu  substituted %llu  resolvents %llu  subsumed %llu  "
               "strengthened %llu\n",
               ull(stats_.eliminations), ull(stats_.eliminated), ull(stats_.substituted), ull(stats_.resolvents),
               ull(stats_.subsumed), ull(stats_.strengthened));
  std::fprintf(out, "c vivifications  %14llu  checked %llu  vivified %llu  removed literals %llu  instantiated %llu  "
                    "implied deleted %llu  asym deleted %llu  ticks %llu\n",
               ull(stats_.vivifications), ull(stats_.vivify_checked), ull(stats_.vivified),
               ull(stats_.vivified_literals), ull(stats_.vivify_instantiated), ull(stats_.vivify_implied_deleted),
               ull(stats_.vivify_asym), ull(stats_.vivify_ticks));
  std::fprintf(out, "c probing        %14llu  failed literals %llu\n", ull(stats_.probes), ull(stats_.failed_literals));
  std::fprintf(out, "c unhiding       %14llu  units %llu  transitive %llu  hidden tautologies %llu  strengthened %llu  "
                    "removed literals %llu  ticks %llu\n",
               ull(stats_.unhides), ull(stats_.unhide_units), ull(stats_.unhide_transitive), ull(stats_.unhide_tautologies),
               ull(stats_.unhide_strengthened), ull(stats_.unhide_literals), ull(stats_.unhide_ticks));
  std::fprintf(out, "c sweeping       %14llu  variables %llu  units %llu  equivalences %llu  flips %llu  ticks %llu  "
                    "(kitten %llu in %llu solves)  limits %u vars / %u clauses / depth %u (growth %u)\n",
               ull(stats_.sweeps), ull(stats_.swept_vars), ull(stats_.sweep_units), ull(stats_.sweep_equivalences),
               ull(stats_.sweep_flips), ull(stats_.sweep_ticks), ull(stats_.sweep_kitten_ticks), ull(stats_.sweep_solves),
               sweep_lim_vars_, sweep_lim_clauses_, sweep_lim_depth_, sweep_growth_);
  std::fprintf(out, "c simulation     %14llu  gates %llu (ite %llu)  candidates %llu  checked %llu  equivalences %llu  units %llu  "
                    "failed %llu  ticks %llu\n",
               ull(stats_.simulations), ull(stats_.sim_gates), ull(stats_.sim_ites), ull(stats_.sim_candidates), ull(stats_.sim_checked),
               ull(stats_.sim_equivalences), ull(stats_.sim_units), ull(stats_.sim_failed), ull(stats_.sim_ticks));
  std::fprintf(out, "c gates          %14llu  (definitions in elimination: xor %llu, ite %llu, semantic %llu; xor merges skipped %llu)  congruent outputs %llu (xor %llu, ite %llu)\n",
               ull(stats_.gates), ull(stats_.xor_gates), ull(stats_.ite_gates), ull(stats_.definitions),
               ull(stats_.xor_merges_skipped), ull(stats_.congruent), ull(stats_.congruent_xors), ull(stats_.congruent_ites));
  std::fprintf(out, "c lucky          %14llu\n", ull(stats_.lucky));
  std::fprintf(out, "c walks          %14llu  flips %llu  ticks %llu\n", ull(stats_.walks), ull(stats_.walk_flips),
               ull(stats_.walk_ticks));
  std::fprintf(out, "c bva            %14llu  variables, clauses removed %llu added %llu, 3-hop tie-breaks %llu, "
               "trials %llu (rounds made %llu)\n",
               ull(stats_.bva_vars), ull(stats_.bva_removed), ull(stats_.bva_added), ull(stats_.bva_hop_ties),
               ull(stats_.bva_trials), ull(stats_.bva_rounds));
  std::fprintf(out, "c tiers          %14u  tier2 %u\n", tier1_, tier2_);
  std::fprintf(out, "c shrunk         %14llu  literals\n", ull(stats_.shrunk_literals));
  std::fprintf(out, "c fixed          %14llu  of %u variables\n", ull(stats_.fixed), num_vars_);
  std::fprintf(out, "c memory         %14.1f MB  (peak resident %.1f MB)\n", static_cast<double>(memory_bytes()) / (1 << 20),
               peak_rss_mb());
  std::fprintf(out, "c time           %14.2f s\n", t);
  {
    // Exclusive wall time of the passes; search is the rest (with garbage collection).
    const double* p = pass_seconds_;
    double passes = 0;
    for (int k = 0; k < kPassCount; ++k) passes += p[k];
    auto share = [t](double x) { return t > 0 ? 100.0 * x / t : 0.0; };
    std::fprintf(out, "c profile        search %.2f s (%.0f%%)  sweep %.2f (%.0f%%)  vivify %.2f (%.0f%%)  eliminate %.2f (%.0f%%)  "
                      "walk %.2f (%.0f%%)\n",
                 t - passes, share(t - passes), p[kPassSweep], share(p[kPassSweep]), p[kPassVivify], share(p[kPassVivify]),
                 p[kPassEliminate], share(p[kPassEliminate]), p[kPassWalk], share(p[kPassWalk]));
    std::fprintf(out, "c                probe %.2f  substitute %.2f  congruence %.2f  subsume %.2f  bva %.2f  reduce %.2f  "
                      "lucky %.2f  unhide %.2f  simulate %.2f s\n",
                 p[kPassProbe], p[kPassSubstitute], p[kPassCongruence], p[kPassSubsume], p[kPassBva], p[kPassReduce],
                 p[kPassLucky], p[kPassUnhide], p[kPassSimulate]);
  }
}

}  // namespace psat
