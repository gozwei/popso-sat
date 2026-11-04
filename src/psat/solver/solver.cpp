// Solver setup, clause input, the main search loop, schedules (restarts, modes, rephasing) and
// limits.

#include "psat/solver/solver.hpp"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <new>
#include <stdexcept>

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
  if (proof_) proof_->add_unit(l);
}

void Solver::add_original_clause() {
  ++stats_.original_clauses;
  if (level() > 0) backtrack(0);
  if (inconsistent_) return;
  int max_v = 0;
  for (int d : adding_) max_v = std::max(max_v, std::abs(d));
  if (max_v > static_cast<int>(num_vars_)) grow_vars(static_cast<uint32_t>(max_v));
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
  arena_.resize(ref + kHeaderWords + size);
  Clause& c = clause(static_cast<uint32_t>(ref));
  c.size = size;
  c.glue = std::min<uint32_t>(glue, (1u << 20) - 1);
  c.used = redundant ? (glue <= static_cast<uint32_t>(opts_.tier2) ? 2 : 1) : 0;
  c.keep = redundant && glue <= static_cast<uint32_t>(opts_.tier1);
  c.reason = 0;
  c.garbage = 0;
  c.redundant = redundant;
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
  const int8_t x = vals_[2 * static_cast<size_t>(v - 1)];
  const bool truth = (x > 0) == (lit > 0);
  return truth ? lit : -lit;
}

int Solver::solve() {
  unknown_reason_ = "";
  if (!adding_.empty()) throw std::logic_error("solve() called with an unterminated clause");
  if (inconsistent_) return kUnsat;
  connect_pending();
  const int res = search();
  if (proof_) proof_->flush();
  return res;
}

int Solver::search() {
  for (;;) {
    if (!propagate()) {
      if (level() == 0) {
        inconsistent_ = true;
        if (proof_) proof_->add_empty();
        return kUnsat;
      }
      analyze();
    } else if (trail_.size() == num_vars_) {
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
    } else if (level() == 0 && fixed_ > last_simplify_fixed_ &&
               stats_.ticks >= simplify_ticks_limit_) {
      simplify_root();
    } else {
      decide();
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

void Solver::restart() {
  ++stats_.restarts;
  update_target_and_best(static_cast<uint32_t>(trail_.size()));
  backtrack(0);
  reluctant_.trigger = false;
  restart_limit_ = stats_.conflicts + static_cast<uint64_t>(opts_.restartint);
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
  // Focused and stable phases of a pair get the same ticks; each pair is longer by modegrowth.
  double length = static_cast<double>(mode_ticks_base_);
  const double growth = static_cast<double>(opts_.modegrowth) / 100.0;
  for (uint64_t pair = mode_count_ / 2; pair > 0; --pair) length *= growth;
  mode_limit_ticks_ = stats_.ticks + static_cast<uint64_t>(std::min(length, 1e18));
  mode_start_ticks_ = stats_.ticks;
  target_assigned_ = 0;
  if (stable_) {
    rebuild_heap();
    reluctant_.init(static_cast<uint64_t>(opts_.reluctantint), static_cast<uint64_t>(opts_.reluctantlim));
  } else {
    queue_search_ = queue_last_;
    restart_limit_ = stats_.conflicts + static_cast<uint64_t>(opts_.restartint);
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
  // Cycle: best, original, best, inverted.
  switch ((rephase_count_ - 1) % 4) {
    case 0:
    case 2:
      for (Var v = 0; v < num_vars_; ++v) {
        if (best_[v]) saved_[v] = best_[v];
      }
      break;
    case 1:
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
  std::fprintf(out, "c restarts       %14llu  rephased %llu  mode switches %llu\n", ull(stats_.restarts),
               ull(stats_.rephased), ull(stats_.switched));
  std::fprintf(out, "c reductions     %14llu  reduced %llu  collections %llu  root simplifications %llu\n",
               ull(stats_.reductions), ull(stats_.reduced_clauses), ull(stats_.collections), ull(stats_.simplified_root));
  std::fprintf(out, "c learned        %14llu  units %llu  binary %llu  avg size %.1f  minimized %.1f%%\n",
               ull(stats_.learned), ull(stats_.learned_units), ull(stats_.learned_binary),
               stats_.learned ? static_cast<double>(stats_.learned_literals) / static_cast<double>(stats_.learned) : 0.0,
               pct(stats_.minimized_literals, stats_.learned_literals + stats_.minimized_literals));
  std::fprintf(out, "c fixed          %14llu  of %u variables\n", ull(stats_.fixed), num_vars_);
  std::fprintf(out, "c memory         %14.1f MB\n", static_cast<double>(memory_bytes()) / (1 << 20));
  std::fprintf(out, "c time           %14.2f s\n", t);
}

}  // namespace psat
