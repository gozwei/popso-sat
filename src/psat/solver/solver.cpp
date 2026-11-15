// Solver setup, clause input, the main search loop, schedules (restarts, modes, rephasing) and
// limits.

#include "psat/solver/solver.hpp"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <new>
#include <stdexcept>

#include <sys/resource.h>
#include <unistd.h>
#if defined(__APPLE__) && defined(__clang__)  // (g++ cannot parse the SDK's mach headers)
#include <mach/mach.h>
#include <malloc/malloc.h>
#endif
#if defined(__GLIBC__) && (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 33))
#include <malloc.h>
#define PSAT_MALLINFO2 1
#endif

#include "psat/core/small_sort.hpp"
#include "psat/io/proof.hpp"

namespace psat {

Solver::Solver(const Options& opts) : opts_(opts) {
  watches_.set_stress(opts_.watchstress != 0);
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
  randec_limit_ = static_cast<uint64_t>(opts_.randecint);
  randec_rng_ = static_cast<uint64_t>(opts_.seed) * 0xD1B54A32D192ED03ull + 0x8CB92BA72F3D8DD7ull;
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
  // Capacity grows by an eighth at a time once there are variables: std::vector's resize doubles
  // it, and BVA adds its variables one at a time (ncc_none_3001: 22,584 BVA variables on 1.6M
  // doubled every per-variable array, 107 -> 201 MB, and the trail, reserved at the exact size,
  // was reallocated for each of them). The first call (the input's header) reserves exactly.
  if (n > vdata_.capacity()) {
    const size_t cap = std::max<size_t>(n, vdata_.capacity() + vdata_.capacity() / 8);
    vals_.reserve(2 * cap);
    vdata_.reserve(cap);
    saved_.reserve(cap);
    target_.reserve(cap);
    best_.reserve(cap);
    watches_.reserve_lists(2 * cap);
    flags_.reserve(cap);
    links_.reserve(cap);
    bumped_.reserve(cap);
    score_.reserve(cap);
    heap_.reserve(cap);
    levels_.reserve(cap + 1);
    level_stamp_.reserve(cap + 1);
    eliminated_.reserve(cap);
    touched_.reserve(cap);
    marks_.reserve(2 * cap);
    trail_.reserve(cap);
  }
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
  if (n > touched_.size()) touched_count_ += n - touched_.size();
  touched_.resize(n, 1);
  marks_.resize(2 * size_t{n}, 0);
  trail_.reserve(n);
  num_vars_ = n;
  // (renumber.cpp permutes the arrays above.) After a renumbering, new variables keep their index.
  if (!renum_ext_.empty()) {
    for (Lit l = 2 * old; l < 2 * n; ++l) renum_ext_.push_back(l);
  }
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

void Solver::set_proof(ProofWriter* proof) {
  proof_ = proof;
  if (proof_ && !renum_ext_.empty()) proof_->set_map(&renum_ext_);
}

void Solver::on_root_fixed(Lit l) {
  ++fixed_;
  ++stats_.fixed;
  touch_var(var_of(l));
  if (proof_ && !unit_in_proof_) proof_->add_unit(l);
}

void Solver::add_original_clause() {
  ++stats_.original_clauses;
  if (gauss_tried_) {  // the detached Gauss-Jordan solver has an older copy of the formula
    gauss_sub_.reset();
    gauss_tried_ = false;
  }
  if (level() > 0) backtrack(0);
  model_valid_ = false;
  if (inconsistent_) return;
  int max_v = 0;
  for (int d : adding_) max_v = std::max(max_v, std::abs(d));
  if (max_v > static_cast<int>(num_vars_)) grow_vars(static_cast<uint32_t>(max_v));
  // PR clauses are redundant for the formula they were derived from, not for an extension of it.
  if (counting_added_) throw std::logic_error("adding a clause after counting certificates is not supported (use --no-counting)");
  clause_buf_.clear();
  for (int d : adding_) {
    const Lit l = from_dimacs(d);
    clause_buf_.push_back(make_lit(internal_var(var_of(l)), is_negative(l)));  // (renumbered input)
  }
  if (inactive_) {  // (no variable is eliminated before the first elimination or substitution)
    for (const Lit l : clause_buf_) {
      if (eliminated_[var_of(l)]) {
        throw std::logic_error("adding a clause on an eliminated variable is not supported yet (use --no-eliminate)");
      }
    }
  }
  if (clause_buf_.size() <= 16) {
    small_sort(clause_buf_.data(), static_cast<uint32_t>(clause_buf_.size()));
  } else {
    std::sort(clause_buf_.begin(), clause_buf_.end());
  }
  const size_t before = clause_buf_.size();
  clause_buf_.erase(std::unique(clause_buf_.begin(), clause_buf_.end()), clause_buf_.end());
  bool changed = clause_buf_.size() != before;
  if (changed) input_irregular_ = true;  // duplicate literals
  // Sorted: a literal and its negation are adjacent.
  for (size_t i = 1; i < clause_buf_.size(); ++i) {
    if (clause_buf_[i] == negate(clause_buf_[i - 1])) {  // tautology
      input_irregular_ = true;
      return;
    }
  }
  if (!trail_.empty()) {  // (else every literal is unassigned)
    size_t j = 0;
    for (size_t i = 0; i < clause_buf_.size(); ++i) {
      const int8_t v = value(clause_buf_[i]);
      if (v > 0) return;  // satisfied by a root-level unit
      if (v < 0) {
        changed = true;
        input_shortened_ = true;
        continue;
      }
      clause_buf_[j++] = clause_buf_[i];
    }
    clause_buf_.resize(j);
  }
  if (changed && proof_ && !clause_buf_.empty()) proof_->add(clause_buf_.data(), clause_buf_.size());
  if (clause_buf_.empty()) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return;
  }
  if (clause_buf_.size() == 1) {
    assign_unit_in_proof(clause_buf_[0]);  // an input clause, or its shortened copy written above
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
  arena_.resize_uninitialized(ref + kHeaderWords + size);  // (every word is written below)
  Clause& c = clause(static_cast<uint32_t>(ref));
  std::memset(&c, 0, sizeof(Clause));
  c.size = size;
  c.glue = std::min<uint32_t>(glue, (1u << 20) - 1);
  c.used = redundant ? (glue <= tier2_ ? 2 : 1) : 0;
  c.keep = redundant && glue <= tier1_ && (!opts_.tier1keepglue || glue <= static_cast<uint32_t>(opts_.tier1keepglue));
  if (redundant && glue <= tier1_) ++stats_.tier1_other;
  c.reason = 0;
  c.garbage = 0;
  c.redundant = redundant;
  c.vivified = 0;
  c.age = 0;
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
  const Var iv = internal_var(static_cast<Var>(v - 1));
  const int8_t x = model_valid_ ? model_[iv] : vals_[2 * size_t{iv}];
  const bool truth = (x > 0) == (lit > 0);
  return truth ? lit : -lit;
}

int Solver::solve() {
  unknown_reason_ = "";
  stop_reason_ = nullptr;
  if (!adding_.empty()) throw std::logic_error("solve() called with an unterminated clause");
  if (inconsistent_) return kUnsat;
  if (opts_.renumber && !renumber_tried_) renumber();  // (before the watches are connected)
  connect_pending();
  // --queueorder=1: before the first search, the decision queue takes the variables lowest index
  // first (by default the queue picks the most recently enqueued, so the highest index first).
  // Circuit encodings number the inputs first and the gate outputs after them: deciding inputs
  // first propagates through the circuit (asconhash: 26k propagations and 1.0 decision per
  // conflict focused-only, refuted in 74k conflicts; highest first, 250 and 10.7, 6.6M conflicts).
  // The other values decide where it applies (order.cpp).
  if (opts_.queueorder && !queue_ordered_ && stats_.decisions == 0) initial_queue_order();
  if (memory_limit_ && memory_exceeded(true)) {  // before preprocessing (the periodic check comes later)
    unknown_reason_ = "memory limit";
    return kUnknown;
  }
  if (opts_.xorsub && !xorsub_tried_ && level() == 0) {
    // Before everything else: lucky phases, counting and Gauss-Jordan see the reduced formula.
    xorsub_tried_ = true;
    xor_unsubstitute();
    if (inconsistent_) {
      if (proof_) proof_->flush();
      return kUnsat;
    }
  }
  if (opts_.cardinality && !card_runs_) detect_cardinality("original");
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
  // Counting certificates before search (and before the first elimination round, whose BVA and
  // BVE would re-encode the at-most-one cliques).
  if (opts_.reportmem) report_memory("start");
  if (opts_.counting && !counting_tried_) {
    counting();
    if (opts_.reportmem) report_memory("counting");
    if (inconsistent_) {
      if (proof_) proof_->flush();
      return kUnsat;
    }
  }
  // Linear equations mod p on one-hot domains (--linmod, off): a model from Gaussian elimination
  // over GF(p), before the XOR pass.
  if (opts_.linmod && !linmod_tried_ && level() == 0) {
    linmod_tried_ = true;
    const bool linmod_model = linmod();
    if (linmod_model || inconsistent_) {  // (inconsistent_: a conflict at the root)
      if (proof_) proof_->flush();
      return linmod_model ? kSat : kUnsat;
    }
  }
  if (opts_.gauss && !gauss_tried_ && level() == 0) {
    gauss_tried_ = true;
    const bool gauss_model = gauss_start();
    if (opts_.reportmem) report_memory("gauss");
    if (gauss_model) {
      if (proof_) proof_->flush();
      return kSat;
    }
    if (inconsistent_) {  // refuted (the empty clause is in the proof)
      if (proof_) proof_->flush();
      return kUnsat;
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
      if (opts_.reportmem) report_memory("eliminate");
      if (inconsistent_) return kUnsat;
      if (propagate()) debug_check("eliminate");
    } else if (opts_.sweep && !sweep_initial_done_ && level() == 0) {
      // One sweep before the first decision (after the first elimination round), as Kissat's
      // preprocessing does: miters give up many equivalences early.
      sweep_initial_done_ = true;
      sweep(1'000'000 + arena_.size() / 2);
      if (opts_.reportmem) report_memory("sweep");
      if (inconsistent_) return kUnsat;
    } else if (vivifying()) {
      vivify();
      if (inconsistent_) return kUnsat;
      debug_check("vivify");
    } else if (level() == 0 && fixed_ > last_simplify_fixed_ &&
               stats_.ticks >= simplify_ticks_limit_) {
      simplify_root();
    } else if (gauss_due()) {
      if (gauss_round()) return kSat;  // a model from the detached Gauss-Jordan solver
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
        for (uint32_t m = 0; m < c.size; ++m) std::fprintf(stderr, " %d%s", to_dimacs(external_lit(l[m])), eliminated_[var_of(l[m])] ? "*" : "");
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
  if (stop_reason_ == kStopFault) stop_reason_ = nullptr;  // (--stopfault: the search goes on)
  if (!stop_reason_ && terminate_ && terminate_->load(std::memory_order_relaxed)) stop_reason_ = "interrupted";
  if (stop_reason_) {  // (also noticed by a pass, see stop_requested())
    unknown_reason_ = stop_reason_;
    return true;
  }
  if (conflict_limit_ >= 0 && stats_.conflicts >= static_cast<uint64_t>(conflict_limit_)) {
    unknown_reason_ = "conflict limit";
    return true;
  }
  // (the detached Gauss-Jordan solver's rounds: checked every time, so that short rounds stay short)
  if (ticks_limit_ && stats_.ticks >= ticks_limit_) {
    unknown_reason_ = "ticks limit";
    return true;
  }
  const bool periodic = (++limit_check_ & 1023) == 0;
  // The time limit: the clock is read every kClockTicks search ticks (about 0.3-2 ms of search;
  // a conflict can take more than a millisecond on large formulas) and every 1024 calls (at most
  // a few milliseconds of decisions that propagate little).
  constexpr uint64_t kClockTicks = uint64_t{1} << 16;
  if (time_limit_ > 0 && (periodic || stats_.ticks >= clock_ticks_)) {
    clock_ticks_ = stats_.ticks + kClockTicks;
    const double now = seconds();
    if (now >= time_limit_) {
      stop_reason_ = unknown_reason_ = "time limit";
      if (opts_.verbose) std::printf("c [%.2f s] the search noticed the time limit %.3f s late\n", now, now - time_limit_);
      return true;
    }
  }
  if (!periodic) return false;
  if (opts_.reportmem) {
    const double now = seconds();
    if (now >= report_next_) report_memory("search");
    // (on its own clock: the reports after elimination rounds move report_next_)
    if (now >= progress_next_) {
      progress_next_ = now + opts_.reportmem;
      report_progress();
    }
  }
  if (memory_limit_ && memory_exceeded((limit_check_ & 65535) == 0)) {
    unknown_reason_ = "memory limit";
    return true;
  }
  return false;
}

bool Solver::stop_check() {
  if (opts_.stopfault) {
    stop_countdown_ = static_cast<uint32_t>(opts_.stopfault);
    ++stats_.stop_faults;
    stop_reason_ = kStopFault;
    return true;
  }
  if (time_limit_ <= 0) {  // (set_time_limit() comes before solve(), whose passes reset the countdown)
    stop_countdown_ = UINT32_MAX;
    return false;
  }
  const double now = seconds();
  if (now >= time_limit_) {
    stop_reason_ = "time limit";
    return true;
  }
  constexpr uint32_t kMaxPeriod = 4096;
  const double since = now - stop_last_;
  stop_last_ = now;
  if (since < 1e-4) {
    if (stop_period_ < kMaxPeriod) stop_period_ *= 2;
  } else if (since > 1e-3) {
    stop_period_ = std::max<uint32_t>(stop_period_ / 4, 1);
  }
  stop_countdown_ = stop_period_;
  return false;
}

// The --mem-limit check (every 1024 limit checks; also before preprocessing
// and during elimination rounds, which add clauses). The internal accounting (memory_bytes(): the
// main structures) misses the input copy kept for the model check, the inprocessing buffers and
// the allocator's overhead (on ncc it read 815 MB at a peak resident size of 2594 MB), so the
// peak resident set size of the process counts too (getrusage, cheap; the accounting walks every
// watch list and is only added when 'accounting' is set). The limit is 7/8 of --mem-limit:
// memory grows between two checks (the end of an inprocessing round, the model extension), and a
// watchdog enforcing --mem-limit must not kill the process first.
bool Solver::memory_exceeded(bool accounting) const {
  const double soft = static_cast<double>(memory_limit_ - memory_limit_ / 8);
  if (peak_rss_mb() * (1 << 20) > soft) return true;
  return accounting && static_cast<double>(memory_bytes()) > soft;
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

double Solver::current_rss_mb() {
#if defined(__APPLE__) && defined(__clang__)
  mach_task_basic_info_data_t info{};
  mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;
  if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, reinterpret_cast<task_info_t>(&info), &count) != KERN_SUCCESS) {
    return 0;
  }
  return static_cast<double>(info.resident_size) / (1 << 20);
#elif defined(__APPLE__)
  return peak_rss_mb();  // (no current size without the mach headers: the peak instead)
#else
  std::ifstream statm("/proc/self/statm");
  unsigned long long pages = 0, resident = 0;
  if (!(statm >> pages >> resident)) return 0;
  return static_cast<double>(resident) * static_cast<double>(sysconf(_SC_PAGESIZE)) / (1 << 20);
#endif
}

double Solver::heap_in_use_mb() {
#if defined(__APPLE__) && defined(__clang__)
  malloc_statistics_t st{};
  malloc_zone_statistics(nullptr, &st);
  return static_cast<double>(st.size_in_use) / (1 << 20);
#elif defined(PSAT_MALLINFO2)
  const struct mallinfo2 mi = mallinfo2();
  return static_cast<double>(mi.uordblks + mi.hblkhd) / (1 << 20);
#else
  return -1;
#endif
}

// One line per report: where, resident size now and at its peak, then the parts in MB. Arena:
// capacity, and the live words of irredundant and learned clauses (the rest is garbage not yet
// collected); watches: list headers, binary entries and long-clause entries; per variable: the
// arrays indexed by variable or literal.
void Solver::report_memory(const char* where) {
  report_next_ = seconds() + opts_.reportmem;
  auto mb = [](double b) { return b / (1 << 20); };
  size_t irr_words = 0, red_words = 0, red_clauses = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    if (c.redundant) {
      red_words += kHeaderWords + c.size;
      ++red_clauses;
    } else {
      irr_words += kHeaderWords + c.size;
    }
  }
  // Watches: list heads; binary and long entries; unused capacity inside the lists and garbage
  // slices of the pool (until compaction); the pool's unused tail.
  size_t watch_headers = watches_.head_bytes(), watch_entries = 0;
  size_t bin_entries = 0, nonempty = 0;
  for (size_t l = 0; l < watches_.size(); ++l) {
    const ConstWatchList ws = std::as_const(watches_)[l];
    watch_entries += ws.size() * sizeof(Watch);
    nonempty += ws.capacity() != 0;
    for (const Watch& w : ws) bin_entries += w.binary();
  }
  const size_t watch_slack = watches_.pool_bytes() - watch_entries;
  const size_t per_var = vals_.capacity() + vdata_.capacity() * sizeof(VarData) + 3 * saved_.capacity() +
                         trail_.capacity() * 4 + flags_.capacity() + links_.capacity() * sizeof(Link) +
                         bumped_.capacity() * 8 + score_.capacity() * 8 + num_vars_ * 4 +
                         levels_.capacity() * sizeof(LevelInfo) + level_stamp_.capacity() * 8 + model_.capacity() +
                         eliminated_.capacity() + touched_.capacity() + marks_.capacity();
  size_t gauss = gauss_reasons_.capacity() * 4;
  for (const GaussMatrix& m : gauss_mats_) gauss += m.bits.capacity() * 8 + m.ncols * 40 + m.nrows * 16;
  const size_t gauss_copy = gauss_sub_ ? gauss_sub_->memory_bytes() : 0;
  // Other persistent arrays and the scratch buffers kept between calls (not in 'accounted'):
  // per-variable arrays of sweeping, elimination and BVA, the sweep stamps (per long clause),
  // vivification counters, elimination and definition scratch, pending binaries, the root trail.
  auto cap = [](const auto& v) { return v.capacity() * sizeof(*v.data()); };
  const size_t other = cap(sweep_local_) + cap(sweep_merged_) + cap(sweep_dirty_) + cap(sweep_queued_) +
                       cap(bva_added_) + cap(elim_failed_bound_) + cap(elim_size_failed_) + cap(sweep_stamp_) +
                       cap(sweep_env_) + cap(sweep_added_) + cap(sweep_depth_) + cap(sweep_follow_) +
                       cap(sweep_emitted_) + cap(sweep_emitted_lits_) + cap(viv_count_) + cap(viv_cands_) +
                       cap(viv_marked_) + cap(recent_learned_) + cap(elim_side_[0]) + cap(elim_side_[1]) +
                       cap(elim_refs_) + cap(elim_gate_[0]) + cap(elim_gate_[1]) + cap(elim_res_) + cap(elim_noccs_) +
                       cap(elim_nlits_) + cap(elim_changed_) + cap(elim_changed_mark_) + cap(def_lits_) +
                       cap(def_core_) + cap(pending_binaries_) + cap(control_) + cap(analyzed_) + cap(minimized_) +
                       cap(shrunk_) + cap(learned_) + cap(touched_levels_) + cap(unhide_target_) + cap(adding_) +
                       cap(clause_buf_) + cap(gauss_queue_) + cap(gauss_closed_) + cap(gauss_conflict_) +
                       cap(gauss_free_);
  std::printf("c [%.2f s] memory %s: rss %.0f MB (peak %.0f, heap in use %.0f)  arena %.0f (irredundant %.0f, learned %.0f in %zu clauses, "
              "garbage %.0f)  clause refs %.0f  watches %.0f (headers %.0f, binary %zu entries %.0f, long %.0f, "
              "slack %.0f, %zu lists)  per-variable %.0f (%u vars)  extension %.0f  occs %.0f  kitten %.0f  gauss %.0f  "
              "gauss copy %.0f  accounted %.0f  other %.0f  model-check copy %.0f\n",
              seconds(), where, current_rss_mb(), peak_rss_mb(), heap_in_use_mb(), mb(static_cast<double>(arena_.capacity()) * 4),
              mb(static_cast<double>(irr_words) * 4), mb(static_cast<double>(red_words) * 4), red_clauses,
              mb(static_cast<double>(garbage_words_) * 4), mb(static_cast<double>(clauses_.capacity()) * 4),
              mb(static_cast<double>(watch_headers + watch_entries + watch_slack)), mb(static_cast<double>(watch_headers)),
              bin_entries, mb(static_cast<double>(bin_entries * sizeof(Watch))),
              mb(static_cast<double>(watch_entries - bin_entries * sizeof(Watch))), mb(static_cast<double>(watch_slack)),
              nonempty, mb(static_cast<double>(per_var)), num_vars_, mb(static_cast<double>(extension_.capacity()) * 4),
              mb(static_cast<double>(occs_.bytes())), mb(static_cast<double>(kitten_.bytes())),
              mb(static_cast<double>(gauss)), mb(static_cast<double>(gauss_copy)),
              mb(static_cast<double>(memory_bytes())), mb(static_cast<double>(other)),
              mb(static_cast<double>(input_copy_bytes_)));
  std::fflush(stdout);
}

namespace {
const char* const kPassNames[kPassCount] = {"eliminate", "substitute", "congruence", "subsume", "bva",
                                            "vivify",    "probe",      "sweep",      "walk",    "reduce",
                                            "lucky",     "unhide",     "simulate",   "counting", "gauss",
                                            "binreduce"};
}  // namespace

// --reportmem (periodic, in the search): one line of cumulative counters for time series over long
// runs. Learned clauses by tier (tier1: glue <= tier1 or kept; tier2: glue <= tier2; tier3: the
// rest) with their arena words; the mode and the ticks left in it; the next rephase and reduce
// limits (conflicts); pass seconds in kPassNames order. Reads only.
void Solver::report_progress() {
  uint64_t t[3] = {}, tw[3] = {}, tu[3] = {};
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || !c.redundant) continue;
    const int k = c.keep || c.glue <= tier1_ ? 0 : c.glue <= tier2_ ? 1 : 2;
    ++t[k];
    tw[k] += kHeaderWords + c.size;
    tu[k] += c.used != 0;
  }
  auto ull = [](uint64_t x) { return static_cast<unsigned long long>(x); };
  auto mb = [](double words) { return words * 4 / (1 << 20); };
  std::string passes;
  char buf[64];
  for (int k = 0; k < kPassCount; ++k) {
    std::snprintf(buf, sizeof buf, "%s%.2f", k ? "," : "", pass_seconds_[k]);
    passes += buf;
  }
  const uint64_t mode_left = mode_limit_ticks_ > stats_.ticks ? mode_limit_ticks_ - stats_.ticks : 0;
  std::printf("c [%.2f s] progress conflicts=%llu decisions=%llu propagations=%llu ticks=%llu stable_conflicts=%llu "
              "restarts=%llu reused=%llu switched=%llu rephased=%llu reductions=%llu reduced=%llu collections=%llu "
              "full=%llu collected=%.1f learned=%llu learned_lits=%llu learned_glue=%llu units=%llu "
              "mode=%c mode_len=%llu mode_left=%llu rephase_limit=%llu reduce_limit=%llu "
              "t1=%llu t2=%llu t3=%llu t1used=%llu t2used=%llu t3used=%llu t1mb=%.1f t2mb=%.1f t3mb=%.1f t1aged=%llu redbin=%llu irr=%llu irrbin=%llu "
              "fixed=%llu inactive=%u vars=%u arena=%.1f arenacap=%.1f garbage=%.1f "
              "elim_rounds=%llu viv_rounds=%llu walks=%llu walk_ticks=%llu sweeps=%llu sweep_ticks=%llu "
              "vivify_ticks=%llu bva_vars=%llu bva_search_vars=%llu gauss_rounds=%llu gauss_share=%llu "
              "ema_fast=%.2f ema_slow=%.2f proof=%.1f passes=%s\n",
              seconds(), ull(stats_.conflicts), ull(stats_.decisions), ull(stats_.propagations), ull(stats_.ticks),
              ull(stats_.stable_conflicts), ull(stats_.restarts), ull(stats_.reused_levels), ull(stats_.switched),
              ull(stats_.rephased), ull(stats_.reductions), ull(stats_.reduced_clauses), ull(stats_.collections),
              ull(stats_.collections_full), mb(static_cast<double>(stats_.collected_words)), ull(stats_.learned),
              ull(stats_.learned_literals), ull(stats_.learned_glue), ull(stats_.learned_units), stable_ ? 'S' : 'F',
              ull(mode_limit_ticks_ - mode_start_ticks_), ull(mode_left), ull(rephase_limit_), ull(reduce_limit_),
              ull(t[0]), ull(t[1]), ull(t[2]), ull(tu[0]), ull(tu[1]), ull(tu[2]), mb(static_cast<double>(tw[0])),
              mb(static_cast<double>(tw[1])), mb(static_cast<double>(tw[2])), ull(stats_.reduced_tier1), ull(binaries_redundant_), ull(irredundant_), ull(binaries_irredundant_),
              ull(fixed_), inactive_, num_vars_, mb(static_cast<double>(arena_.size())),
              mb(static_cast<double>(arena_.capacity())), mb(static_cast<double>(garbage_words_)),
              ull(eliminate_rounds_), ull(vivify_rounds_), ull(stats_.walks), ull(stats_.walk_ticks), ull(stats_.sweeps),
              ull(stats_.sweep_ticks), ull(stats_.vivify_ticks), ull(stats_.bva_vars), ull(stats_.bva_search_vars),
              ull(gauss_stats_.rounds), ull(gauss_sub_ ? gauss_share_ : 0), ema_fast_.value, ema_slow_.value,
              proof_ ? static_cast<double>(proof_->bytes()) / 1e6 : 0.0, passes.c_str());
  std::fflush(stdout);
  if (opts_.binstats) binary_census();
  if (opts_.tierstats) report_tiers();
  if (opts_.propstats) report_propstats();
}

// --tierstats (with --reportmem, at every progress line; reads only): tier1 learned clauses by glue
// (1, 2, kept above the limit), size and age bucket (age = reductions in a row unused; "used" =
// used in the last two reduce intervals), the cumulative tier inflow, and per age bucket the
// revivals / exposure since the last line (the chance per reduce interval that an aged tier1
// clause is used again).
void Solver::report_tiers() {
  uint64_t g[3] = {}, sz[4] = {}, age[kAgeBuckets] = {}, used = 0, lits = 0, n = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || !c.redundant || !(c.keep || c.glue <= tier1_)) continue;
    ++n;
    lits += c.size;
    ++g[c.glue <= 1 ? 0 : c.glue <= tier1_ ? 1 : 2];
    ++sz[c.size <= 3 ? 0 : c.size <= 7 ? 1 : c.size <= 15 ? 2 : 3];
    ++age[age_bucket(c.age)];
    used += c.used != 0;
  }
  auto ull = [](uint64_t x) { return static_cast<unsigned long long>(x); };
  std::string ages, rates;
  char buf[96];
  TierStats& t = tier_stats_;
  for (int b = 0; b < kAgeBuckets; ++b) {
    std::snprintf(buf, sizeof buf, "%s%llu", b ? "/" : "", ull(age[b]));
    ages += buf;
    const uint64_t e = t.exposure[b] - t.last_exposure[b], r = t.revived[b] - t.last_revived[b];
    std::snprintf(buf, sizeof buf, "%s%.4f(%llu)", b ? "/" : "", e ? static_cast<double>(r) / static_cast<double>(e) : 0.0,
                  ull(r));
    rates += buf;
    t.last_exposure[b] = t.exposure[b];
    t.last_revived[b] = t.revived[b];
  }
  const double interval = static_cast<double>(opts_.reduceint) * std::sqrt(static_cast<double>(stats_.reductions + 1));
  std::printf("c [%.2f s] tiers t1=%llu t1used=%llu t1glue=%llu/%llu/%llu t1size=%llu/%llu/%llu/%llu t1avg=%.1f "
              "t1age=%s t1revive=%s in_learned=%llu in_other=%llu in_promoted=%llu t2promoted=%llu aged=%llu "
              "interval=%.0f limits=%u/%u agelimit=%u\n",
              seconds(), ull(n), ull(used), ull(g[0]), ull(g[1]), ull(g[2]), ull(sz[0]), ull(sz[1]), ull(sz[2]), ull(sz[3]),
              n ? static_cast<double>(lits) / static_cast<double>(n) : 0.0, ages.c_str(), rates.c_str(),
              ull(stats_.tier1_learned), ull(stats_.tier1_other), ull(stats_.tier1_promoted), ull(stats_.tier2_promoted),
              ull(stats_.reduced_tier1), interval, tier1_, tier2_, revive_limit_);
  // All learned (long) clauses by glue 1-7 and 8+, with how many are used now, and the cumulative
  // uses in conflict analysis by glue in focused (F) and stable (S) mode (per cent).
  uint64_t dg[9] = {}, du[9] = {};
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || !c.redundant) continue;
    const uint32_t k = std::min<uint32_t>(c.glue, 8);
    ++dg[k];
    du[k] += c.used != 0;
  }
  std::string db, ug[2];
  for (uint32_t k = 1; k <= 8; ++k) {
    std::snprintf(buf, sizeof buf, "%s%llu(%llu)", k > 1 ? "/" : "", ull(dg[k]), ull(du[k]));
    db += buf;
  }
  for (int m = 0; m < 2; ++m) {
    uint64_t total = 0;
    for (uint32_t k = 1; k <= 8; ++k) total += t.used_glue[m][k];
    for (uint32_t k = 1; k <= 8; ++k) {
      std::snprintf(buf, sizeof buf, "%s%.1f", k > 1 ? "/" : "",
                    total ? 100.0 * static_cast<double>(t.used_glue[m][k]) / static_cast<double>(total) : 0.0);
      ug[m] += buf;
    }
  }
  std::string viv;
  for (int k = 0; k < 4; ++k) {
    std::snprintf(buf, sizeof buf, "%s%llu/%llu/%llu/%llu", k ? "," : "", ull(t.viv_checked[k]), ull(t.viv_shortened[k]),
                  ull(t.viv_deleted[k]), ull(t.viv_literals[k]));
    viv += buf;
  }
  std::printf("c [%.2f s] glues db=%s usedF=%s usedS=%s viv=%s\n", seconds(), db.c_str(), ug[0].c_str(), ug[1].c_str(),
              viv.c_str());
  std::fflush(stdout);
}

// --reportmem: a pass after which the resident size grew by 32 MB or more (with its time).
void Solver::report_pass_rss(Pass p, double rss0, double secs) {
  const double rss1 = current_rss_mb();
  if (rss1 - rss0 < 32) return;
  std::printf("c [%.2f s] rss +%.0f MB in %s (%.2f s): %.0f MB (peak %.0f)\n", seconds(), rss1 - rss0, kPassNames[p], secs,
              rss1, peak_rss_mb());
}

void Solver::report_late_pass(Pass p, std::chrono::steady_clock::time_point t0,
                              std::chrono::steady_clock::time_point t1) const {
  const double a = std::chrono::duration<double>(t0 - start_).count();
  const double b = std::chrono::duration<double>(t1 - start_).count();
  if (a >= time_limit_ || b < time_limit_) return;
  std::printf("c [%.2f s] the time limit passed during %s (from %.2f s): %.3f s late\n", b, kPassNames[p], a,
              b - time_limit_);
  std::fflush(stdout);
}

size_t Solver::memory_bytes() const {
  size_t bytes = arena_.capacity() * 4 + clauses_.capacity() * 4;
  bytes += vals_.capacity() + vdata_.capacity() * sizeof(VarData) + 3 * saved_.capacity();
  bytes += trail_.capacity() * 4 + flags_.capacity() + links_.capacity() * sizeof(Link) + bumped_.capacity() * 8;
  bytes += score_.capacity() * 8 + num_vars_ * 4 + levels_.capacity() * sizeof(LevelInfo) + level_stamp_.capacity() * 8;
  bytes += watches_.bytes();
  bytes += extension_.capacity() * 4 + occs_.bytes() + model_.capacity() + eliminated_.capacity();
  bytes += touched_.capacity() + marks_.capacity();
  for (const GaussMatrix& m : gauss_mats_) bytes += m.bits.capacity() * 8 + m.ncols * 40 + m.nrows * 16;
  bytes += gauss_reasons_.capacity() * 4;
  if (gauss_sub_) bytes += gauss_sub_->memory_bytes();
  return bytes;
}

// --- restarts --------------------------------------------------------------------------------

bool Solver::restarting() const {
  if (level() == 0) return false;
  if (randec_left_) return false;  // (a random decision sequence runs without restarts)
  if (randec_due()) return true;
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
  const bool random = randec_due();
  const uint32_t keep = random ? 0 : reuse_trail_level();
  stats_.reused_levels += keep;
  stats_.restart_levels += level();
  backtrack(keep);
  // (no watch list is being iterated here; the search does not depend on where lists are)
  if (watches_.compact_due()) watches_.compact();
  if (random) {
    randec_left_ = static_cast<uint64_t>(opts_.randeclength);
    ++stats_.randec_sequences;
  }
  // --targetrestart: the target phases follow the longest consistent trail since this restart
  // (by default: since the last rephase or mode switch, so one long trail can pin them for a
  // whole rephase interval of the stable phase).
  if (stable_ && opts_.targetrestart) target_assigned_ = 0;
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
  if (randec_left_ && --randec_left_ == 0) end_random_sequence();
}

// --- random decision sequences ---------------------------------------------------------------

// A random decision sequence (--randec) explores a part of the search space the decision
// heuristics would not visit: from the root, decisions pick random variables (with their saved
// or target phases) until --randeclength conflicts have been learned. Sequences are due every
// --randecint conflicts times the square root of their count.
void Solver::end_random_sequence() {
  randec_left_ = 0;
  const double count = static_cast<double>(stats_.randec_sequences + 1);
  randec_limit_ = stats_.conflicts + static_cast<uint64_t>(static_cast<double>(opts_.randecint) * std::sqrt(count));
}

Var Solver::random_decision() {
  auto next = [this]() {
    randec_rng_ ^= randec_rng_ << 13;
    randec_rng_ ^= randec_rng_ >> 7;
    randec_rng_ ^= randec_rng_ << 17;
    return randec_rng_;
  };
  auto free = [this](Var v) { return vals_[make_lit(v, false)] == 0 && !eliminated_[v]; };
  // (random input indices: the same picks after a renumbering)
  Var v = 0;
  for (int i = 0; i < 64; ++i) {
    v = static_cast<Var>(next() % num_vars_);
    if (free(internal_var(v))) return internal_var(v);
  }
  // Mostly assigned: scan from the last probe (decide() runs only with unassigned variables).
  for (uint32_t k = 0; k < num_vars_; ++k) {
    const Var u = internal_var(v + k < num_vars_ ? v + k : v + k - num_vars_);
    if (free(u)) return u;
  }
  return stable_ ? next_stable() : next_focused();
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
  if (randec_left_ && stable_ && !opts_.randecstable) end_random_sequence();
  // Focused and stable phases of a pair get the same ticks; each pair is longer by modegrowth
  // (geometric), or the length is the base times the square of the pair number (quadratic, closer
  // to Kissat: over long runs the modes keep alternating instead of one phase taking most time).
  double length = static_cast<double>(mode_ticks_base_);
  if (opts_.modeschedule == 1) {
    const double pair = static_cast<double>(mode_count_ / 2 + 1);
    length *= pair * pair;
  } else if (opts_.modeschedule == 2) {
    const double pair = static_cast<double>(mode_count_ / 2 + 1);
    length *= std::pow(pair, static_cast<double>(opts_.modepower) / 100.0);
  } else {
    const double growth = static_cast<double>(opts_.modegrowth) / 100.0;
    for (uint64_t pair = mode_count_ / 2; pair > 0; --pair) length *= growth;
  }
  mode_limit_ticks_ = stats_.ticks + static_cast<uint64_t>(std::min(length, 1e18));
  mode_start_ticks_ = stats_.ticks;
  target_assigned_ = 0;
  if (stable_) {
    if (opts_.stablereorder) stable_occurrence_scores();
    rebuild_heap();
    reluctant_.init(static_cast<uint64_t>(opts_.reluctantint), static_cast<uint64_t>(opts_.reluctantlim));
  } else {
    queue_search_ = queue_last_;
    restart_limit_ = stats_.conflicts + focused_restart_interval();
    // --queueorder=3 / 4: the default order from the second focused phase on
    if (order_revert_ && mode_count_ == 2) queue_default_order_unbumped();
    if (opts_.queuescores == 1 || (opts_.queuescores == 2 && mode_count_ == 2)) queue_score_order();
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
  if (opts_.verbose >= 2) {
    std::printf("c [%.2f s] rephase %llu (%c) in %s mode after %llu conflicts (best trail %u)\n", seconds(),
                static_cast<unsigned long long>(rephase_count_), kind, stable_ ? "stable" : "focused",
                static_cast<unsigned long long>(stats_.conflicts), best_assigned_);
  }
  std::copy(saved_.begin(), saved_.end(), target_.begin());
  target_assigned_ = 0;
  best_assigned_ = 0;
  const bool by_stable = opts_.rephasestable == 2 && opts_.stable != 0;
  rephase_limit_ = (by_stable ? stats_.stable_conflicts : stats_.conflicts) +
                   static_cast<uint64_t>(opts_.rephaseint) * rephase_count_;
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

static_assert(kProofSources <= ProofWriter::kSources, "proof sources");

int Solver::proof_enter(int source) {
  if (!proof_) return 0;
  const int saved = proof_->source();
  proof_->set_source(source);
  return saved;
}

void Solver::proof_leave(int saved) {
  if (proof_) proof_->set_source(saved);
}

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
  std::fprintf(out, "c restarts       %14llu  reused levels %llu of %llu  rephased %llu  mode switches %llu\n",
               ull(stats_.restarts), ull(stats_.reused_levels), ull(stats_.restart_levels), ull(stats_.rephased),
               ull(stats_.switched));
  std::fprintf(out, "c random         %14llu  sequences, %llu decisions\n", ull(stats_.randec_sequences),
               ull(stats_.random_decisions));
  std::fprintf(out, "c levels         %14.1f  per conflict, %.1f backtracked per learned clause\n",
               stats_.learned ? static_cast<double>(stats_.conflict_levels) / static_cast<double>(stats_.learned) : 0.0,
               stats_.learned ? static_cast<double>(stats_.backjump_levels) / static_cast<double>(stats_.learned) : 0.0);
  std::fprintf(out, "c chronological  %14llu  backtracks to the conflict level %llu  missed implications %llu  fallbacks %llu\n",
               ull(stats_.chrono_backtracks), ull(stats_.chrono_conflict_backtracks), ull(stats_.chrono_missed),
               ull(stats_.chrono_fallbacks));
  std::fprintf(out, "c reductions     %14llu  reduced %llu  root simplifications %llu  tier1 aged out %llu\n",
               ull(stats_.reductions), ull(stats_.reduced_clauses), ull(stats_.simplified_root), ull(stats_.reduced_tier1));
  std::fprintf(out, "c collections    %14llu  full %llu  arena %.1f MB, collected %.1f MB\n", ull(stats_.collections),
               ull(stats_.collections_full), static_cast<double>(arena_.size()) * 4 / 1e6,
               static_cast<double>(stats_.collected_words) * 4 / 1e6);
  std::fprintf(out, "c watch pool     %14llu  list moves, %llu compactions, %.1f MB\n", ull(watches_.relocations()),
               ull(watches_.compactions()), static_cast<double>(watches_.pool_bytes()) / 1e6);
  std::fprintf(out, "c learned        %14llu  units %llu  binary %llu  avg size %.1f  glue %.1f  minimized %.1f%%  eager subsumed %llu\n",
               ull(stats_.learned), ull(stats_.learned_units), ull(stats_.learned_binary),
               stats_.learned ? static_cast<double>(stats_.learned_literals) / static_cast<double>(stats_.learned) : 0.0,
               stats_.learned ? static_cast<double>(stats_.learned_glue) / static_cast<double>(stats_.learned) : 0.0,
               pct(stats_.minimized_literals, stats_.learned_literals + stats_.minimized_literals),
               ull(stats_.eager_subsumed));
  std::fprintf(out,
               "c eliminations   %14llu  eliminated %llu  substituted %llu  resolvents %llu  subsumed %llu  "
               "strengthened %llu  merged pairs %llu\n",
               ull(stats_.eliminations), ull(stats_.eliminated), ull(stats_.substituted), ull(stats_.resolvents),
               ull(stats_.subsumed), ull(stats_.strengthened), ull(stats_.merged));
  std::fprintf(out,
               "c elim tries     %14llu  resolutions %llu  retried unchanged %llu (same bound) %llu (raised)  failed: "
               "occurrences %llu  size %llu (skipped %llu)  bound %llu  literals %llu  xor %llu\n",
               ull(stats_.elim_tried), ull(stats_.elim_resolutions), ull(stats_.elim_retried_same), ull(stats_.elim_retried_raised),
               ull(stats_.elim_fail_occ), ull(stats_.elim_fail_size), ull(stats_.elim_long_skipped),
               ull(stats_.elim_fail_bound),
               ull(stats_.elim_fail_lits), ull(stats_.elim_fail_xor));
  std::fprintf(out,
               "c elim work      %14llu  occs %llu  subsume %llu  congruence %llu  gather %llu  gates %llu  "
               "definitions %llu  count %llu  add %llu  (failed tries %llu)\n",
               ull(stats_.elim_w_occs + stats_.elim_w_subsume + stats_.elim_w_congruence + stats_.elim_w_gather +
                   stats_.elim_w_gates + stats_.elim_w_defs + stats_.elim_w_count + stats_.elim_w_add),
               ull(stats_.elim_w_occs), ull(stats_.elim_w_subsume), ull(stats_.elim_w_congruence),
               ull(stats_.elim_w_gather), ull(stats_.elim_w_gates), ull(stats_.elim_w_defs), ull(stats_.elim_w_count),
               ull(stats_.elim_w_add), ull(stats_.elim_w_failed));
  std::fprintf(out, "c vivifications  %14llu  checked %llu  vivified %llu (learned %llu of %llu)  removed literals %llu  instantiated %llu  "
                    "implied deleted %llu  asym deleted %llu  subsumed %llu  ticks %llu\n",
               ull(stats_.vivifications), ull(stats_.vivify_checked), ull(stats_.vivified), ull(stats_.vivified_learned),
               ull(stats_.vivify_checked_learned),
               ull(stats_.vivified_literals), ull(stats_.vivify_instantiated), ull(stats_.vivify_implied_deleted),
               ull(stats_.vivify_asym), ull(stats_.vivify_subsumed), ull(stats_.vivify_ticks));
  {
    const TierStats& ts = tier_stats_;
    std::fprintf(out, "c vivify tiers   checked / shortened / deleted / removed literals:  irredundant %llu/%llu/%llu/%llu  "
                      "tier1 %llu/%llu/%llu/%llu  tier2 %llu/%llu/%llu/%llu  tier3 %llu/%llu/%llu/%llu  tier1 turns %llu  "
                      "pass ticks irredundant %llu learned %llu tier1 %llu tier2 %llu\n",
                 ull(ts.viv_checked[0]), ull(ts.viv_shortened[0]), ull(ts.viv_deleted[0]), ull(ts.viv_literals[0]),
                 ull(ts.viv_checked[1]), ull(ts.viv_shortened[1]), ull(ts.viv_deleted[1]), ull(ts.viv_literals[1]),
                 ull(ts.viv_checked[2]), ull(ts.viv_shortened[2]), ull(ts.viv_deleted[2]), ull(ts.viv_literals[2]),
                 ull(ts.viv_checked[3]), ull(ts.viv_shortened[3]), ull(ts.viv_deleted[3]), ull(ts.viv_literals[3]),
                 ull(stats_.vivify_tier1_turns), ull(ts.viv_ticks[0]), ull(ts.viv_ticks[1]), ull(ts.viv_ticks[2]),
                 ull(ts.viv_ticks[3]));
  }
  std::fprintf(out, "c probing        %14llu  failed literals %llu (below the probe %llu)\n", ull(stats_.probes),
               ull(stats_.failed_literals), ull(stats_.probe_uips));
  std::fprintf(out, "c unhiding       %14llu  units %llu  transitive %llu  hidden tautologies %llu  strengthened %llu  "
                    "removed literals %llu  ticks %llu\n",
               ull(stats_.unhides), ull(stats_.unhide_units), ull(stats_.unhide_transitive), ull(stats_.unhide_tautologies),
               ull(stats_.unhide_strengthened), ull(stats_.unhide_literals), ull(stats_.unhide_ticks));
  if (opts_.binreduce) {
    std::fprintf(out, "c binreduce      %14llu  checked %llu  deleted %llu  undecided %llu  ticks %llu\n",
                 ull(stats_.binreduce_rounds), ull(stats_.binreduce_checked), ull(stats_.binreduce_deleted),
                 ull(stats_.binreduce_cut), ull(stats_.binreduce_ticks));
  }
  std::fprintf(out, "c sweeping       %14llu  variables %llu  units %llu  equivalences %llu  flips %llu  ticks %llu  "
                    "(kitten %llu in %llu solves)  limits %u vars / %u clauses / depth %u (growth %u)\n",
               ull(stats_.sweeps), ull(stats_.swept_vars), ull(stats_.sweep_units), ull(stats_.sweep_equivalences),
               ull(stats_.sweep_flips), ull(stats_.sweep_ticks), ull(stats_.sweep_kitten_ticks), ull(stats_.sweep_solves),
               sweep_lim_vars_, sweep_lim_clauses_, sweep_lim_depth_, sweep_growth_);
  std::fprintf(out, "c sweep calls    %14llu  env %llu  backbone %llu (sat %llu unsat %llu unknown %llu)  "
                    "equivalence %llu (sat %llu unsat %llu unknown %llu)\n",
               ull(stats_.sweep_solves), ull(stats_.sweep_env_solves), ull(stats_.sweep_bb_solves), ull(stats_.sweep_bb_sat),
               ull(stats_.sweep_bb_unsat), ull(stats_.sweep_bb_unknown), ull(stats_.sweep_eq_solves), ull(stats_.sweep_eq_sat),
               ull(stats_.sweep_eq_unsat), ull(stats_.sweep_eq_unknown));
  std::fprintf(out, "c sweep cands    backbone %llu (flips %llu models %llu)  equivalence %llu (flips %llu models %llu)  "
                    "checks %llu (known %llu, outer literals dropped %llu)  ticks limit %llu  followed %llu  clean skipped %llu  "
                    "environments %.1f vars %.1f clauses\n",
               ull(stats_.sweep_bb_cands), ull(stats_.sweep_bb_by_flip), ull(stats_.sweep_bb_by_model),
               ull(stats_.sweep_eq_cands), ull(stats_.sweep_eq_by_flip), ull(stats_.sweep_eq_by_model),
               ull(stats_.sweep_eq_checks), ull(stats_.sweep_eq_known), ull(stats_.sweep_outer_dropped),
               ull(stats_.sweep_var_limit), ull(stats_.sweep_followed), ull(stats_.sweep_clean_skipped),
               stats_.swept_vars ? static_cast<double>(stats_.sweep_env_vars) / static_cast<double>(stats_.swept_vars) : 0.0,
               stats_.swept_vars ? static_cast<double>(stats_.sweep_env_clauses) / static_cast<double>(stats_.swept_vars) : 0.0);
  std::fprintf(out, "c simulation     %14llu  gates %llu (ite %llu)  candidates %llu  checked %llu  equivalences %llu  units %llu  "
                    "failed %llu  ticks %llu\n",
               ull(stats_.simulations), ull(stats_.sim_gates), ull(stats_.sim_ites), ull(stats_.sim_candidates), ull(stats_.sim_checked),
               ull(stats_.sim_equivalences), ull(stats_.sim_units), ull(stats_.sim_failed), ull(stats_.sim_ticks));
  std::fprintf(out, "c gates          %14llu  (definitions in elimination: xor %llu, ite %llu, semantic %llu; xor merges skipped %llu)  congruent outputs %llu (xor %llu, ite %llu)  ternary binaries %llu (subsumed %llu)\n",
               ull(stats_.gates), ull(stats_.xor_gates), ull(stats_.ite_gates), ull(stats_.definitions),
               ull(stats_.xor_merges_skipped), ull(stats_.congruent), ull(stats_.congruent_xors), ull(stats_.congruent_ites),
               ull(stats_.tern_binaries), ull(stats_.tern_subsumed));
  if (xorsub_stats_.runs) {
    const XorSubStats& x = xorsub_stats_;
    std::fprintf(out, "c xorsub         %14llu  tuples (%llu of 3 variables), %llu expanded clauses -> %llu reduced, %llu definition clauses, %.4f s\n",
                 ull(x.tuples), ull(x.triples), ull(x.removed), ull(x.reduced), ull(x.definition_clauses), x.seconds);
  }
  if (linmod_stats_.runs) {
    const LinmodStats& x = linmod_stats_;
    std::fprintf(out, "c linmod         %14llu  domains (3: %llu, 5: %llu, 7: %llu), equations %llu, nonlinear %llu, covering %.1f%% of %llu clauses, "
                      "systems %llu (%llu x %llu, rank %llu, skipped %llu), inconsistent %llu, attempts %llu, models %llu, conflicts %llu, %.4f s\n",
                 ull(x.groups), ull(x.group_sizes[3]), ull(x.group_sizes[5]), ull(x.group_sizes[7]), ull(x.equations),
                 ull(x.nonlinear), pct(x.covered, x.clauses), ull(x.clauses), ull(x.systems), ull(x.rows), ull(x.columns),
                 ull(x.rank), ull(x.skipped), ull(x.inconsistent), ull(x.attempts), ull(x.models), ull(x.conflicts), x.seconds);
  }
  if (opts_.gauss || gauss_on_) {
    const GaussStats& g = gauss_stats_;
    std::fprintf(out, "c gauss          %14llu  xors covering %.1f%% of %llu clauses, %llu components, %llu matrices (%llu x %llu), "
                      "%s, rounds %llu, ticks %llu, conflicts %llu, share %llu (max %llu, grown %llu, shrunk %llu)%s, %s\n",
                 ull(g.xors), pct(g.covered, g.clauses), ull(g.clauses), ull(g.components), ull(g.matrices),
                 ull(g.matrix_rows), ull(g.matrix_cols), g.gated ? "gated in" : "gated out", ull(g.rounds),
                 ull(g.sub_ticks), ull(g.sub_conflicts), ull(g.share), ull(g.max_share), ull(g.grown), ull(g.shrunk),
                 g.stopped ? " stopped" : "",
                 g.model ? "model found" : g.sub_result == kUnsat ? "unsatisfiable (ignored)" : "no model");
    std::fprintf(out, "c gauss-jordan   %14llu  propagations, conflicts %llu, pivots %llu, row checks %llu, reopened %llu, root units %llu\n",
                 ull(g.propagations), ull(g.conflicts), ull(g.pivots), ull(g.row_checks), ull(g.reopened), ull(g.root_units));
  }
  std::fprintf(out, "c lucky          %14llu\n", ull(stats_.lucky));
  std::fprintf(out, "c walks          %14llu  flips %llu  ticks %llu  not adopted %llu  models %llu  weight transfers %llu  model walks %llu (ticks %llu, skipped %llu)\n",
               ull(stats_.walks), ull(stats_.walk_flips), ull(stats_.walk_ticks), ull(stats_.walks_kept),
               ull(stats_.walk_models), ull(stats_.walk_transfers), ull(stats_.model_walks), ull(stats_.model_walk_ticks),
               ull(stats_.model_walks_skipped));
  std::fprintf(out, "c deduplicated   %14llu  binary clauses\n", ull(stats_.deduplicated));
  if (stats_.stop_faults) std::fprintf(out, "c stop faults    %14llu  (--stopfault)\n", ull(stats_.stop_faults));
  std::fprintf(out, "c bva            %14llu  variables, clauses removed %llu added %llu, 3-hop tie-breaks %llu, "
               "trials %llu (rounds made %llu), in search %llu variables in %llu rounds\n",
               ull(stats_.bva_vars), ull(stats_.bva_removed), ull(stats_.bva_added), ull(stats_.bva_hop_ties),
               ull(stats_.bva_trials), ull(stats_.bva_rounds), ull(stats_.bva_search_vars), ull(stats_.bva_search_rounds));
  std::fprintf(out, "c counting       %14llu  structures (%s)  PR clauses %llu  units %llu  lemmas %llu  abandoned %llu  "
                    "skipped %llu  work %llu\n",
               ull(stats_.counting_found), counting_desc_.empty() ? "-" : counting_desc_.c_str(), ull(stats_.counting_pr),
               ull(stats_.counting_units), ull(stats_.counting_lemmas), ull(stats_.counting_failed),
               ull(stats_.counting_skipped), ull(stats_.counting_work));
  std::fprintf(out, "c tiers          %14u  tier2 %u  tier1 in: learned %llu other %llu promoted %llu  tier2 promoted %llu\n",
               tier1_, tier2_, ull(stats_.tier1_learned), ull(stats_.tier1_other), ull(stats_.tier1_promoted),
               ull(stats_.tier2_promoted));
  std::fprintf(out, "c shrunk         %14llu  literals\n", ull(stats_.shrunk_literals));
  std::fprintf(out, "c fixed          %14llu  of %u variables\n", ull(stats_.fixed), num_vars_);
  std::fprintf(out, "c memory         %14.1f MB  (peak resident %.1f MB)\n", static_cast<double>(memory_bytes()) / (1 << 20),
               peak_rss_mb());
  if (proof_) {
    auto mb = [](uint64_t b) { return static_cast<double>(b) / 1e6; };
    std::fprintf(out, "c proof          %14.1f MB  %.1f MB/s  added %llu  deleted %llu (%.1f MB)  PR %llu  shortened %llu  "
                      "forgotten %llu (%llu left)\n",
                 mb(proof_->bytes()), t > 0 ? mb(proof_->bytes()) / t : 0.0, ull(proof_->added()), ull(proof_->deleted()),
                 mb(proof_->deleted_bytes()), ull(proof_->pr()), ull(proof_->shortened()), ull(proof_->forgotten()),
                 ull(proof_->shortened_live()));
    static const char* const kNames[kProofSources] = {
        "search", "eliminate", "substitute", "congruence", "subsume", "bva", "vivify", "probe", "sweep", "walk",
        "reduce", "lucky", "unhide", "simulate", "counting", "gauss", "binreduce", "simplify", "eager"};
    std::string line;
    char buf[160];
    for (int k = 0; k < kProofSources; ++k) {
      const ProofWriter::SourceStats& s = proof_->source_stats(k);
      if (!s.added && !s.deleted) continue;
      std::snprintf(buf, sizeof buf, "  %s %.1f MB (+%llu -%llu, deletions %.1f MB)", kNames[k], mb(s.bytes), ull(s.added),
                    ull(s.deleted), mb(s.deleted_bytes));
      line += buf;
    }
    std::fprintf(out, "c proof sources %s\n", line.c_str());
  }
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
                      "lucky %.2f  unhide %.2f  simulate %.2f  counting %.2f  gauss %.2f  binreduce %.2f s\n",
                 p[kPassProbe], p[kPassSubstitute], p[kPassCongruence], p[kPassSubsume], p[kPassBva], p[kPassReduce],
                 p[kPassLucky], p[kPassUnhide], p[kPassSimulate], p[kPassCounting], p[kPassGauss], p[kPassBinreduce]);
  }
}

}  // namespace psat
