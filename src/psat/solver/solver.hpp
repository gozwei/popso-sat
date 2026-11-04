#pragma once
// The CDCL solver.
//
// Data layout (cache-conscious, Kissat/CaDiCaL style):
// - values: one int8 per literal (1 true, -1 false, 0 unassigned);
// - clauses of size >= 3 live in one arena of 32-bit words: a 3-word header then the literals;
//   a clause is referenced by its word offset;
// - binary clauses exist only in the watch lists (8-byte watches: blocking literal + reference,
//   with a tag bit marking binary watches);
// - a reason is a clause reference, a tagged binary "other literal", or kNoReason (decisions and
//   all root-level assignments).
//
// All scheduling (mode switches) uses "ticks", a deterministic estimate of cache lines touched
// during propagation.

#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <vector>

#include "psat/core/options.hpp"
#include "psat/core/types.hpp"
#include "psat/solver/heap.hpp"

namespace psat {

class ProofWriter;

struct Clause {
  uint32_t size;
  uint32_t glue : 20;
  uint32_t used : 2;
  uint32_t keep : 1;  // tier1: never reduced
  uint32_t reason : 1;
  uint32_t garbage : 1;
  uint32_t redundant : 1;
  uint32_t spare : 6;
  uint32_t pos;  // where the last replacement-watch search ended; GC forwarding address

  Lit* lits() { return reinterpret_cast<Lit*>(this + 1); }
  const Lit* lits() const { return reinterpret_cast<const Lit*>(this + 1); }
};
static_assert(sizeof(Clause) == 12, "clause header must be three words");
constexpr uint32_t kHeaderWords = 3;

constexpr uint32_t kBinaryTag = 0x80000000u;
constexpr uint32_t kNoReason = 0xFFFFFFFFu;
constexpr uint32_t kMaxArenaWords = 0x7FFFFFF0u;

struct Watch {
  Lit blit;      // blocking literal (the other literal for binary clauses)
  uint32_t ref;  // clause reference, or kBinaryTag | redundant-flag for binary clauses

  bool binary() const { return (ref & kBinaryTag) != 0; }
  bool redundant_binary() const { return (ref & 1u) != 0; }
};

struct VarData {
  uint32_t level;
  uint32_t reason;
  uint32_t trail;  // position on the trail
};

// Exponential moving average with bias correction (as in Kissat).
struct Ema {
  double value = 0, biased = 0, alpha = 0, beta = 0, exp = 0;
  void init(double window) {
    alpha = 1.0 / window;
    beta = 1.0 - alpha;
    exp = 1.0;
    value = biased = 0;
  }
  void update(double y) {
    biased += alpha * (y - biased);
    if (exp > 0) {
      exp *= beta;
      value = exp > 1e-12 ? biased / (1.0 - exp) : biased;
      if (exp <= 1e-12) exp = 0;
    } else {
      value = biased;
    }
  }
};

// Knuth's reluctant doubling sequence (Luby restarts): 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...
struct Reluctant {
  uint64_t u = 1, v = 1, period = 0, wait = 0, limit = 0;
  bool trigger = false;
  void init(uint64_t p, uint64_t lim) {
    u = v = 1;
    period = wait = p;
    limit = lim;
    trigger = false;
  }
  void tick() {
    if (!period || trigger) return;
    if (--wait) return;
    if ((u & (~u + 1)) == v) {
      ++u;
      v = 1;
    } else {
      v *= 2;
    }
    if (v * period > limit) u = v = 1;
    wait = v * period;
    trigger = true;
  }
};

struct Stats {
  uint64_t conflicts = 0, decisions = 0, propagations = 0, ticks = 0;
  uint64_t restarts = 0, reductions = 0, rephased = 0, switched = 0, collections = 0;
  uint64_t learned = 0, learned_units = 0, learned_binary = 0, learned_literals = 0, minimized_literals = 0;
  uint64_t reduced_clauses = 0, simplified_root = 0, fixed = 0;
  uint64_t stable_conflicts = 0, focused_conflicts = 0;
  uint64_t original_clauses = 0;
};

class Solver {
 public:
  explicit Solver(const Options& opts = Options());
  ~Solver();
  Solver(const Solver&) = delete;
  Solver& operator=(const Solver&) = delete;

  // Pre-allocates variables 1..max_var.
  void reserve(int max_var);
  // Hint: about this many clauses will be added (reserves address space only).
  void reserve_clauses(int64_t clauses);
  // IPASIR-style clause input: DIMACS literals, 0 ends the clause.
  void add(int lit);
  // Adds a whole clause (DIMACS literals, no terminating 0).
  void add_clause(const int* lits, size_t n);
  // Returns kSat, kUnsat or kUnknown (limit reached or interrupted).
  int solve();
  // After kSat: lit if lit is true in the model, -lit otherwise.
  int val(int lit) const;
  int max_var() const { return static_cast<int>(num_vars_); }

  void set_proof(ProofWriter* proof) { proof_ = proof; }
  void set_terminate(const std::atomic<bool>* flag) { terminate_ = flag; }
  void set_time_limit(double seconds) { time_limit_ = seconds; }
  void set_conflict_limit(int64_t conflicts) { conflict_limit_ = conflicts; }
  void set_memory_limit(uint64_t bytes) { memory_limit_ = bytes; }

  const Stats& stats() const { return stats_; }
  const Options& options() const { return opts_; }
  // Why the last solve() returned kUnknown ("" otherwise).
  const char* unknown_reason() const { return unknown_reason_; }
  size_t memory_bytes() const;
  double seconds() const;
  void print_statistics(std::FILE* out) const;

 private:
  // --- variables and assignment -------------------------------------------------------------
  void grow_vars(uint32_t n);
  uint32_t level() const { return static_cast<uint32_t>(control_.size()); }
  int8_t value(Lit l) const { return vals_[l]; }
  void assign(Lit l, uint32_t reason) {
    const Var v = var_of(l);
    vals_[l] = 1;
    vals_[negate(l)] = -1;
    VarData& d = vdata_[v];
    const uint32_t lvl = level();
    d.level = lvl;
    d.reason = lvl ? reason : kNoReason;
    d.trail = static_cast<uint32_t>(trail_.size());
    saved_[v] = is_negative(l) ? -1 : 1;
    trail_.push_back(l);
    if (!lvl) on_root_fixed(l);
  }
  void on_root_fixed(Lit l);

  // --- clauses --------------------------------------------------------------------------------
  Clause& clause(uint32_t ref) { return *reinterpret_cast<Clause*>(arena_.data() + ref); }
  const Clause& clause(uint32_t ref) const { return *reinterpret_cast<const Clause*>(arena_.data() + ref); }
  uint32_t new_clause(const Lit* lits, uint32_t size, bool redundant, uint32_t glue, bool watch = true);
  void watch_clause(uint32_t ref);
  void add_binary(Lit a, Lit b, bool redundant);
  // Original clauses are watched lazily, all at once at the start of solve(): exact-size watch
  // lists instead of millions of reallocations while parsing large files.
  void connect_pending();
  void add_original_clause();

  // --- search ---------------------------------------------------------------------------------
  int search();
  bool propagate();
  void analyze();
  void minimize_clause();
  bool minimize_literal(Lit lit, uint32_t depth);
  uint32_t recompute_glue(const Clause& c);
  void bump_reason_clause(uint32_t ref);
  void learn_clause(uint32_t jump, uint32_t glue);
  void backtrack(uint32_t new_level);
  void update_target_and_best(uint32_t consistent);
  bool decide();
  Var next_focused();
  Var next_stable();

  // --- heuristics -----------------------------------------------------------------------------
  void bump_variables();
  void bump_reason_literals();
  void queue_init();
  void queue_dequeue(Var v);
  void queue_enqueue_last(Var v);
  void queue_bump(Var v);
  void heap_bump(Var v);
  void rebuild_heap();

  // --- schedules ------------------------------------------------------------------------------
  bool restarting() const;
  void restart();
  bool rephasing() const { return opts_.rephase && stats_.conflicts >= rephase_limit_; }
  void rephase();
  bool reducing() const { return stats_.conflicts >= reduce_limit_; }
  void reduce();
  bool switching() const;
  void switch_mode();
  void update_conflict_statistics(uint32_t glue);
  bool check_limits();

  // --- clause database maintenance ------------------------------------------------------------
  void mark_reasons(bool on);
  void simplify_root();
  void collect_garbage();
  void flush_root_binaries();
  void delete_clause_proof(const Clause& c);

  Options opts_;
  uint32_t num_vars_ = 0;
  bool inconsistent_ = false;

  std::vector<int8_t> vals_;  // per literal
  std::vector<VarData> vdata_;
  std::vector<int8_t> saved_, target_, best_;  // phases per variable (+1 / -1)
  std::vector<Lit> trail_;
  size_t propagated_ = 0;
  std::vector<uint32_t> control_;  // trail size at each decision

  std::vector<uint32_t> arena_;
  std::vector<uint32_t> clauses_;  // live clause references in arena order
  std::vector<std::vector<Watch>> watches_;  // per literal
  uint64_t irredundant_ = 0, redundant_ = 0, binaries_irredundant_ = 0, binaries_redundant_ = 0;
  uint64_t garbage_words_ = 0;
  size_t watched_clauses_ = 0;           // clauses_[0, watched_clauses_) are watched
  std::vector<Lit> pending_binaries_;    // original binary clauses not yet in the watch lists

  // Conflict: a clause reference or a binary clause.
  uint32_t conflict_ref_ = kNoReason;
  Lit conflict_bin_[2] = {kNoLit, kNoLit};
  bool has_conflict_ = false;

  // Analysis scratch.
  std::vector<uint8_t> flags_;  // per variable: kSeen | kPoison | kRemovable
  std::vector<Var> analyzed_;
  std::vector<Var> minimized_;
  std::vector<Lit> learned_;
  struct LevelInfo {
    uint32_t seen = 0;          // learned-clause literals on this level
    uint32_t trail = UINT32_MAX;  // earliest trail position of those literals
  };
  std::vector<LevelInfo> levels_;
  std::vector<uint32_t> touched_levels_;
  std::vector<uint64_t> level_stamp_;  // for glue computation
  uint64_t glue_stamp_ = 0;

  // VMTF queue (focused mode).
  struct Link {
    Var prev = UINT32_MAX, next = UINT32_MAX;
  };
  std::vector<Link> links_;
  std::vector<uint64_t> bumped_;  // enqueue time stamps
  Var queue_first_ = UINT32_MAX, queue_last_ = UINT32_MAX, queue_search_ = UINT32_MAX;
  uint64_t queue_stamp_ = 0;

  // EVSIDS (stable mode).
  std::vector<double> score_;
  ScoreHeap heap_{score_};
  double score_inc_ = 1.0;

  // Modes, restarts, phases.
  bool stable_ = false;
  uint64_t mode_limit_conflicts_ = 0, mode_limit_ticks_ = 0, mode_ticks_base_ = 0, mode_start_ticks_ = 0;
  uint64_t mode_count_ = 0;
  Ema ema_fast_, ema_slow_;
  Reluctant reluctant_;
  uint64_t restart_limit_ = 0;
  uint32_t target_assigned_ = 0, best_assigned_ = 0;
  uint64_t rephase_limit_ = 0, rephase_count_ = 0;
  uint64_t reduce_limit_ = 0;
  uint64_t last_simplify_fixed_ = 0, simplify_ticks_limit_ = 0;
  uint64_t fixed_ = 0;

  // Input.
  std::vector<int> adding_;
  std::vector<Lit> clause_buf_;

  // Limits and output.
  ProofWriter* proof_ = nullptr;
  const std::atomic<bool>* terminate_ = nullptr;
  double time_limit_ = 0;
  int64_t conflict_limit_ = -1;
  uint64_t memory_limit_ = 0;
  uint64_t limit_check_ = 0;
  const char* unknown_reason_ = "";
  std::chrono::steady_clock::time_point start_;
  uint64_t rng_ = 0;
  Stats stats_;
};

}  // namespace psat
