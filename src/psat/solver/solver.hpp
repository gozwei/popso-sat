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
#include "psat/core/word_arena.hpp"
#include "psat/solver/heap.hpp"
#include "psat/solver/kitten.hpp"
#include "psat/solver/occs.hpp"

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
  uint32_t vivified : 1;  // already vivified in the current pass
  uint32_t spare : 5;
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

// Per-variable analysis flags (Solver::flags_).
constexpr uint8_t kSeen = 1, kPoison = 2, kRemovable = 4, kShrinkable = 8;

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

// Wall time per pass (top-level passes, and the sub-passes of elimination and vivification).
enum Pass : uint8_t {
  kPassEliminate, kPassSubstitute, kPassCongruence, kPassSubsume, kPassBva,
  kPassVivify, kPassProbe, kPassSweep, kPassWalk, kPassReduce, kPassLucky, kPassUnhide, kPassSimulate, kPassCount
};

struct Stats {
  uint64_t conflicts = 0, decisions = 0, propagations = 0, ticks = 0;
  uint64_t reused_levels = 0;
  uint64_t restarts = 0, reductions = 0, rephased = 0, switched = 0, collections = 0;
  uint64_t collections_full = 0, collected_words = 0;  // words scanned and moved from the start on
  uint64_t learned = 0, learned_units = 0, learned_binary = 0, learned_literals = 0, minimized_literals = 0;
  uint64_t eager_subsumed = 0;
  uint64_t chrono_backtracks = 0, chrono_conflict_backtracks = 0, chrono_missed = 0;
  uint64_t reduced_clauses = 0, simplified_root = 0, fixed = 0;
  uint64_t eliminations = 0, eliminated = 0, resolvents = 0, subsumed = 0, strengthened = 0, substituted = 0;
  uint64_t vivifications = 0, vivify_ticks = 0, vivify_checked = 0, vivified = 0, vivified_literals = 0, vivify_instantiated = 0, vivify_implied_deleted = 0,
           vivify_asym = 0;
  uint64_t unhides = 0, unhide_units = 0, unhide_transitive = 0, unhide_tautologies = 0, unhide_strengthened = 0,
           unhide_literals = 0, unhide_ticks = 0;
  uint64_t sweeps = 0, swept_vars = 0, sweep_units = 0, sweep_equivalences = 0, sweep_ticks = 0, sweep_flips = 0, sweep_solves = 0, sweep_kitten_ticks = 0;
  uint64_t simulations = 0, sim_gates = 0, sim_candidates = 0, sim_checked = 0, sim_equivalences = 0, sim_units = 0,
           sim_failed = 0, sim_ticks = 0, sim_ites = 0;
  uint64_t probes = 0, failed_literals = 0, gates = 0, xor_gates = 0, xor_merges_skipped = 0, ite_gates = 0, definitions = 0, shrunk_literals = 0;
  uint64_t bva_vars = 0, bva_removed = 0, bva_added = 0, bva_hop_ties = 0, bva_trials = 0, bva_rounds = 0;
  uint64_t walks = 0, walk_flips = 0, walk_ticks = 0, congruent = 0, congruent_xors = 0, congruent_ites = 0, lucky = 0;
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
  static double peak_rss_mb();  // of the process (getrusage), for diagnostics
  void print_statistics(std::FILE* out) const;

 private:
  // --- variables and assignment -------------------------------------------------------------
  void grow_vars(uint32_t n);
  uint32_t level() const { return static_cast<uint32_t>(control_.size()); }
  int8_t value(Lit l) const { return vals_[l]; }
  void assign(Lit l, uint32_t reason) { assign_at(l, reason, level()); }
  // With chronological backtracking an implied literal gets the highest level of its reason's
  // other literals, which can be below the current level ("out of order" on the trail).
  void assign_at(Lit l, uint32_t reason, uint32_t lvl) {
    const Var v = var_of(l);
    vals_[l] = 1;
    vals_[negate(l)] = -1;
    VarData& d = vdata_[v];
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
  bool propagate_vivify(uint32_t ignore);
  template <bool kVivify>
  bool propagate_impl(uint32_t ignore);
  bool analyze();  // false: the conflict is at the root (unsatisfiable)
  uint32_t conflict_level(Lit& forced, uint32_t& count);
  void remove_long_watch(Lit l, uint32_t ref);
  void minimize_clause();
  void shrink_clause();
  bool minimize_literal(Lit lit, uint32_t depth);
  uint32_t recompute_glue(const Clause& c);
  void bump_reason_clause(uint32_t ref);
  void learn_clause(uint32_t jump, uint32_t glue);
  void backtrack(uint32_t new_level);
  // Backtracks to the root and propagates the root literals kept by chronological backtracking
  // (inprocessing expects a fully propagated root). False on a root conflict (inconsistent_).
  bool backtrack_to_root();
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
  void drop_inactive_decisions();

  // --- schedules ------------------------------------------------------------------------------
  bool restarting() const;
  void restart();
  uint64_t focused_restart_interval() const;
  uint32_t reuse_trail_level();
  bool rephasing() const { return opts_.rephase && stats_.conflicts >= rephase_limit_; }
  void rephase();
  bool reducing() const { return stats_.conflicts >= reduce_limit_; }
  void reduce();
  void update_tier_limits();
  bool switching() const;
  void switch_mode();
  void update_conflict_statistics(uint32_t glue);
  bool check_limits();
  void debug_check(const char* where);

  // --- clause database maintenance ------------------------------------------------------------
  void mark_reasons(bool on);
  void simplify_root();
  void collect_garbage();
  void flush_root_binaries();
  void delete_clause_proof(const Clause& c);

  // --- simplification rounds (eliminate.cpp, subsume.cpp) ----------------------------------------
  bool eliminating() const;
  void eliminate();
  void disconnect_long_watches();
  void reconnect_long_watches();
  void subsume_round(uint64_t& budget);
  bool substitute();
  void substitute_now();  // outside elimination rounds, at the root
  uint32_t congruence(uint64_t& budget);
  uint32_t congruent_xors(uint64_t& budget);
  uint32_t congruent_ites(uint64_t& budget);
  void prove_by_cases(std::vector<Lit>& clause, const std::vector<Var>& cases, size_t depth);
  int64_t bva_round(uint64_t& budget, uint64_t limit, bool dry);  // -> clauses removed (estimated if dry)
  void bva_run(uint64_t& budget);  // a trial round first with --bvamin
  size_t bva_count(Lit l, uint64_t& budget);
  bool try_eliminate(Var v, uint32_t bound, uint64_t& budget);
  void gather_occurrences(Lit l, std::vector<uint32_t>& out, uint64_t& budget);
  void delete_irredundant(uint32_t ref);
  void delete_binary(Lit a, Lit b);  // an irredundant binary clause
  void remove_binary_watch(Lit owner, Lit other, bool redundant);
  void touch_clause(const Lit* lits, uint32_t size);
  void push_extension(Lit witness, const Lit* lits, uint32_t size);
  void extend_model();
  void walk();
  bool lucky();
  bool vivifying() const { return opts_.vivify && stats_.conflicts >= vivify_limit_; }
  void vivify();
  void vivify_clauses(bool redundant, uint64_t ticks_limit);
  bool vivify_clause(uint32_t ref, const Lit* lits, uint32_t n);
  void vivify_analyze(Lit implied, bool track_redundant);
  bool irredundant_binary(Lit a, Lit b);
  bool viv_used_redundant_ = false;  // the last vivify_analyze used a learned clause
  void probe_failed_literals(uint64_t ticks_limit);
  void unhide(uint64_t ticks_limit);
  std::vector<uint32_t> unhide_start_, unhide_dsc_, unhide_fin_;
  std::vector<Lit> unhide_target_;
  size_t unhide_next_ = 0;  // long clause to continue with
  void sweep(uint64_t min_budget = 100000);
  bool sweep_initial_done_ = false;
  uint32_t sweep_delay_ = 0, sweep_skip_ = 0;  // back-off after unproductive sweeps
  bool sweep_variable(Var v, const std::vector<uint32_t>& start, const std::vector<uint32_t>& occ, uint64_t& ticks);
  bool sweep_classes(uint32_t n);  // backbone / equivalence candidates as classes (Kissat)
  void sweep_emit_learned();
  bool sweep_add(const Lit* lits, uint32_t size);
  void sweep_retire_learned();
  void simulate_equivalences();
  Kitten kitten_;
  std::vector<uint32_t> sweep_local_;   // per variable: index in the environment or UINT32_MAX
  std::vector<Var> sweep_env_;          // environment variables (local index -> variable)
  std::vector<uint32_t> sweep_stamp_;   // per long clause (CSR index): environment stamp
  uint32_t sweep_stamp_now_ = 0;
  size_t sweep_emitted_ = 0;            // kitten learned clauses already in the proof
  std::vector<Lit> sweep_emitted_lits_; // their literals (flat, size-prefixed) for deletion
  std::vector<uint32_t> sweep_backbone_, sweep_partition_, sweep_next_;  // Kitten literals (sweep_classes)
  std::vector<uint32_t> sweep_merged_;  // per variable: the sweep round that proved it equivalent
  uint32_t sweep_lim_vars_ = 0, sweep_lim_clauses_ = 0, sweep_lim_depth_ = 0;  // this round's environment limits
  std::vector<uint8_t> bva_added_;  // per variable: introduced by BVA
  uint32_t sweep_growth_ = 0;              // growth steps of the limits (--sweepgrow)
  uint64_t sweep_cycle_found_ = 0, sweep_cycle_swept_ = 0;  // finds before / variables swept in this cycle
  std::vector<Lit> sweep_added_;        // binary clauses added to the formula for this variable
  Var sweep_cursor_ = 0;
  std::vector<Kitten::KLit> def_lits_;
  std::vector<uint32_t> def_core_;
  uint64_t sweep_last_ticks_ = 0;

  Options opts_;
  uint32_t num_vars_ = 0;
  bool inconsistent_ = false;

  std::vector<int8_t> vals_;  // per literal
  std::vector<VarData> vdata_;
  std::vector<int8_t> saved_, target_, best_;  // phases per variable (+1 / -1)
  std::vector<Lit> trail_;
  size_t propagated_ = 0;
  std::vector<uint32_t> control_;  // trail size at each decision

  WordArena arena_;
  std::vector<uint32_t> clauses_;  // live clause references in arena order
  std::vector<std::vector<Watch>> watches_;  // per literal
  uint64_t irredundant_ = 0, redundant_ = 0, binaries_irredundant_ = 0, binaries_redundant_ = 0;
  uint64_t garbage_words_ = 0;
  uint64_t shrunk_words_ = 0;  // dead words left by clauses shortened in place (upper bound)
  uint32_t first_garbage_ = UINT32_MAX;  // lowest arena offset of a garbage clause since the last collection
  void note_garbage(const Clause& c) {
    const auto ref = static_cast<uint32_t>(reinterpret_cast<const uint32_t*>(&c) - arena_.data());
    if (ref < first_garbage_) first_garbage_ = ref;
  }
  void maybe_collect_garbage();
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
  std::vector<Var> shrunk_;
  std::vector<Lit> learned_;
  std::vector<Lit> backtrack_tmp_;  // literals unassigned by a chronological backtrack
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
  // Tier limits: static (options) or dynamic (glue quantiles of learned clauses used in focused-mode
  // conflict analysis, as in Kissat 4).
  static constexpr uint32_t kGlueBuckets = 64;
  uint32_t tier1_ = 2, tier2_ = 6;
  uint64_t used_glue_[kGlueBuckets] = {};
  uint64_t last_simplify_fixed_ = 0, simplify_ticks_limit_ = 0;
  uint64_t fixed_ = 0;

  // Simplification state.
  std::vector<uint8_t> eliminated_;  // per variable
  uint32_t inactive_ = 0;           // eliminated variables (never assigned)
  WordArena extension_;             // [witness, clause literals..., kNoLit]* for model reconstruction
  std::vector<int8_t> model_;       // per variable, filled after kSat
  bool model_valid_ = false;
  OccLists occs_;  // per literal: irredundant long clauses (rounds only)
  std::vector<uint8_t> touched_;    // per variable: occurrences changed since the last round
  std::vector<int8_t> marks_;       // per literal scratch marks
  struct OccClause {
    uint32_t ref;  // kNoReason for a binary clause (pivot, other)
    Lit other;
  };
  std::vector<OccClause> elim_side_[2];  // scratch of try_eliminate
  uint32_t find_xor_gate(Var v, std::vector<OccClause>* side, std::vector<uint8_t>* gate,
                         const std::vector<uint8_t>* skip, uint64_t& budget);
  bool find_ite_gate(Var v, std::vector<OccClause>* side, std::vector<uint8_t>* gate, uint64_t& budget);
  bool find_definition(Var v, std::vector<OccClause>* side, std::vector<uint8_t>* gate, uint64_t& budget);
  std::vector<uint32_t> elim_refs_;
  std::vector<uint8_t> elim_gate_[2];
  std::vector<Lit> elim_res_;
  uint64_t vivify_limit_ = 0, vivify_rounds_ = 0, vivify_last_ticks_ = 0;
  uint64_t vivify_ticks_per_clause_ = 200;  // running estimate, to order only what a round can afford
  uint32_t congruence_delay_ = 0, congruence_skip_ = 0;  // back-off after unproductive rounds
  uint64_t walk_last_ticks_ = 0;
  uint64_t lucky_limit_ = 0;
  bool lucky_tried_ = false;
  std::vector<Lit> viv_lits_, viv_decided_;
  std::vector<Var> viv_marked_;
  std::vector<uint64_t> viv_cands_;
  std::vector<uint32_t> recent_learned_;  // newest last; cleared by collections (refs move)
  void eager_subsume();
  std::vector<uint32_t> viv_count_;
  uint64_t eliminate_limit_ = 0, eliminate_rounds_ = 0, eliminate_last_ticks_ = 0;
  uint64_t eliminate_last_fixed_ = UINT64_MAX, eliminate_last_irredundant_ = 0;
  uint32_t eliminate_delay_ = 0;     // unproductive rounds in a row (back-off exponent)
  uint32_t eliminate_last_bound_ = 0;

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
  // Exclusive wall time per pass: a pass called from another (sweeping from vivification,
  // substitution from elimination) is subtracted from its caller.
  double pass_seconds_[kPassCount] = {};
  struct PassTimer;
  PassTimer* pass_top_ = nullptr;
  struct PassTimer {
    Solver& s;
    double& acc;
    PassTimer* parent;
    double nested = 0;
    std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
    PassTimer(Solver& solver, Pass p) : s(solver), acc(solver.pass_seconds_[p]), parent(solver.pass_top_) {
      s.pass_top_ = this;
    }
    PassTimer(const PassTimer&) = delete;
    PassTimer& operator=(const PassTimer&) = delete;
    ~PassTimer() {
      const double t = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
      acc += t - nested;
      if (parent) parent->nested += t;
      s.pass_top_ = parent;
    }
  };
};

}  // namespace psat
