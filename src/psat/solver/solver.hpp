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
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "psat/core/lit_stack.hpp"
#include "psat/core/options.hpp"
#include "psat/core/types.hpp"
#include "psat/core/word_arena.hpp"
#include "psat/solver/gauss.hpp"
#include "psat/solver/heap.hpp"
#include "psat/solver/kitten.hpp"
#include "psat/solver/occs.hpp"
#include "psat/solver/watches.hpp"

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
  uint32_t age : 5;  // --tier1age: reductions in a row a tier1 clause went unused
  uint32_t pos;  // where the last replacement-watch search ended; GC forwarding address

  Lit* lits() { return reinterpret_cast<Lit*>(this + 1); }
  const Lit* lits() const { return reinterpret_cast<const Lit*>(this + 1); }
};
static_assert(sizeof(Clause) == 12, "clause header must be three words");
constexpr uint32_t kHeaderWords = 3;

constexpr uint32_t kNoReason = 0xFFFFFFFFu;
constexpr uint32_t kMaxArenaWords = 0x7FFFFFF0u;
// Gauss-Jordan reasons (--gauss, detached solver only): kGaussTag | offset into the reason buffer.
// Binary reasons are kBinaryTag | literal with literals below 2^29, so both tags test true for
// (reason & kBinaryTag) and the two are told apart by reason >= kGaussTag (kNoReason excluded).
constexpr uint32_t kGaussTag = 0xC0000000u;
constexpr uint32_t kGaussMask = 0x3FFFFFFFu;
constexpr uint32_t kGaussConflict = 0x7FFFFFFFu;  // conflict_ref_ of a Gauss-Jordan conflict


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
  kPassVivify, kPassProbe, kPassSweep, kPassWalk, kPassReduce, kPassLucky, kPassUnhide, kPassSimulate, kPassCounting,
  kPassGauss, kPassBinreduce,
  kPassCount
};

// Proof statistics by source (ProofWriter::set_source): search (learned clauses), each pass
// (1 + Pass), root simplification and eager subsumption.
enum ProofSource : int { kProofSearch = 0, kProofSimplify = 1 + kPassCount, kProofEager, kProofSources };

// Cardinality constraints found by detection (cardinality.cpp; --cardinality, statistics only).
struct CardinalityStats {
  uint64_t amo = 0, amo_lits = 0, amo_pos = 0, amo_neg = 0, amo_mixed = 0;  // cliques of >= 3 literals
  uint64_t amo_binaries = 0;     // binary clauses inside those cliques
  uint64_t eo = 0, eo_clique = 0, eo_exact = 0, eo_big = 0;  // clauses that are exactly-one constraints
  uint64_t eo_lits = 0;
  uint64_t amk = 0, amk_lits = 0, amk_candidates = 0, amk_merged = 0;  // at-most-k (k >= 1) over auxiliary encodings
  uint64_t vars_active = 0, vars_covered = 0, vars_covered4 = 0, vars_amo2 = 0;  // 4: in one of >= 4 literals; amo2: in 2+ cliques
  uint64_t binaries = 0, long_clauses = 0, clauses_covered = 0;
  uint64_t work = 0;
  uint8_t incomplete = 0;  // phases that ran out of budget: 1 amo, 2 eo, 4 amk, 8 amk skipped (size)
  double seconds = 0, phase_seconds[4] = {};  // build, amo, eo, amk
  std::vector<uint32_t> amo_sizes, eo_sizes;
  std::vector<std::pair<uint32_t, uint32_t>> amk_sizes;  // (literals, k)
};

struct Stats {
  uint64_t conflicts = 0, decisions = 0, propagations = 0, ticks = 0;
  uint64_t reused_levels = 0, restart_levels = 0, backjump_levels = 0, conflict_levels = 0;
  uint64_t restarts = 0, reductions = 0, rephased = 0, switched = 0, collections = 0;
  uint64_t collections_full = 0, collected_words = 0;  // words scanned and moved from the start on
  uint64_t learned = 0, learned_units = 0, learned_binary = 0, learned_literals = 0, minimized_literals = 0, learned_glue = 0;
  uint64_t eager_subsumed = 0;
  uint64_t chrono_backtracks = 0, chrono_conflict_backtracks = 0, chrono_missed = 0, chrono_fallbacks = 0;
  uint64_t reduced_clauses = 0, reduced_tier1 = 0, simplified_root = 0, fixed = 0;
  // Tier inflow (statistics): learned clauses of glue <= tier1 from conflict analysis, other new
  // learned clauses of glue <= tier1 (vivification, unhiding), clauses whose glue fell to tier1 /
  // tier2 when used in conflict analysis.
  uint64_t tier1_learned = 0, tier1_other = 0, tier1_promoted = 0, tier2_promoted = 0;
  uint64_t eliminations = 0, eliminated = 0, resolvents = 0, subsumed = 0, strengthened = 0, substituted = 0, merged = 0;
  // Elimination breakdown: candidates tried and why they failed (occurrence limit, resolvent size,
  // clause bound, literal bound or growth cap, XOR merge), tries of a variable that failed in an
  // earlier round with its clauses unchanged since (same bound / raised bound), and the round's
  // work units by phase (occurrence lists, subsumption, congruence, gathering the clauses of a
  // candidate, syntactic gates, semantic definitions, counting resolvents, adding them) plus the
  // units of the tries that failed.
  uint64_t elim_tried = 0, elim_fail_occ = 0, elim_fail_size = 0, elim_fail_bound = 0, elim_fail_lits = 0,
           elim_fail_xor = 0, elim_retried_same = 0, elim_retried_raised = 0, elim_resolutions = 0,
           elim_long_skipped = 0;  // (--eliminatelongskip: of elim_fail_size)
  uint64_t elim_w_occs = 0, elim_w_subsume = 0, elim_w_congruence = 0, elim_w_gather = 0, elim_w_gates = 0,
           elim_w_defs = 0, elim_w_count = 0, elim_w_add = 0, elim_w_failed = 0;
  uint64_t vivifications = 0, vivify_ticks = 0, vivify_checked = 0, vivified = 0, vivified_literals = 0, vivify_instantiated = 0, vivify_implied_deleted = 0,
           vivify_asym = 0;
  uint64_t vivify_checked_learned = 0, vivified_learned = 0;  // (of vivify_checked / vivified)
  uint64_t vivify_subsumed = 0;
  uint64_t vivify_tier1_turns = 0;  // (--vivifytier1: turns of the tier1 pass completed)
  uint64_t randec_sequences = 0, random_decisions = 0;
  uint64_t unhides = 0, unhide_units = 0, unhide_transitive = 0, unhide_tautologies = 0, unhide_strengthened = 0,
           unhide_literals = 0, unhide_ticks = 0;
  uint64_t sweeps = 0, swept_vars = 0, sweep_units = 0, sweep_equivalences = 0, sweep_ticks = 0, sweep_flips = 0, sweep_solves = 0, sweep_kitten_ticks = 0;
  // Sweeping breakdown: Kitten calls per purpose (env: the first model of an environment; bb: backbone
  // checks; eq: equivalence checks) and result, candidates and how they were refuted.
  uint64_t sweep_env_solves = 0, sweep_bb_solves = 0, sweep_bb_sat = 0, sweep_bb_unsat = 0, sweep_bb_unknown = 0,
           sweep_eq_solves = 0, sweep_eq_sat = 0, sweep_eq_unsat = 0, sweep_eq_unknown = 0;
  uint64_t sweep_bb_cands = 0, sweep_bb_by_flip = 0, sweep_bb_by_model = 0, sweep_eq_cands = 0, sweep_eq_by_flip = 0,
           sweep_eq_by_model = 0, sweep_eq_checks = 0, sweep_eq_known = 0, sweep_var_limit = 0, sweep_env_vars = 0,
           sweep_env_clauses = 0, sweep_outer_dropped = 0, sweep_followed = 0, sweep_clean_skipped = 0;
  uint64_t simulations = 0, sim_gates = 0, sim_candidates = 0, sim_checked = 0, sim_equivalences = 0, sim_units = 0,
           sim_failed = 0, sim_ticks = 0, sim_ites = 0;
  uint64_t probes = 0, failed_literals = 0, probe_uips = 0, gates = 0, xor_gates = 0, xor_merges_skipped = 0, ite_gates = 0, definitions = 0, shrunk_literals = 0;
  uint64_t bva_vars = 0, bva_removed = 0, bva_added = 0, bva_hop_ties = 0, bva_trials = 0, bva_rounds = 0;
  uint64_t bva_search_vars = 0, bva_search_rounds = 0;  // --bvasearch
  uint64_t deduplicated = 0;  // duplicate binary clauses removed
  uint64_t binpair_units = 0, binpair_rounds = 0, binpair_binaries = 0;  // --binpairunits
  uint64_t tern_binaries = 0, tern_subsumed = 0;  // --congruencetern
  uint64_t binreduce_rounds = 0, binreduce_checked = 0, binreduce_deleted = 0, binreduce_cut = 0, binreduce_ticks = 0;  // --binreduce
  uint64_t stop_faults = 0;   // --stopfault (testing): stops injected
  uint64_t walks = 0, walks_kept = 0, walk_flips = 0, walk_ticks = 0, walk_models = 0, walk_transfers = 0, congruent = 0, congruent_xors = 0, congruent_ites = 0, congruence_rewrites = 0, lucky = 0;
  uint64_t model_walks = 0, model_walks_skipped = 0, model_walk_ticks = 0;  // --walkmode=3
  uint64_t stable_conflicts = 0, focused_conflicts = 0;
  uint64_t original_clauses = 0;
  // Counting certificates (counting.cpp): structures found, PR clauses and units added, structures
  // abandoned (a failed check) or skipped (over budget), work units (detection included).
  uint64_t counting_found = 0, counting_pr = 0, counting_units = 0, counting_lemmas = 0, counting_failed = 0,
           counting_skipped = 0, counting_work = 0;
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

  void set_proof(ProofWriter* proof);
  void set_terminate(const std::atomic<bool>* flag) { terminate_ = flag; }
  void set_time_limit(double seconds) { time_limit_ = seconds; }
  void set_conflict_limit(int64_t conflicts) { conflict_limit_ = conflicts; }
  void set_memory_limit(uint64_t bytes) { memory_limit_ = bytes; }

  const Stats& stats() const { return stats_; }
  // The first cardinality detection run (--cardinality).
  const CardinalityStats& cardinality_stats() const { return card_stats_; }
  // XOR detection and Gauss-Jordan elimination (--gauss).
  const GaussStats& gauss_stats() const { return gauss_stats_; }
  const XorSubStats& xorsub_stats() const { return xorsub_stats_; }
  const LinmodStats& linmod_stats() const { return linmod_stats_; }
  const Options& options() const { return opts_; }
  // Why the last solve() returned kUnknown ("" otherwise).
  const char* unknown_reason() const { return unknown_reason_; }
  size_t memory_bytes() const;
  // --reportmem: the resident size (current and peak) and the main structures, one line.
  void report_memory(const char* where);
  // --reportmem, in the search: cumulative counts, the learned clauses by tier, the schedules
  // (mode, rephase, reduce) and the pass times, one line of key=value pairs (output only).
  void report_progress();
  static double current_rss_mb();
  // Bytes the C library's allocator has handed out and not got back (macOS: malloc zone
  // statistics; glibc 2.33+: mallinfo2); -1 where unknown. Resident size minus this is memory the
  // allocator keeps (freed blocks cached or not returned, fragmentation) plus untouched code/stack.
  static double heap_in_use_mb();
  // --reportmem: memory the caller holds for the solver (the model-check copy of the input).
  void set_input_copy_bytes(size_t bytes) { input_copy_bytes_ = bytes; }
  size_t input_copy_bytes_ = 0;
  double report_next_ = 0, progress_next_ = 0;
  double seconds() const;
  static double peak_rss_mb();  // of the process (getrusage)
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
  // A root unit whose clause is already in the proof (or the formula): assigned without logging
  // it a second time (its propagated consequences are logged as usual).
  void assign_unit_in_proof(Lit l) {
    unit_in_proof_ = true;
    assign(l, kNoReason);
    unit_in_proof_ = false;
  }
  bool unit_in_proof_ = false;

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
  bool propagate_search();  // propagate() without Gauss-Jordan
  bool propagate_vivify(uint32_t ignore);
  template <bool kVivify, bool kPrefetch, bool kStats = false, int kProp = 0>
  bool propagate_impl(uint32_t ignore);  // (propagate.cpp only)
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
  // --queueorder (order.cpp): the initial focused-mode order (lowest input index first, where
  // and when the option value says so).
  void initial_queue_order();
  void queue_lowest_first();
  struct GateDirection {
    uint64_t gates = 0, forward = 0, backward = 0, outputs = 0, work = 0;
    bool complete = true;
  };
  GateDirection gate_direction(uint64_t budget);
  bool gates_forward();
  void queue_default_order_unbumped();
  // --queuescores (order.cpp): the focused-mode queue takes the stable-mode score order.
  void queue_score_order();
  // --stablereorder (order.cpp): stable-mode scores from weighted clause occurrences.
  void stable_occurrence_scores();

  // --- schedules ------------------------------------------------------------------------------
  bool restarting() const;
  void restart();
  uint64_t focused_restart_interval() const;
  uint32_t reuse_trail_level();
  // (--rephasestable: only in stable mode, unless the search never enters it; 2: the interval
  // counts stable-mode conflicts)
  bool rephasing() const {
    if (!opts_.rephase) return false;
    if (opts_.rephasestable && !stable_ && opts_.stable != 0) return false;
    return (opts_.rephasestable == 2 && opts_.stable != 0 ? stats_.stable_conflicts : stats_.conflicts) >= rephase_limit_;
  }
  void rephase();
  bool reducing() const { return stats_.conflicts >= reduce_limit_; }
  void reduce();
  void update_tier_limits();
  bool switching() const;
  void switch_mode();
  void update_conflict_statistics(uint32_t glue);
  bool check_limits();
  // Inprocessing passes and the work before search call stop_requested() in their main loops
  // (per candidate, variable, clause or Kitten call, per flip of the walk): true once the time
  // limit has passed or termination was requested. When it is, the pass ends as when its budget
  // runs out, and so does every pass after it (the answer stays true until solve() starts again),
  // until the search loop's check_limits() returns with the reason. The terminate flag is read on
  // every call, the clock every stop_period_ calls: the period doubles while the clock reads come
  // less than 0.1 ms apart and drops to a quarter when they are more than 1 ms apart, from 1 at
  // the start and at the end of every pass (PassTimer), whose calls differ in cost.
  // --stopfault=n (testing): every n-th call requests a stop that check_limits() then drops, so
  // the search goes on after the interrupted passes (their formula must be consistent).
  bool stop_requested() {
    if (stop_reason_) return true;
    if (terminate_ && terminate_->load(std::memory_order_relaxed)) {
      stop_reason_ = "interrupted";
      return true;
    }
    if (--stop_countdown_ != 0) return false;
    return stop_check();
  }
  bool stop_check();
  void stop_period_reset() {
    if (!opts_.stopfault) stop_period_ = stop_countdown_ = 1;
  }
  static constexpr const char* kStopFault = "stop fault (testing)";
  // A sub-solver (the detached Gauss-Jordan solver, an isolated counting refutation) that stopped
  // on the shared limits: this solver stops too.
  void stop_after(const Solver& sub) {
    if (sub.stop_reason_ && sub.stop_reason_ != kStopFault) stop_reason_ = sub.stop_reason_;
  }
  bool memory_exceeded(bool accounting) const;
  void debug_check(const char* where);
  void dump_simplified();

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
  void merge_pairs();                               // --mergepairs (subsume.cpp)
  bool strengthen_irredundant(uint32_t ref, Lit remove);  // true: the clause became binary
  bool substitute();
  void substitute_rounds();
  uint64_t dedup_binaries();
  bool binary_pair_units();  // --binpairunits (substitute.cpp); false: inconsistent
  bool binary_pair_units_pass();
  void substitute_now();  // outside elimination rounds, at the root
  uint32_t congruence(uint64_t& budget);
  uint32_t ternary_binaries(uint64_t& budget);  // --congruencetern
  uint32_t elim_clslim() const {  // --eliminateclslim, or --eliminateclslim1 in the first round
    return static_cast<uint32_t>(eliminate_rounds_ == 1 && opts_.eliminateclslim1 ? opts_.eliminateclslim1 : opts_.eliminateclslim);
  }
  uint32_t congruent_xors(uint64_t& budget);
  uint32_t congruent_ites(uint64_t& budget);
  // Gate extraction for congruence: XOR constraints (complete clause sets of 3..5 variables: the
  // variables and the parity of their sum) and ITE gates o = ITE(c, t, e) (c and t positive).
  struct CongruenceXor {
    Var vars[5];
    uint8_t n, parity;
  };
  struct CongruenceIte {
    Lit c, t, e, o;
  };
  void extract_xor_constraints(std::vector<CongruenceXor>& out, uint64_t& budget);
  void extract_ites(std::vector<CongruenceIte>& out, uint64_t& budget);
  void prove_by_cases(std::vector<Lit>& clause, const std::vector<Var>& cases, size_t depth);
  // -> clauses removed (estimated if dry); touched_only: matchings start only from literals of
  // touched variables (--bvasearch rounds during search)
  int64_t bva_round(uint64_t& budget, uint64_t limit, bool dry, bool touched_only = false);
  uint64_t bva_last_span_ = 0;   // ticks the last round spent (--bvaextend)
  int64_t bva_target_ = 0;       // --bvarealtarget: the qualifying trial's reduction (real round only)
  uint32_t bva_last_added_ = 0;  // variables the last round added (would add, if dry)
  void bva_run(uint64_t& budget);  // a trial round first with --bvamin
  size_t bva_count(Lit l, uint64_t& budget);
  // --bvasearch: BVA in an elimination round after the first (after its eliminations), and the
  // elimination bound of a variable (0 for BVA variables, so that elimination does not undo BVA).
  void bva_search(uint64_t& budget);
  uint32_t bva_elim_bound(Var v, uint32_t bound) const {
    return opts_.bvasearch && v < bva_added_.size() && bva_added_[v] ? 0 : bound;
  }
  bool try_eliminate(Var v, uint32_t bound, uint64_t& budget);
  void gather_occurrences(Lit l, std::vector<uint32_t>& out, uint64_t& budget);
  void delete_irredundant(uint32_t ref);
  void delete_binary(Lit a, Lit b);  // an irredundant binary clause
  void remove_binary_watch(Lit owner, Lit other, bool redundant);
  void touch_clause(const Lit* lits, uint32_t size);
  void push_extension(Lit witness, const Lit* lits, uint32_t size);
  void extend_model();
  void reconstruct_model(size_t end);  // model_ through the reconstruction stack [0, end)
  void walk();
  bool lucky();
  bool vivifying() const { return opts_.vivify && stats_.conflicts >= vivify_limit_; }
  void vivify();
  // Candidates of a vivify_clauses pass: irredundant clauses, learned clauses of tier1 and tier2
  // (one pass, the default), and with --vivifytier1 tier1 and the rest (tier2) separately.
  enum class VivifyPass { kIrredundant, kLearned, kTier1, kTier2 };
  void vivify_clauses(VivifyPass pass, uint64_t ticks_limit);
  bool vivify_candidates(VivifyPass pass, uint64_t ticks_limit, std::vector<uint32_t>* tried);
  bool vivify_clause(uint32_t ref, const Lit* lits, uint32_t n);
  void vivify_analyze(Lit implied, bool track_redundant);
  bool vivify_subsumed(Lit implied, bool redundant);
  bool irredundant_binary(Lit a, Lit b);
  bool viv_used_redundant_ = false;  // the last vivify_analyze used a learned clause
  void probe_failed_literals(uint64_t ticks_limit);
  Lit probe_uip();
  void unhide(uint64_t ticks_limit);
  // --binstats (binaries.cpp, statistics only): a census of the learned binary clauses with every
  // progress line (duplicates, transitive in the binary implication graph, never / recently
  // unused) and the watches the search visited by kind since the last one.
  struct BinCensus {
    uint64_t visit_red = 0, visit_irr = 0, visit_long = 0, implied_red = 0, implied_irr = 0;  // (propagate_impl<kStats>)
    uint64_t last_visit_red = 0, last_visit_irr = 0, last_visit_long = 0, last_implied_red = 0, last_implied_irr = 0,
             last_props = 0;
    uint32_t epoch = 0;  // censuses so far
    double seconds = 0;  // their time
  };
  BinCensus bin_census_;
  void binary_census();
  // --binreduce (binaries.cpp): transitive reduction of the learned binary clauses at the root.
  void reduce_binaries(uint64_t ticks_limit);
  bool binary_implied(Lit a, Lit b, uint64_t& ticks);
  std::vector<uint32_t> binreduce_seen_;  // per literal: stamp of the search that reached it
  std::vector<Lit> binreduce_queue_, binreduce_cands_;
  uint32_t binreduce_stamp_ = 0;
  Lit binreduce_next_ = 0;  // literal to continue with
  std::vector<uint32_t> unhide_start_, unhide_dsc_, unhide_fin_;
  std::vector<Lit> unhide_target_;
  size_t unhide_next_ = 0;  // long clause to continue with
  void sweep(uint64_t min_budget = 100000);
  bool sweep_initial_done_ = false;
  uint32_t sweep_delay_ = 0, sweep_skip_ = 0;  // back-off after unproductive sweeps
  bool sweep_variable(Var v, const std::vector<uint32_t>& start, const std::vector<uint32_t>& occ, uint64_t& ticks);
  bool sweep_classes(uint32_t n);  // backbone / equivalence candidates as classes (Kissat)
  void sweep_emit_learned();
  void sweep_mark_learned_units();
  bool sweep_add(const Lit* lits, uint32_t size);
  void sweep_retire_learned();
  void simulate_equivalences();
  void detect_cardinality(const char* when);  // statistics only: reads the clauses, changes nothing
  // Counting certificates (counting.cpp, --counting): PR refutations of detected pigeonhole,
  // parity and Count^3 systems, before search.
  struct CountingState;
  struct CountingPlan;
  void counting();
  bool counting_detect(CountingState& st);
  bool counting_certify(CountingState& st);
  bool counting_detect_clique(CountingState& st);
  bool counting_detect_rphp(CountingState& st);
  bool counting_detect_embedded(CountingState& st);
  bool counting_detect_sparse(CountingState& st, bool probe);
  bool counting_virtual(CountingState& st);
  bool counting_isolated(CountingState& st);
  bool counting_isolated_sparse(CountingState& st);
  void counting_plan(CountingState& st);
  bool counting_extend(CountingState& st, uint32_t base);
  bool counting_add(CountingState& st, const Lit* c, size_t nc, const Lit* w, size_t nw);
  bool counting_add_unit(CountingState& st, Lit u);
  bool counting_check_pr(CountingState& st, const Lit* c, size_t nc, const Lit* w, size_t nw);
  bool counting_implied(CountingState& st, const Lit* lits, size_t n);
  bool counting_refutes(const Lit* lits, size_t n);
  bool counting_tried_ = false;
  bool counting_added_ = false;  // PR clauses were added: later clauses could make them unsound
  std::string counting_desc_;    // the structure found (statistics)
  // An input clause was a tautology (dropped here, kept by the checker) or repeated a literal
  // (dpr-trim reads a clause whose first literal repeats as a PR line: the clause up to the
  // repetition, with the rest as a witness, so its formula is not ours). PR checks need the
  // checker's clauses to be the solver's (plus satisfied ones): no counting certificates then.
  bool input_irregular_ = false;
  // An input clause lost root-false literals: the checker keeps the longer clause, which the
  // deletions of an isolated refutation (counting_isolated) cannot name.
  bool input_shortened_ = false;
  bool counting_isolated_ = false;  // this solver refutes an isolated subsystem (no nested search for one)
  const CountingPlan* counting_plan_ = nullptr;  // ... by elimination, on this structure (no detection)

  // --- Gauss-Jordan elimination (gauss.cpp, --gauss) ------------------------------------------
  // The main solver extracts XORs and, if the formula has enough of them, runs a detached solver
  // (gauss_sub_: a copy of the irredundant clauses, Gauss-Jordan propagation on, no proof, no
  // elimination) in rounds besides its own search. Only a model can come back from it (extended
  // with the main solver's reconstruction stack as of the copy); nothing it learns reaches the
  // main solver's clauses or the proof.
  void extract_xors(XorList& out, uint64_t max_size);
  bool gauss_start();   // true: the detached solver found a model (imported); inconsistent_: refuted
  bool gauss_refute(const XorList& xors);
  void gauss_facts(const XorList& xors);  // root units / equivalences implied (--gaussfacts)
  void xor_unsubstitute();  // XOR-substitution reversal before search (xorsub.cpp, --xorsub)
  XorSubStats xorsub_stats_;
  bool xorsub_tried_ = false;
  bool linmod();  // linear equations mod p on one-hot domains (linmod.cpp, --linmod); true: model found
  LinmodStats linmod_stats_;
  bool linmod_tried_ = false;
  bool gauss_prove(const std::vector<uint32_t>& rows, const XorList& xors);
  bool gauss_round();   // true: likewise
  bool gauss_run(uint64_t ticks);
  void gauss_import_model();
  bool gauss_due() const { return gauss_sub_ && stats_.ticks >= gauss_next_ticks_; }
  // Gauss-Jordan propagation (in the detached solver).
  bool gauss_init(const XorList& xors);  // false: the XORs are inconsistent
  bool propagate_with_gauss();
  bool gauss_propagate();
  bool gauss_process_queue();
  bool gauss_fix_row(uint32_t m, uint32_t r, uint32_t trigger);
  void gauss_pivot(uint32_t m, uint32_t r, uint32_t col, uint32_t trigger);
  // trigger: the column whose assignment queued the row (kNone: pivot or reopen).
  void gauss_enqueue(uint32_t m, uint32_t r, uint32_t trigger = UINT32_MAX) {
    GaussMatrix& M = gauss_mats_[m];
    if (M.queued[r]) return;
    M.queued[r] = 1;
    gauss_queue_.push_back(GaussQueued{m, r, trigger});
  }
  void gauss_backtrack(uint32_t new_level);
  Var gauss_decision(Var linear);  // an unassigned variable outside the matrices, else `linear`
  std::vector<Var> gauss_free_;   // variables outside the matrices
  void gauss_conflict_from_row(uint32_t m, uint32_t r);
  const Lit* gauss_reason(uint32_t reason, uint32_t& n) const {
    const Lit* p = gauss_reasons_.data() + (reason & kGaussMask);
    n = p[0];
    return p + 1;
  }
  bool gauss_on_ = false;  // this solver propagates XORs by Gauss-Jordan (the detached solver)
  std::vector<GaussMatrix> gauss_mats_;
  std::vector<uint32_t> gauss_mat_, gauss_col_;  // per variable: matrix and column (kNone: none)
  size_t gauss_qhead_ = 0;                        // trail literals already in the matrices' view
  std::vector<GaussQueued> gauss_queue_;          // rows to check
  std::vector<Lit> gauss_reasons_;                // [size, propagated literal, false literals...]*
  std::vector<Lit> gauss_conflict_;
  std::vector<GaussClosed> gauss_closed_;  // levels non-decreasing
  GaussStats gauss_stats_;
  std::unique_ptr<Solver> gauss_sub_;
  bool gauss_tried_ = false;
  uint32_t gauss_sub_vars_ = 0;   // variables of the copy
  size_t gauss_ext_size_ = 0;     // reconstruction stack size at the copy
  uint64_t gauss_next_ticks_ = 0, gauss_last_ticks_ = 0;
  // Adaptive share (--gaussadapt): current share (per mille of search ticks), detached solver
  // ticks granted and used in rounds (an overshoot is paid back), counters at the last evaluation.
  uint64_t gauss_share_ = 0, gauss_granted_ = 0, gauss_used_ = 0;
  uint64_t gauss_eval_conflicts_ = 0, gauss_eval_gauss_conflicts_ = 0, gauss_eval_rounds_ = 0;
  uint64_t ticks_limit_ = 0;      // search stops (unknown) at this many ticks (0: none)
  CardinalityStats card_stats_;
  uint32_t card_runs_ = 0;
  Kitten kitten_;
  std::vector<uint32_t> sweep_local_;   // per variable: index in the environment or UINT32_MAX
  std::vector<Var> sweep_env_;          // environment variables (local index -> variable)
  std::vector<uint32_t> sweep_stamp_;   // per long clause (CSR index): environment stamp
  uint32_t sweep_stamp_now_ = 0;
  std::vector<uint8_t> sweep_emitted_;  // per kitten learned clause: already in the proof
  std::vector<Lit> sweep_emitted_lits_; // their literals (flat, size-prefixed) for deletion
  std::vector<uint32_t> sweep_backbone_, sweep_partition_, sweep_next_;  // Kitten literals (sweep_classes)
  std::vector<uint32_t> sweep_merged_;  // per variable: the sweep round (--sweepknown=2: substitute_epoch_ + 1) that proved it equivalent
  uint32_t substitute_epoch_ = 0;       // substitute() calls (equivalences proved before are merged after one)
  uint32_t sweep_lim_vars_ = 0, sweep_lim_clauses_ = 0, sweep_lim_depth_ = 0;  // this round's environment limits
  std::vector<uint8_t> bva_added_;  // per variable: introduced by BVA
  uint32_t sweep_growth_ = 0;              // growth steps of the limits (--sweepgrow)
  uint64_t sweep_cycle_found_ = 0, sweep_cycle_swept_ = 0;  // finds before / variables swept in this cycle
  std::vector<Lit> sweep_added_;        // binary clauses added to the formula for this variable
  std::vector<uint32_t> sweep_depth_;   // per environment variable: its depth (steps from the swept one)
  std::vector<Var> sweep_follow_;       // --sweepfollow: variables to sweep next (before the cursor)
  std::vector<uint8_t> sweep_dirty_;    // per variable: clauses changed (touch_var) since it was swept
  std::vector<uint8_t> sweep_queued_;   // per variable: in sweep_follow_
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
  LitStack trail_;  // (lit_stack.hpp: push_back small enough to inline)
  size_t propagated_ = 0;
  std::vector<uint32_t> control_;  // trail size at each decision

  WordArena arena_;
  std::vector<uint32_t> clauses_;  // live clause references in arena order
  WatchLists watches_;  // per literal, in one pool (watches.hpp)
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
  std::vector<Var> probe_marked_;  // probe_uip()
  std::vector<Var> minimized_;
  std::vector<Var> shrunk_;
  std::vector<uint64_t> sort_keys_, sort_tmp_;  // bump_variables() and shrink_clause() scratch
  std::vector<Lit> learned_;
  std::vector<Lit> backtrack_tmp_;  // literals unassigned by a chronological backtrack
  // --chrono=2: the backjump level of the last chronological backtrack and the decision count
  // then (a missed implication before the next decision falls back to that backjump).
  uint32_t chrono_jump_ = UINT32_MAX;
  uint64_t chrono_decisions_ = 0;
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
  // Random decision sequences (--randec): due at randec_limit_ conflicts (the next restart starts
  // one from the root), then randec_left_ conflicts with random decisions and no restarts.
  uint64_t randec_limit_ = 0, randec_left_ = 0;
  uint64_t randec_rng_ = 0;
  bool randec_due() const {
    return opts_.randec && !randec_left_ && stats_.conflicts >= randec_limit_ && (!stable_ || opts_.randecstable);
  }
  void end_random_sequence();
  Var random_decision();
  uint32_t target_assigned_ = 0, best_assigned_ = 0;
  uint64_t rephase_limit_ = 0, rephase_count_ = 0;
  uint64_t reduce_limit_ = 0;
  // Tier limits: static (options) or dynamic (glue quantiles of learned clauses used in focused-mode
  // conflict analysis, as in Kissat 4).
  static constexpr uint32_t kGlueBuckets = 64;
  uint32_t tier1_ = 2, tier2_ = 6;
  uint64_t used_glue_[kGlueBuckets] = {};
  // --dynamictiers=2: per mode (index stable_), the glue histogram of used clauses and its limits.
  uint64_t mode_used_glue_[2][kGlueBuckets] = {};
  uint32_t mode_tier1_[2] = {2, 2}, mode_tier2_[2] = {6, 6};
  // --tierstats (statistics only): tier1 clauses' ages (reductions in a row unused, as --tier1age
  // counts them) are kept, and a use of an aged clause in conflict analysis is a revival. exposure
  // counts (clause, reduction) pairs by the age after the reduction, revived the revivals by the age
  // they ended, so revived / exposure is the chance that a clause of that age is used again before
  // the next reduction. Buckets: age 0, 1, 2-3, 4-7, 8-15, 16-31.
  static constexpr int kAgeBuckets = 6;
  static int age_bucket(uint32_t age) { return age == 0 ? 0 : age == 1 ? 1 : age <= 3 ? 2 : age <= 7 ? 3 : age <= 15 ? 4 : 5; }
  struct TierStats {
    uint64_t exposure[kAgeBuckets] = {}, revived[kAgeBuckets] = {};
    uint64_t last_exposure[kAgeBuckets] = {}, last_revived[kAgeBuckets] = {};
    // Uses of learned clauses in conflict analysis by their glue before the recomputation (1-7,
    // 8+), focused and stable mode, cumulative (as Kissat's "glue usage" statistics).
    uint64_t used_glue[2][9] = {};
    // Vivification by the kind of the checked clause (irredundant, tier1, tier2, tier3):
    // checked, shortened (replaced by a subset), deleted (implied or subsumed), literals removed
    // (counted without --tierstats too, for the final statistics).
    uint64_t viv_checked[4] = {}, viv_shortened[4] = {}, viv_deleted[4] = {}, viv_literals[4] = {};
    // Ticks spent on the clauses of each pass (VivifyPass order: irredundant, shared learned,
    // --vivifytier1's tier1 and tier2).
    uint64_t viv_ticks[4] = {};
  };
  TierStats tier_stats_;
  void report_tiers();
  // --propstats (statistics only, propagate_impl<kProp>, search propagation; the search is the
  // same): what the watch lists cost, by interval between progress lines (propagate.cpp,
  // report_propstats). visit[] / implied[] / conflict[] are by the visited clause's kind:
  // irredundant, tier1, tier2, tier3; psm_* by the share of a visited clause's literals that the
  // saved phases satisfy (quartiles), tier1 or not. --propstats=2 also feeds the cache lines
  // propagation touches (watch slices and the clause bytes read, 64-byte lines) to set-associative
  // LRU models of 32 KB, 256 KB, 2 MB and 8 MB (an x86 L1, L2, a quarter and all of an i7 L3).
  struct CacheModel {
    uint32_t sets = 0, ways = 0;
    std::vector<uint64_t> tags;  // per set, most recent first (0: empty)
    uint64_t access = 0, miss = 0;
    void init(size_t bytes, uint32_t w) {
      ways = w;
      sets = static_cast<uint32_t>(bytes / 64 / w);
      tags.assign(size_t{sets} * w, 0);
    }
    void touch(uint64_t line) {
      ++access;
      uint64_t* t = tags.data() + static_cast<size_t>(line % sets) * ways;
      const uint64_t tag = line + 1;
      uint32_t k = 0;
      while (k < ways && t[k] != tag) ++k;
      if (k == ways) {
        ++miss;
        k = ways - 1;
      }
      for (; k > 0; --k) t[k] = t[k - 1];
      t[0] = tag;
    }
  };
  struct PropStats {
    uint64_t props = 0, lists = 0, list_watches = 0, bin = 0, longw = 0, blocked = 0, garbage = 0;
    uint64_t visit[4] = {}, implied[4] = {}, conflict[4] = {};
    uint64_t other_true = 0, repl_true = 0, moved = 0, lits_read = 0, lines = 0;
    uint64_t nanos = 0, calls = 0;
    uint64_t psm_visit[2][4] = {}, psm_implied[2][4] = {};  // [tier1][PSM quartile]
  };
  PropStats prop_stats_, prop_last_;
  CacheModel prop_cache_[4];
  uint64_t prop_last_miss_[4] = {};
  double prop_last_seconds_ = 0;
  uint64_t prop_last_ticks_ = 0;
  void report_propstats();
  uint32_t psm_quartile(const Clause& c) const;
  // --tier1revive (reduce.cpp): per age 1-31 the decayed exposure and revivals of unused tier1
  // clauses (as tier_stats_, by exact age), and the age limit they set (32: none).
  double revive_exposure_[32] = {}, revive_count_[32] = {};
  uint32_t revive_limit_ = 32;
  void update_revive_limit();
  uint64_t last_simplify_fixed_ = 0, simplify_ticks_limit_ = 0;
  uint64_t fixed_ = 0;
  Stats progress_;  // statistics at the last progress line (-v 3, at reductions)

  // Simplification state.
  std::vector<uint8_t> eliminated_;  // per variable
  uint32_t inactive_ = 0;           // eliminated variables (never assigned)
  WordArena extension_;             // [witness, clause literals..., kNoLit]* for model reconstruction
  std::vector<int8_t> model_;       // per variable, filled after kSat
  bool model_valid_ = false;
  OccLists occs_;  // per literal: irredundant long clauses (rounds only)
  std::vector<uint8_t> touched_;    // per variable: occurrences changed since the last round
  uint64_t touched_count_ = 0;      // variables marked in touched_ (recounted after each round)
  void touch_var(Var v) {
    if (v < sweep_dirty_.size()) sweep_dirty_[v] = 1;
    if (!touched_[v]) {
      touched_[v] = 1;
      ++touched_count_;
    }
  }
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
  // Growth of the irredundant formula by the eliminations of the current round (resolvents minus
  // removed clauses, and the same in literals; eliminations that added clauses).
  int64_t elim_round_clauses_ = 0, elim_round_lits_ = 0;
  uint64_t elim_round_growing_ = 0;
  // --eliminategrowth: irredundant literals before the first round (the reference) and the cap on
  // the irredundant literals during the current round (UINT64_MAX: none); rejected eliminations.
  uint64_t elim_ref_lits_ = 0, elim_cap_lits_ = UINT64_MAX, elim_round_lits_start_ = 0;
  uint64_t elim_capped_ = 0;
  // Per variable: the bound of the round in which its last try failed plus one (0: none since its
  // clauses last changed; statistics of repeated tries).
  std::vector<uint32_t> elim_failed_bound_;
  // --eliminatelongskip: per variable, its last try failed on the resolvent size limit.
  std::vector<uint8_t> elim_size_failed_;
  // --eliminateheap: per literal its irredundant clauses (long and binary) during a round's
  // eliminations, and the variables whose counts the last try changed.
  std::vector<uint32_t> elim_noccs_;
  std::vector<uint64_t> elim_nlits_;  // (--eliminateheap=2: literals of those clauses)
  std::vector<Var> elim_changed_;
  std::vector<uint8_t> elim_changed_mark_;
  void elim_count(const Lit* lits, uint32_t size, int delta);
  uint64_t irredundant_literals() const;
  uint64_t vivify_limit_ = 0, vivify_rounds_ = 0, vivify_last_ticks_ = 0;
  uint64_t vivify_ticks_per_clause_ = 200;  // running estimate, to order only what a round can afford
  uint64_t vivify_ticks_per_tier1_ = 200;   // (the same for the --vivifytier1 pass)
  uint32_t congruence_delay_ = 0, congruence_skip_ = 0;  // back-off after unproductive rounds
  uint64_t walk_last_ticks_ = 0;
  bool queue_ordered_ = false;  // --queueorder applied
  uint64_t order_stamp_ = 0;   // --queueorder=3 / 4: queue stamp after the lowest-first order
  bool order_revert_ = false;  // --queueorder=3 / 4: lowest first in the first focused phase only
  size_t walk_record_ = SIZE_MAX;  // fewest unsatisfied clauses a walk ended with (--walkrecord)
  // --walkmodel: far model walks in a row and the calls left to skip; the last model walk's
  // minimum, the lowest one, whether the last one set it, and the lowest ProbSAT walk minimum
  uint32_t walk_model_far_ = 0;
  uint64_t walk_model_skip_ = 0;
  size_t walk_model_last_ = SIZE_MAX, walk_model_best_ = SIZE_MAX, walk_model_phase_best_ = SIZE_MAX;
  bool walk_model_improved_ = true;
  uint64_t lucky_limit_ = 0;
  bool lucky_tried_ = false;
  std::vector<Lit> viv_lits_, viv_decided_;
  std::vector<Var> viv_marked_;
  std::vector<uint64_t> viv_cands_;
  std::vector<uint32_t> viv_tried_;  // (--vivifytier1: the clauses a separate pass tried)
  std::vector<uint32_t> recent_learned_;  // newest last; cleared by collections (refs move)
  void eager_subsume();
  std::vector<uint32_t> viv_count_;
  uint64_t eliminate_limit_ = 0, eliminate_rounds_ = 0, eliminate_last_ticks_ = 0;
  uint64_t eliminate_last_fixed_ = UINT64_MAX, eliminate_last_irredundant_ = 0;
  uint32_t eliminate_delay_ = 0;     // unproductive rounds in a row (back-off exponent)
  bool merge_productive_ = false;    // --mergepairs: the last call merged a pair (later rounds run it only then)
  uint32_t eliminate_last_bound_ = 0;
  // --eliminatecomplete: bound raises so far (each after a round that tried all its candidates)
  // and whether the last round left candidates untried.
  uint32_t eliminate_level_ = 0;
  bool eliminate_incomplete_ = false;
  uint32_t elimination_bound() const;  // the bound of the next round
  // --eliminatecircuit: the formula is an AND circuit numbered inputs first (decided before the
  // first round); elimination then runs as with --eliminateheap=1 --eliminatecomplete=1.
  bool elim_circuit_ = false;
  int64_t elim_heap_mode() const { return opts_.eliminateheap ? opts_.eliminateheap : (elim_circuit_ ? 1 : 0); }
  int64_t elim_complete_mode() const {
    return opts_.eliminatecomplete ? opts_.eliminatecomplete : (elim_circuit_ ? 1 : 0);
  }
  bool circuit_formula(int64_t outputs_per_mille, const char* what);

  // Input.
  std::vector<int> adding_;
  std::vector<Lit> clause_buf_;

  // --- renumbering (renumber.cpp, --renumber) --------------------------------------------------
  // Once, at the first solve() before anything else: the variables get new internal indices in a
  // locality order. Input variable v (0-based) is internal variable renum_int_[v]; internal
  // literal l is renum_ext_[l] in the input numbering (the proof writer's map). Variables added
  // later (BVA, XOR substitution) keep their index on both sides, above the input's. Empty: none.
  void renumber();
  void renumber_bfs(std::vector<Var>& order) const;
  void renumber_apply(const std::vector<Var>& order);
  double renumber_span(const std::vector<Var>* to_new) const;
  Var internal_var(Var input) const { return input < renum_int_.size() ? renum_int_[input] : input; }
  Lit external_lit(Lit l) const { return l < renum_ext_.size() ? renum_ext_[l] : l; }
  std::vector<Var> renum_int_;
  std::vector<Lit> renum_ext_;
  bool renumber_tried_ = false;
  double renumber_seconds_ = 0;

  // Limits and output.
  ProofWriter* proof_ = nullptr;
  const std::atomic<bool>* terminate_ = nullptr;
  double time_limit_ = 0;
  int64_t conflict_limit_ = -1;
  uint64_t memory_limit_ = 0;
  uint64_t limit_check_ = 0;
  uint64_t clock_ticks_ = 0;  // check_limits(): the clock is read again at this many search ticks
  const char* stop_reason_ = nullptr;  // "time limit" or "interrupted" once noticed (see stop_requested())
  uint32_t stop_countdown_ = 1, stop_period_ = 1;
  double stop_last_ = 0;  // seconds() at the last clock read of stop_requested()
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
    int proof_saved;
    Pass pass;
    double rss0 = 0;  // --reportmem: resident size at the start
    PassTimer(Solver& solver, Pass p)
        : s(solver), acc(solver.pass_seconds_[p]), parent(solver.pass_top_), proof_saved(solver.proof_enter(1 + p)),
          pass(p) {
      s.pass_top_ = this;
      s.stop_period_reset();
      if (s.opts_.reportmem) rss0 = current_rss_mb();
    }
    PassTimer(const PassTimer&) = delete;
    PassTimer& operator=(const PassTimer&) = delete;
    ~PassTimer() {
      const std::chrono::steady_clock::time_point t1 = std::chrono::steady_clock::now();
      const double t = std::chrono::duration<double>(t1 - t0).count();
      acc += t - nested;
      if (parent) parent->nested += t;
      s.pass_top_ = parent;
      s.stop_period_reset();
      s.proof_leave(proof_saved);
      if (s.opts_.reportmem) s.report_pass_rss(pass, rss0, t);
      if (s.time_limit_ > 0 && s.opts_.verbose) s.report_late_pass(pass, t0, t1);
    }
  };
  void report_pass_rss(Pass p, double rss0, double seconds);
  // -v with a time limit: a pass that was running when the limit passed (its start and end).
  void report_late_pass(Pass p, std::chrono::steady_clock::time_point t0, std::chrono::steady_clock::time_point t1) const;
  // Proof lines written in a scope are counted for a source (statistics only).
  int proof_enter(int source);
  void proof_leave(int saved);
  struct ProofScope {
    Solver& s;
    int saved;
    ProofScope(Solver& solver, int source) : s(solver), saved(solver.proof_enter(source)) {}
    ProofScope(const ProofScope&) = delete;
    ProofScope& operator=(const ProofScope&) = delete;
    ~ProofScope() { s.proof_leave(saved); }
  };
};

}  // namespace psat
