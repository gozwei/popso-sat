#pragma once
// Kitten: a small CDCL solver for local sub-formulas (as Kissat's kitten), used by sweeping to
// find backbone literals and equivalences in the environment of a variable.
//
// Variables are local (0 .. n-1, literals 2v+sign as in the main solver). Solving takes
// assumptions and a ticks limit. Learned clauses are kept for the lifetime of an instance (until
// clear()) in derivation order, so that a caller writing a DRAT proof can emit them before a
// clause derived from them: each learned clause is RUP with respect to the original clauses and
// the earlier learned ones, and after an unsatisfiable result under assumptions, final_clause()
// (the negations of the assumptions involved) is RUP as well.
//
// Unsat cores (for definition mining): original clauses carry a caller id, learned clauses record
// the clauses they were resolved from, and literals false at the root stay in the stored clauses,
// so that after an unsatisfiable result without assumptions compute_core() can collect the ids of
// the original clauses the refutation depends on.
//
// No restarts and no clause deletion: instances are small and solves are bounded by ticks.

#include <cstdint>
#include <vector>

namespace psat {

class Kitten {
 public:
  using KLit = uint32_t;
  static constexpr int kSat = 10, kUnsat = 20, kUnknown = 0;

  void clear();
  // Makes variables 0 .. n-1 available (keeps the existing ones).
  void resize(uint32_t n);
  uint32_t num_vars() const { return nvars_; }

  // An original clause (duplicate literals allowed, tautologies are skipped). Must be called at
  // decision level 0, i.e. before solve() or between solves.
  void add_clause(const KLit* lits, uint32_t size, uint32_t id = 0);
  void assume(KLit lit) { assumptions_.push_back(lit); }

  // Solves under the assumptions given since the last solve() (which are then cleared).
  int solve(uint64_t ticks_limit);
  int8_t value(KLit lit) const { return vals_[lit]; }  // after kSat: +1 / -1 (0: unassigned)

  // After kUnsat: the negations of the assumptions involved (empty: unsatisfiable without them).
  const std::vector<KLit>& final_clause() const { return final_; }
  bool inconsistent() const { return inconsistent_; }

  // Learned clauses in derivation order: learned(i) for i < num_learned().
  size_t num_learned() const { return learned_refs_.size(); }
  const KLit* learned_lits(size_t i) const { return &arena_[learned_refs_[i] + 2]; }
  uint32_t learned_size(size_t i) const { return arena_[learned_refs_[i]]; }

  uint64_t ticks() const { return ticks_; }

  // After an unsatisfiable result without assumptions (inconsistent()): the ids of the original
  // clauses in a refutation (an unsatisfiable subset, not necessarily minimal).
  void compute_core(std::vector<uint32_t>& ids);

 private:
  static constexpr uint32_t kNone = UINT32_MAX;
  static constexpr uint32_t kLearnedBit = 0x80000000u;
  static KLit neg(KLit l) { return l ^ 1u; }
  static uint32_t var(KLit l) { return l >> 1; }

  uint32_t level() const { return static_cast<uint32_t>(control_.size()); }
  uint32_t new_clause(const KLit* lits, uint32_t size, uint32_t aux, bool watch);
  void assign(KLit lit, uint32_t reason);
  bool propagate();  // false on conflict (conflict_ set)
  void backtrack(uint32_t lvl);
  void analyze();  // learns from conflict_, backjumps and asserts
  void analyze_final(KLit failed);
  bool decide();  // false when every variable is assigned
  void bump(uint32_t v);
  void heap_up(uint32_t i);
  void heap_down(uint32_t i);
  void heap_push(uint32_t v);
  uint32_t heap_pop();

  // Clause arena: [size, aux, lits...] with aux = the caller id (original clauses) or kLearnedBit |
  // learned index; watches hold arena offsets. Antecedents of learned clause i are
  // ante_[ante_begin_[i] .. ante_begin_[i + 1]).
  std::vector<uint32_t> arena_;
  std::vector<std::vector<uint32_t>> watches_;  // per literal
  std::vector<uint32_t> learned_refs_;
  std::vector<uint32_t> ante_, ante_begin_{0};
  uint32_t core_conflict_ = kNone;  // the clause falsified at the root
  std::vector<int8_t> vals_;      // per literal
  std::vector<int8_t> phase_;     // per variable
  std::vector<uint32_t> levels_;  // per variable
  std::vector<uint32_t> reasons_;  // per variable (arena offset or kNone)
  std::vector<uint8_t> seen_;     // per variable
  std::vector<double> score_;     // per variable
  std::vector<uint32_t> heap_, heap_pos_;  // max-heap on score_
  double inc_ = 1.0;
  std::vector<KLit> trail_;
  std::vector<uint32_t> control_;  // trail position of each decision level
  size_t propagated_ = 0;
  std::vector<KLit> assumptions_, final_, learned_;
  uint32_t conflict_ = kNone;
  bool inconsistent_ = false;
  uint64_t ticks_ = 0;
  uint32_t nvars_ = 0;
};

}  // namespace psat
