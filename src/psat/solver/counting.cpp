// Counting certificates (--counting): PR refutations of counting principles, before search.
//
// The pigeonhole principle, the parity principle (no perfect matching of an odd K_n) and Count^3
// (no partition of n points into triples, n not divisible by 3) need exponential resolution
// proofs, so CDCL with DRAT cannot refute them in reasonable time. They have polynomial PR proofs
// without new variables (Heule, Kiesl & Biere, CADE 2017; Buss & Thapen, LMCS 2021): symmetry
// arguments, each a binary PR clause whose witness swaps two pigeons / vertices / triples, followed
// by RUP units. This pass recognises such a system in the formula, checks every step on the clause
// database, adds the steps to the formula and to the proof (dpr-trim reads PR lines in both proof
// formats), and lets search go on; usually the last unit leaves the root inconsistent.
//
// Recognition (the whole formula is the structure; a sign map allows shuffled polarities):
// - every irredundant long clause (size >= 3) is an at-least-one constraint over "structure
//   literals": each variable occurs in long clauses with one polarity only, unassigned, and in
//   the same number q of them; every irredundant binary clause on a structure variable is
//   (-x v -y) over two structure literals (at-most-one);
// - q = 1, pigeonhole: the long clauses are pigeons; holes are the classes of variables joined by
//   binary clauses across pigeons; every pigeon has the same number k of variables in every hole,
//   variables of different pigeons in one hole exclude each other (and those of one pigeon in one
//   hole, if k > 1); more pigeons than holes. k = 1 is PHP (functional or not), k > 1 the clique
//   formulas on complete multipartite graphs. Pigeons that share no hole, directly or through
//   other pigeons, form independent systems (homer: two PHP 11 -> 10); the cheapest valid one
//   with more pigeons than holes is refuted;
// - q = 2, parity: the long clauses are vertices, a variable is the edge between its two clauses;
//   all pairs of n vertices, n odd, the edges at a vertex pairwise exclusive;
// - q = 3, Count^3: the long clauses are points, a variable is a triple; all triples of n points,
//   n not divisible by 3, the triples through a point pairwise exclusive.
// Otherwise (other clauses may share the structure's variables):
// - clique-colouring (clqcl): positions pick vertices (exactly-one clauses joined into vertex
//   classes by at-most-one clauses), edge literals from (-q[i][u] v -q[j][v] v e), colour clauses
//   of the vertices from (-e v -r[u][c] v -r[v][c]); more positions than colours;
// - relativized pigeonhole (rphp): n pigeons rest at r >= n places (pigeon clauses; a place hosts
//   at most one pigeon), a place in use (each of its pigeon literals implies its in-use literal)
//   maps to one of h < n holes (-in-use v holes), two places in use not to the same hole;
// - a pigeonhole system inside the formula (graph colouring with a clique larger than the number
//   of colours, ...): pigeons are long clauses of one size s whose literals exclude, hole by hole,
//   one literal of each other pigeon (k = 1); a greedy clique of such clauses in the s-core of
//   their graph, with s + 1 members.
//
// Proof plans (benchmarks/tools/counting_pr.py writes the same proofs offline):
// - pigeonhole, for m = holes .. 1, hole m-1 is reserved for pigeon m: PR clauses
//   (-p[i][m-1][a] v -p[m][x][b]) for i < m, x < m-1 with the witness "pigeons i and m swap":
//   {-p[i][m-1][a], p[i][x][b], p[m][m-1][a], -p[m][x][b]}; then the RUP units -p[i][m-1][a];
// - parity, while 3 or more vertices are left, the last vertex m is matched to the one before, q:
//   PR clauses (-e[m][u] v -e[q][w]) with the witness {-e[m][u], e[m][q], e[u][w], -e[q][w]} for
//   the other vertices u != w, the units -e[m][u], then e[m][q];
// - Count^3, while 4 or more points are left: first the triple of the last point m contains the
//   one before, q (PR clauses (-t(m,a,b) v -t(q,c,d)), witness {-t(m,a,b), t(m,q,b), t(a,c,d),
//   -t(q,c,d)}, units -t(m,a,b)), then the third one, r (the same with t(m,q,b) and r), then the
//   unit t(m,q,r);
// - clique-colouring (Buss & Thapen show PR refutations without new variables exist; this one is
//   a pigeonhole of positions into colours, "position i has colour c" being q[i][u] and r[u][c]
//   for some u, and only the positions are swapped, which every clause allows): for
//   c = m-1 .. 0, colour c reserved for position c+1, the PR clauses
//   (-q[i][u] v -r[u][c] v -q[c+1][v] v -r[v][x]) for i <= c, x < c, u != v, with the witness
//   "positions i and c+1 swap vertices" {-q[i][u], q[i][v], q[c+1][u], -q[c+1][v]}, then the RUP
//   lemmas (-q[i][u] v -r[u][c] v -q[c+1][v]) and (-q[i][u] v -r[u][c]); finally the units -q[0][u];
// - relativized pigeonhole with as many places as pigeons: first "pigeon m rests at place m"
//   (PR clauses (-p[i][m] v -p[m][x]), i, x < m, the witness swaps pigeons i and m; then the units
//   -p[i][m]), after which root propagation puts every pigeon at its place, so every place is in
//   use; then the places into the holes are a plain pigeonhole. With more places than pigeons,
//   the clique-colouring plan with the pigeons as positions, the places as vertices and the holes
//   as colours (its cost grows with the square of the places);
// - an embedded pigeonhole is refuted in isolation (counting_isolated): a separate solver on the
//   subsystem's clauses runs the pigeonhole plan; the proof then deletes every other clause (the
//   PR checks see the subsystem only, as in that solver, and do not visit the rest of the formula
//   for each step) and continues with its refutation. A subset of the clauses is unsatisfiable,
//   so is the formula;
// - a pigeonhole on a sparse graph, also in isolation, by elimination on the graph itself (see
//   Elimination below): a round lets one pigeon rest in one of its holes, after PR clauses that
//   swap it with the other pigeons of that hole; those get its other holes, with new variables
//   where they had none. The steps and the clauses a checker visits for each of them grow with
//   the fill of the elimination, not with pigeons times holes.
//
// Every PR clause C with witness w is checked before it is written. The negation of C is
// propagated at decision level 1 (assignment A); every clause D that w touches without satisfying
// it must have its restriction D|w implied: a literal of D|w is true under A, or propagating the
// negation of D|w at level 2 gives a conflict. Only the clauses with a literal whose negation is
// in w need the check: the binary watches and occurrence lists of the structure literals (learned
// clauses included: the checker has them too). A witness literal false at the root is refused
// (dpr-trim rejects it before its PR check). Units are checked by propagation (RUP). A failed
// check writes nothing and abandons the structure (the clauses added so far stay: each was
// checked). The clauses are only added: a model of the extended formula is a model of the
// original one, and no reconstruction is needed.
//
// Cost: where nothing is found, the detection only: one pass over the long clauses for the whole-
// formula structures (most formulas fail the polarity or multiplicity test within the first
// clauses), then the clique-colouring and embedded detections, each within a budget of a few
// passes over the clauses; the pass reads the clauses and watches without changing any solver
// state, so the search is the same as without the option. A structure whose estimated
// certification work exceeds --countingeffort is skipped.

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <iterator>
#include <memory>
#include <numeric>
#include <string>
#include <unordered_map>

#include "psat/core/options.hpp"
#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

constexpr int kPigeonhole = 1, kParity = 2, kCount3 = 3, kClique = 4, kRphp = 5, kElimination = 6;

uint64_t choose2(uint64_t n) { return n < 2 ? 0 : n * (n - 1) / 2; }
uint64_t choose3(uint64_t n) { return n < 3 ? 0 : n * (n - 1) * (n - 2) / 6; }

// Index of the triple {a, b, c} (distinct) in the combinatorial number system.
size_t triple_index(uint32_t a, uint32_t b, uint32_t c) {
  if (a > b) std::swap(a, b);
  if (b > c) std::swap(b, c);
  if (a > b) std::swap(a, b);
  return static_cast<size_t>(choose3(c) + choose2(b) + a);
}

// Refutation of a pigeonhole system on a sparse graph by elimination (the plan; the solver checks
// and writes its steps). A cell is a (pigeon, hole) pair with a variable; pigeons have at-least-one
// clauses over their cells, the cells of a hole exclude each other, and there are fewer holes than
// pigeons. A round picks a pigeon q and one of its holes h, and argues that q rests in h:
//  - every other pigeon i with a cell a in h gets a cell in each other hole j of q where it has
//    none: a new variable f, the clauses (-f v -u) for the cells u of j (RAT on -f, which no
//    clause contains yet), then f joins i's clause (the wider clause is implied; the narrow one is
//    deleted: a witness may satisfy the wide one by f alone);
//  - for i's cell a in h and q's cell b in j, the PR clause (-a v -b) with the witness "i and q
//    swap": {-a, i's cell in j, q's cell in h, -b};
//  - then -a by RUP for every such a (a pigeon in h leaves q no hole), q's cell in h as a unit (RAT:
//    every clause with its negation is satisfied), and the negations of q's other cells (RAT: the
//    only clause with them, q's, is satisfied).
// What is left is the system without q and h: one pigeon and one hole fewer, the pigeons of h with
// q's other holes instead. The pivot is the cell with the least (r - 1)(c - 1), r cells of its
// pigeon and c of its hole (Markowitz's rule of sparse Gaussian elimination: the number of PR
// clauses of the round, and a bound on its new variables). On a complete graph these are the
// rounds of the pigeonhole plan above; on a sparse one far fewer steps and clauses: the mutilated
// chessboard 16 x 16 (127 pigeons, 126 holes, 474 cells) takes 2,964 PR clauses and 723 new
// variables instead of the 666,750 and 15,528 of the pigeonhole formula on all pairs, and a
// proof checker visits every live clause for each step (dpr-trim: 0.2 s instead of hours).
// The plan keeps the root assignment that the solver's unit propagation gives after each unit (a
// pigeon with one cell left takes it, and the hole's other cells are false), so that its steps
// name unassigned variables only; it ends when a pigeon has no cell left (the solver's
// propagation then fails).
class Elimination {
 public:
  // Steps of a round, in a flat list: the code, then its operands (cells).
  //   kExclude f u: the new cell f excludes u; kWiden p n f1 .. fn: pigeon p's clause gets n new
  //   cells; kPr a b x q: (-a v -b) with the witness {-a, x, q, -b}; kUnit a: the RUP unit -a;
  //   kRat l: the RAT unit l (cell * 2 + negated).
  enum : uint32_t { kExclude, kWiden, kPr, kUnit, kRat };
  // Pigeon p has the cells [poff[p], poff[p + 1]); hole[c] is the hole of cell c.
  Elimination(uint32_t pigeons, uint32_t holes, const std::vector<uint32_t>& poff, const std::vector<uint32_t>& hole)
      : pig_(hole.size()), hole_(hole), state_(hole.size(), 0), role_(hole.size(), 0), rows_(pigeons), cols_(holes),
        rlive_(pigeons), clive_(holes, 0), rested_(pigeons, 0), at_(holes, kAbsent) {
    for (uint32_t p = 0; p < pigeons; ++p) {
      for (uint32_t c = poff[p]; c < poff[p + 1]; ++c) {
        pig_[c] = p;
        rows_[p].push_back(c);
        cols_[hole[c]].push_back(c);
        ++clive_[hole[c]];
      }
      rlive_[p] = poff[p + 1] - poff[p];
      live_.push_back(p);
    }
  }
  bool done() const { return conflict_ || finished_; }
  bool refuted() const { return conflict_; }
  uint32_t cells() const { return static_cast<uint32_t>(pig_.size()); }
  // Totals so far: PR clauses, units (RUP and RAT), other clauses, and the cells of the holes these
  // steps look at (for the work estimate); the plan's own work.
  uint64_t steps_pr = 0, steps_units = 0, steps_lemmas = 0, degree = 0, work = 0;

  void round(std::vector<uint32_t>& ops) {
    ops.clear();
    uint64_t best = UINT64_MAX;
    uint32_t vq = kAbsent;
    size_t keep = 0;
    for (const uint32_t p : live_) {
      if (rested_[p]) continue;
      live_[keep++] = p;
      if (!best) continue;
      compact(rows_[p]);
      const uint64_t r = rows_[p].size();
      for (const uint32_t v : rows_[p]) {
        const uint64_t key = (r - 1) * (clive_[hole_[v]] - 1);
        if (key < best) {
          best = key;
          vq = v;
        }
      }
    }
    live_.resize(keep);
    if (vq == kAbsent) {
      finished_ = true;  // (no pigeon left: not refuted)
      return;
    }
    const uint32_t q = pig_[vq], h = hole_[vq];
    compact(cols_[h]);
    compact(rows_[q]);
    others_.clear();
    rest_.clear();
    for (const uint32_t u : cols_[h]) {
      if (u != vq) others_.push_back(u);
    }
    for (const uint32_t v : rows_[q]) {
      if (v != vq) rest_.push_back(v);
    }
    if (!others_.empty() && !rest_.empty()) {
      for (const uint32_t a : others_) {
        const uint32_t i = pig_[a];
        compact(rows_[i]);
        for (const uint32_t v : rows_[i]) at_[hole_[v]] = v;
        added_.clear();
        for (const uint32_t b : rest_) {
          const uint32_t j = hole_[b];
          if (at_[j] != kAbsent) continue;
          const uint32_t f = cells();
          pig_.push_back(i);
          hole_.push_back(j);
          state_.push_back(0);
          role_.push_back(0);
          compact(cols_[j]);
          for (const uint32_t u : cols_[j]) {
            ops.push_back(kExclude);
            ops.push_back(f);
            ops.push_back(u);
          }
          steps_lemmas += cols_[j].size();
          degree += cols_[j].size() * (cols_[j].size() + 1) / 2;
          cols_[j].push_back(f);
          ++clive_[j];
          at_[j] = f;
          added_.push_back(f);
        }
        if (!added_.empty()) {
          ops.push_back(kWiden);
          ops.push_back(i);
          ops.push_back(static_cast<uint32_t>(added_.size()));
          ops.insert(ops.end(), added_.begin(), added_.end());
          rows_[i].insert(rows_[i].end(), added_.begin(), added_.end());
          rlive_[i] += static_cast<uint32_t>(added_.size());
          ++steps_lemmas;
        }
        for (const uint32_t b : rest_) {
          ops.push_back(kPr);
          ops.push_back(a);
          ops.push_back(b);
          ops.push_back(at_[hole_[b]]);
          ops.push_back(vq);
          degree += clive_[h] + clive_[hole_[b]];
        }
        steps_pr += rest_.size();
        for (const uint32_t v : rows_[i]) at_[hole_[v]] = kAbsent;
        work += rows_[i].size() + 4 * rest_.size();
      }
      // The units, with the round's PR clauses in the propagation (role 1: i's cell in h, 2: q's
      // cell elsewhere; every pair of the two kinds has a clause).
      for (const uint32_t a : others_) role_[a] = 1;
      for (const uint32_t b : rest_) role_[b] = 2;
      for (const uint32_t a : others_) {
        if (state_[a]) continue;
        ops.push_back(kUnit);
        ops.push_back(a);
        ++steps_units;
        degree += others_.size() + rest_.size();
        set_false(a);
        propagate();
        if (conflict_) break;
      }
      for (const uint32_t a : others_) role_[a] = 0;
      for (const uint32_t b : rest_) role_[b] = 0;
    }
    if (!conflict_ && !state_[vq]) {
      ops.push_back(kRat);
      ops.push_back(2 * vq);
      ++steps_units;
      degree += others_.size();
      set_true(vq);
      propagate();
    }
    if (!conflict_) {
      // Pigeons at rest (q, and those the propagation placed): their other cells are false.
      for (const uint32_t p : resting_) {
        for (const uint32_t v : rows_[p]) {
          if (state_[v]) continue;
          ops.push_back(kRat);
          ops.push_back(2 * v + 1);
          ++steps_units;
          degree += clive_[hole_[v]];
          state_[v] = 2;
          --clive_[hole_[v]];
          --rlive_[p];
        }
        work += rows_[p].size();
      }
    }
    resting_.clear();
  }

 private:
  static constexpr uint32_t kAbsent = UINT32_MAX;
  void compact(std::vector<uint32_t>& cells) {  // the unassigned ones stay
    size_t keep = 0;
    work += cells.size();
    for (const uint32_t c : cells) {
      if (!state_[c]) cells[keep++] = c;
    }
    cells.resize(keep);
  }
  void set_false(uint32_t v) {
    if (state_[v] == 2) return;
    if (state_[v] == 1) {
      conflict_ = true;
      return;
    }
    state_[v] = 2;
    --rlive_[pig_[v]];
    --clive_[hole_[v]];
    queue_.push_back(2 * v + 1);
  }
  void set_true(uint32_t v) {
    if (state_[v] == 1) return;
    if (state_[v] == 2) {
      conflict_ = true;
      return;
    }
    state_[v] = 1;
    --rlive_[pig_[v]];
    --clive_[hole_[v]];
    if (!rested_[pig_[v]]) {
      rested_[pig_[v]] = 1;
      resting_.push_back(pig_[v]);
    }
    queue_.push_back(2 * v);
  }
  // Unit propagation over the pigeon clauses, the exclusions and the round's PR clauses.
  void propagate() {
    while (!queue_.empty() && !conflict_) {
      const uint32_t x = queue_.back(), v = x >> 1;
      queue_.pop_back();
      if (!(x & 1)) {  // true: the hole's other cells are false
        const std::vector<uint32_t>& col = cols_[hole_[v]];
        for (size_t k = 0; k < col.size(); ++k) {
          if (!state_[col[k]]) set_false(col[k]);
        }
        work += col.size();
        if (role_[v] == 1) {
          for (const uint32_t b : rest_) set_false(b);
        } else if (role_[v] == 2) {
          for (const uint32_t a : others_) set_false(a);
        }
      } else {  // false: its pigeon may have one cell left, or none
        const uint32_t p = pig_[v];
        if (rested_[p]) continue;
        if (!rlive_[p]) {
          conflict_ = true;
        } else if (rlive_[p] == 1) {
          for (const uint32_t c : rows_[p]) {
            if (!state_[c]) {
              set_true(c);
              break;
            }
          }
          work += rows_[p].size();
        }
      }
    }
    queue_.clear();
  }

  std::vector<uint32_t> pig_, hole_;  // per cell
  std::vector<uint8_t> state_;        // per cell: 0 unassigned, 1 true, 2 false
  std::vector<uint8_t> role_;
  std::vector<std::vector<uint32_t>> rows_, cols_;  // cells of a pigeon / hole (the unassigned ones among them count)
  std::vector<uint32_t> rlive_, clive_;             // unassigned cells
  std::vector<uint8_t> rested_;                     // per pigeon: has a true cell
  std::vector<uint32_t> at_;                        // per hole: the cell of the pigeon at hand
  std::vector<uint32_t> live_, others_, rest_, added_, resting_, queue_;
  bool conflict_ = false, finished_ = false;
};

}  // namespace

// The structure a sparse pigeonhole is refuted on by elimination: the cells are the isolated
// solver's variables 0 .. hole.size() - 1, the plan's new cells the `fresh` variables after them.
struct Solver::CountingPlan {
  uint32_t pigeons = 0, holes = 0, fresh = 0;
  std::vector<uint32_t> poff, hole;
  uint64_t steps_pr = 0, steps_units = 0;
};

struct Solver::CountingState {
  int kind = 0;
  uint32_t pigeons = 0, holes = 0, k = 0;  // pigeonhole
  uint32_t n = 0;                          // vertices (parity) or points (Count^3)
  uint32_t systems = 1;                    // pigeonhole: independent systems (one refuted)
  std::vector<Lit> cell;                   // pigeonhole: cell[(i * holes + h) * k + j]
  std::vector<Lit> lit;                    // parity: lit[a * n + b]; Count^3: lit[triple_index]
  uint32_t positions = 0, vertices = 0, colours = 0;  // clique-colouring
  std::vector<Lit> pp, qq, used;           // relativized pigeonhole: pp[i * places + u], qq[u * holes + k], used[u]
  bool relativized = false;
  std::vector<Lit> q, r;                   // q[i * vertices + u] (position i at vertex u), r[u * colours + c]
  std::vector<Var> vars;                   // the structure variables
  std::vector<Var> extra_vars;             // other variables with occurrence lists
  bool embedded = false;                   // pigeonhole inside a larger formula: refuted in isolation
  // Pigeonhole on a sparse graph (embedded): cells without a variable hold kNoLit; the isolated
  // refutation gives them new variables. The system the violator was found in, for the report.
  bool sparse = false;
  uint32_t missing = 0, graph_pigeons = 0, graph_holes = 0;
  CountingPlan plan;                       // its refutation by elimination (counting_plan)
  // Virtual exclusions (at-most-one constraints over auxiliary variables), found by probing:
  // vlit[voff[x] .. voff[x + 1]) are literals that x falsifies by propagation.
  bool virt = false;
  std::vector<uint32_t> voff;
  std::vector<Lit> vlit;
  std::vector<uint32_t> longs;             // embedded: the pigeon clauses
  uint64_t degree_sum = 0, long_sum = 0;   // for the cost estimate (over all structure variables)
  uint64_t all_vars = 0;
  uint64_t steps_pr = 0, steps_units = 0;  // planned
  uint64_t steps_tried = 0;                // PR steps checked so far (--countingfault)
  // Certification.
  std::vector<uint32_t> slot;              // per variable: index of a structure variable, or none
  std::vector<std::vector<uint32_t>> occ;  // per structure literal: long clauses (learned too)
  std::vector<uint8_t> mark;               // per literal: 1 in the witness, 2 in a checked clause
  std::vector<Lit> others, rest;
  uint64_t work = 0, limit = 0, ticks0 = 0;
  const char* failure = nullptr;
  // Proof clean-up after each round (counting_certify): the round's clauses of three or more
  // literals (size, then the literals), the trail position where the round's units start, and
  // per literal: its satisfied clauses are dropped from the proof already.
  std::vector<Lit> round;
  size_t round_trail = 0;
  std::vector<uint8_t> dropped;
  // Clauses the plan does not need, deleted from the proof before it if it refutes the formula
  // (whole-formula pigeonhole): flat (size, literals), and the number of such copies per clause
  // hash (end_round leaves that many copies of a clause alone).
  std::vector<Lit> upfront;
  std::unordered_map<uint64_t, uint32_t> upfront_copies;
  static uint64_t key(const Lit* lits, uint32_t size) {
    uint64_t h = size;
    for (uint32_t i = 0; i < size; ++i) {
      uint64_t x = lits[i] + 0x9e3779b97f4a7c15ULL;
      x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
      x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
      h += x ^ (x >> 31);
    }
    return h;
  }
  // One copy of the clause is deleted up front (and no longer counted as such).
  bool take_upfront(const Lit* lits, uint32_t size) {
    if (upfront_copies.empty()) return false;
    const auto it = upfront_copies.find(key(lits, size));
    if (it == upfront_copies.end() || !it->second) return false;
    --it->second;
    return true;
  }

  std::vector<uint32_t>* occ_of(Lit l) {
    const uint32_t i = slot[var_of(l)];
    return i == UINT32_MAX ? nullptr : &occ[2 * size_t{i} + (l & 1)];
  }
  Lit e(uint32_t a, uint32_t b) const { return lit[size_t{a} * n + b]; }
  Lit t(uint32_t a, uint32_t b, uint32_t c) const { return lit[triple_index(a, b, c)]; }
};

bool Solver::counting_detect(CountingState& st) {
  const size_t nv = num_vars_;
  std::vector<int8_t> sign(nv, 0);  // the polarity of the variable in the long clauses
  std::vector<uint8_t> mult(nv, 0);
  std::vector<uint32_t> longs;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    st.work += c.size / 4 + 1;
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit l = c.lits()[k];
      if (vals_[l]) return false;
      const Var v = var_of(l);
      const int8_t s = is_negative(l) ? -1 : 1;
      if (!sign[v]) {
        sign[v] = s;
      } else if (sign[v] != s) {
        return false;
      }
      if (mult[v] == 3) return false;
      ++mult[v];
    }
    longs.push_back(ref);
  }
  if (longs.size() < 3) return false;
  uint32_t q = 0;
  for (Var v = 0; v < nv; ++v) {
    if (!mult[v]) continue;
    if (!q) q = mult[v];
    if (mult[v] != q) return false;
    st.vars.push_back(v);
  }
  st.work += nv / 16;
  auto slit = [&sign](Var v) { return make_lit(v, sign[v] < 0); };  // the structure literal
  // Binary clauses on structure variables: (-x v -y) over structure literals only.
  for (const Var v : st.vars) {
    const Lit x = slit(v);
    for (const Watch& w : watches_[x]) {
      if (w.binary() && !w.redundant_binary()) return false;
    }
    for (const Watch& w : watches_[negate(x)]) {
      if (!w.binary() || w.redundant_binary()) continue;
      const Var u = var_of(w.blit);
      if (!mult[u] || w.blit != negate(slit(u))) return false;
      ++st.degree_sum;
    }
    st.work += (watches_[x].size() + watches_[negate(x)].size()) / 4 + 1;
  }
  // The long clause(s) of each structure variable.
  std::vector<uint32_t> owner(nv * q, UINT32_MAX);
  for (uint32_t i = 0; i < longs.size(); ++i) {
    const Clause& c = clause(longs[i]);
    st.long_sum += uint64_t{c.size} * c.size;
    for (uint32_t k = 0; k < c.size; ++k) {
      uint32_t* o = &owner[size_t{var_of(c.lits()[k])} * q];
      while (*o != UINT32_MAX) ++o;
      *o = i;
    }
  }
  const auto nlong = static_cast<uint32_t>(longs.size());
  const uint64_t nvars = st.vars.size();
  st.all_vars = nvars;
  // Distinct conflict-graph neighbours of a structure variable (duplicate binaries counted once).
  std::vector<uint32_t> stamp(nv, 0);
  uint32_t now = 0;
  auto neighbours = [&](Var v, auto&& visit) -> bool {
    ++now;
    for (const Watch& w : watches_[negate(slit(v))]) {
      if (!w.binary() || w.redundant_binary()) continue;
      const Var u = var_of(w.blit);
      if (stamp[u] == now) continue;
      stamp[u] = now;
      if (!visit(u)) return false;
    }
    st.work += watches_[negate(slit(v))].size() / 4 + 1;
    return true;
  };

  if (q == 1) {
    // Holes: classes of variables joined by binary clauses across pigeons.
    std::vector<uint32_t> parent(nv);
    std::iota(parent.begin(), parent.end(), 0u);
    auto find = [](std::vector<uint32_t>& up, uint32_t v) {
      while (up[v] != v) v = up[v] = up[up[v]];
      return v;
    };
    for (const Var v : st.vars) {
      for (const Watch& w : watches_[negate(slit(v))]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const Var u = var_of(w.blit);
        if (owner[u] != owner[v]) parent[find(parent, u)] = find(parent, v);
      }
    }
    std::vector<uint32_t> hole(nv, UINT32_MAX);
    uint32_t holes = 0;
    for (const Var v : st.vars) {
      const uint32_t r = find(parent, v);
      if (hole[r] == UINT32_MAX) hole[r] = holes++;
      hole[v] = hole[r];
    }
    // Systems: pigeons joined through shared holes. Each is checked on its own (homer: two
    // disjoint PHP 11 -> 10), and the cheapest unsatisfiable one is refuted: the witnesses of
    // one system touch no clause of another.
    std::vector<uint32_t> up(nlong), hole_pigeon(holes, UINT32_MAX);
    std::iota(up.begin(), up.end(), 0u);
    for (const Var v : st.vars) {
      uint32_t& hp = hole_pigeon[hole[v]];
      if (hp == UINT32_MAX) {
        hp = owner[v];
      } else {
        up[find(up, owner[v])] = find(up, hp);
      }
    }
    struct System {
      uint32_t pigeons = 0, holes = 0, k = 0;
      uint64_t vars = 0, steps_pr = 0;
      size_t base = 0, pair_base = 0;  // first literal slot, first (pigeon, hole) pair
      bool ok = true;
    };
    std::vector<System> sys;
    std::vector<uint32_t> sys_of(nlong, UINT32_MAX), local_pigeon(nlong), local_hole(holes);
    for (uint32_t p = 0; p < nlong; ++p) {
      const uint32_t r = find(up, p);
      if (sys_of[r] == UINT32_MAX) {
        sys_of[r] = static_cast<uint32_t>(sys.size());
        sys.emplace_back();
      }
      sys_of[p] = sys_of[r];
      local_pigeon[p] = sys[sys_of[p]].pigeons++;
    }
    for (uint32_t h = 0; h < holes; ++h) local_hole[h] = sys[sys_of[hole_pigeon[h]]].holes++;
    for (const Var v : st.vars) ++sys[sys_of[owner[v]]].vars;
    size_t slots = 0, pairs_total = 0;
    for (System& y : sys) {
      const uint64_t pairs = uint64_t{y.pigeons} * y.holes;
      if (y.pigeons <= y.holes || pairs > y.vars || y.vars % pairs) {
        y.ok = false;
        continue;
      }
      y.k = static_cast<uint32_t>(y.vars / pairs);
      y.base = slots;
      y.pair_base = pairs_total;
      slots += pairs * y.k;
      pairs_total += pairs;
      for (uint64_t m = 1; m <= y.holes; ++m) y.steps_pr += m * (m - 1) * y.k * y.k;
    }
    if (!slots) return false;
    // Cells (ascending variables: sorted); every pigeon of a system has k variables in each hole.
    std::vector<uint32_t> fill(pairs_total, 0);
    st.cell.assign(slots, kNoLit);
    for (const Var v : st.vars) {
      System& y = sys[sys_of[owner[v]]];
      if (!y.ok) continue;
      const size_t pair = size_t{local_pigeon[owner[v]]} * y.holes + local_hole[hole[v]];
      uint32_t& f = fill[y.pair_base + pair];
      if (f == y.k) {
        y.ok = false;
        continue;
      }
      st.cell[y.base + pair * y.k + f++] = slit(v);
    }
    // Variables of different pigeons in one hole exclude each other; with k > 1 also those of
    // one pigeon in one hole.
    for (const Var v : st.vars) {
      System& y = sys[sys_of[owner[v]]];
      if (!y.ok) continue;
      uint64_t cross = 0, within = 0;
      neighbours(v, [&](Var u) {
        if (hole[u] == hole[v]) {
          if (owner[u] != owner[v]) {
            ++cross;
          } else {
            ++within;
          }
        }
        return true;
      });
      if (cross != uint64_t{y.pigeons - 1} * y.k || within != y.k - 1) y.ok = false;
    }
    size_t best = sys.size();
    for (size_t i = 0; i < sys.size(); ++i) {
      if (sys[i].ok && (best == sys.size() || sys[i].steps_pr < sys[best].steps_pr)) best = i;
    }
    if (best == sys.size()) return false;
    const System& y = sys[best];
    st.cell.erase(st.cell.begin() + static_cast<std::ptrdiff_t>(y.base + uint64_t{y.pigeons} * y.holes * y.k),
                  st.cell.end());
    st.cell.erase(st.cell.begin(), st.cell.begin() + static_cast<std::ptrdiff_t>(y.base));
    std::vector<Var> vars;
    for (const Var v : st.vars) {
      if (sys_of[owner[v]] == best) vars.push_back(v);
    }
    st.vars.swap(vars);
    st.kind = kPigeonhole;
    st.pigeons = y.pigeons;
    st.holes = y.holes;
    st.k = y.k;
    st.steps_pr = y.steps_pr;
    for (uint64_t m = 1; m <= y.holes; ++m) st.steps_units += m * y.k;
    st.systems = static_cast<uint32_t>(sys.size());
    return true;
  }

  const uint32_t n = nlong;
  auto shares = [&](Var u, Var v) {
    for (uint32_t a = 0; a < q; ++a) {
      for (uint32_t b = 0; b < q; ++b) {
        if (owner[size_t{u} * q + a] == owner[size_t{v} * q + b]) return true;
      }
    }
    return false;
  };
  uint64_t expected_degree = 0;
  if (q == 2) {
    if (n % 2 == 0 || nvars != choose2(n)) return false;
    st.lit.assign(size_t{n} * n, kNoLit);
    for (const Var v : st.vars) {
      const uint32_t a = owner[2 * size_t{v}], b = owner[2 * size_t{v} + 1];
      if (st.lit[size_t{a} * n + b] != kNoLit) return false;
      st.lit[size_t{a} * n + b] = st.lit[size_t{b} * n + a] = slit(v);
    }
    expected_degree = 2 * (uint64_t{n} - 2);
  } else {
    if (n % 3 == 0 || nvars != choose3(n)) return false;
    st.lit.assign(choose3(n), kNoLit);
    for (const Var v : st.vars) {
      const uint32_t* o = &owner[3 * size_t{v}];
      const size_t i = triple_index(o[0], o[1], o[2]);
      if (st.lit[i] != kNoLit) return false;
      st.lit[i] = slit(v);
    }
    expected_degree = choose3(n) - choose3(n - 3) - 1;
  }
  // Each constraint is exactly-one: the variables sharing a constraint exclude each other, and
  // no other binary clauses.
  for (const Var v : st.vars) {
    uint64_t degree = 0;
    const bool ok = neighbours(v, [&](Var u) {
      ++degree;
      return shares(u, v);
    });
    if (!ok || degree != expected_degree) return false;
  }
  st.kind = q == 2 ? kParity : kCount3;
  st.n = n;
  if (q == 2) {
    for (uint64_t r = n - 2;; r -= 2) {
      st.steps_pr += r * (r - 1);
      st.steps_units += r + 1;
      if (r < 3) break;
    }
  } else {
    for (uint64_t v = n; v >= 4; v -= 3) {
      st.steps_pr += choose2(v - 2) * choose2(v - 4) + (v - 3) * choose2(v - 4);
      st.steps_units += choose2(v - 2) + (v - 3) + 1;
    }
  }
  return true;
}

// Clique-colouring (clqcl): a graph with a k-clique that is m-colourable, k > m. Positions i < k
// each pick a vertex u (q[i][u], exactly-one per position; a vertex fills at most one position),
// two positions take adjacent vertices ((-q[i][u] v -q[j][v] v e[u][v]) for i != j, u != v),
// every vertex has a colour (r[u][c], exactly-one per vertex), and adjacent vertices differ
// ((-e[u][v] v -r[u][c] v -r[v][c])). Recognised from the clauses, whatever else the formula
// contains; the PR checks decide whether the proof plan goes through.
bool Solver::counting_detect_clique(CountingState& st) {
  const size_t nv = num_vars_, nl = 2 * nv;
  const uint64_t cap = st.work + 2 * (arena_.size() + 2 * binaries_irredundant_) + 2'000'000;
  constexpr uint32_t kNone = UINT32_MAX, kMulti = UINT32_MAX - 1;
  // 1. Exactly-one long clauses: literals pairwise exclusive through binary clauses (-x v -y).
  std::vector<uint32_t> stamp(nl, 0), owner(nl, kNone), eo;
  uint32_t now = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    if (++st.work > cap) return false;
    const Lit* lits = c.lits();
    bool ok = true;
    for (uint32_t k = 0; k < c.size && ok; ++k) ok = !vals_[lits[k]] && watches_[negate(lits[k])].size() + 1 >= c.size;
    if (!ok) continue;
    ++now;
    for (uint32_t k = 0; k < c.size; ++k) stamp[lits[k]] = now;
    for (uint32_t k = 0; k < c.size && ok; ++k) {
      uint32_t cnt = 0;
      for (const Watch& w : watches_[negate(lits[k])]) {
        cnt += w.binary() && !w.redundant_binary() && stamp[negate(w.blit)] == now;
      }
      st.work += watches_[negate(lits[k])].size() / 4 + 1;
      ok = cnt + 1 >= c.size;
    }
    if (!ok) continue;
    const auto idx = static_cast<uint32_t>(eo.size());
    eo.push_back(ref);
    for (uint32_t k = 0; k < c.size; ++k) owner[lits[k]] = owner[lits[k]] == kNone ? idx : kMulti;
  }
  if (eo.size() < 4 || st.work > cap) return false;
  // 2. Vertices: classes of literals of different exactly-one clauses joined by binary clauses;
  //    a position system: exactly-one clauses joined through classes, each with one literal per
  //    class.
  std::vector<uint32_t> up(nl);
  std::iota(up.begin(), up.end(), 0u);
  auto find = [](std::vector<uint32_t>& u, uint32_t x) {
    while (u[x] != x) x = u[x] = u[u[x]];
    return x;
  };
  for (uint32_t idx = 0; idx < eo.size(); ++idx) {
    const Clause& c = clause(eo[idx]);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (owner[x] != idx) continue;
      for (const Watch& w : watches_[negate(x)]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const Lit y = negate(w.blit);
        if (owner[y] < kMulti && owner[y] != idx) up[find(up, x)] = find(up, y);
      }
      st.work += watches_[negate(x)].size() / 4 + 1;
    }
  }
  if (st.work > cap) return false;
  std::vector<uint32_t> cup(eo.size()), first_clause(nl, kNone);
  std::iota(cup.begin(), cup.end(), 0u);
  for (uint32_t idx = 0; idx < eo.size(); ++idx) {
    const Clause& c = clause(eo[idx]);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (owner[x] != idx) continue;
      const uint32_t r = find(up, x);
      if (first_clause[r] == kNone) {
        first_clause[r] = idx;
      } else {
        cup[find(cup, idx)] = find(cup, first_clause[r]);
      }
    }
  }
  // The largest system of three or more clauses is the candidate position system.
  std::vector<uint32_t> members(eo.size(), 0);
  for (uint32_t idx = 0; idx < eo.size(); ++idx) ++members[find(cup, idx)];
  uint32_t best = kNone;
  for (uint32_t idx = 0; idx < eo.size(); ++idx) {
    if (members[idx] >= 3 && (best == kNone || members[idx] > members[best])) best = idx;
  }
  if (best == kNone) return false;
  std::vector<uint32_t> pos_clauses;
  for (uint32_t idx = 0; idx < eo.size(); ++idx) {
    if (find(cup, idx) == best) pos_clauses.push_back(idx);
  }
  const auto k = static_cast<uint32_t>(pos_clauses.size());
  const uint32_t n = clause(eo[pos_clauses[0]]).size;
  std::vector<uint32_t> vertex_of_root(nl, kNone), position(eo.size(), kNone);
  std::vector<uint32_t> qpos(nl, kNone);  // literal -> i * n + u for the q literals
  uint32_t vertices = 0;
  st.q.assign(size_t{k} * n, kNoLit);
  for (uint32_t i = 0; i < k; ++i) {
    const Clause& c = clause(eo[pos_clauses[i]]);
    if (c.size != n) return false;
    position[pos_clauses[i]] = i;
    for (uint32_t j = 0; j < c.size; ++j) {
      const Lit x = c.lits()[j];
      if (owner[x] != pos_clauses[i]) return false;
      const uint32_t r = find(up, x);
      if (vertex_of_root[r] == kNone) {
        if (vertices == n) return false;
        vertex_of_root[r] = vertices++;
      }
      const uint32_t u = vertex_of_root[r];
      if (st.q[size_t{i} * n + u] != kNoLit) return false;
      st.q[size_t{i} * n + u] = x;
      qpos[x] = i * n + u;
    }
  }
  if (vertices != n) return false;
  // A vertex fills at most one position: the literals of one class exclude each other.
  for (uint32_t i = 0; i < k; ++i) {
    for (uint32_t u = 0; u < n; ++u) {
      const Lit x = st.q[size_t{i} * n + u];
      ++now;
      for (uint32_t j = 0; j < k; ++j) stamp[st.q[size_t{j} * n + u]] = now;
      uint32_t cnt = 0;
      for (const Watch& w : watches_[negate(x)]) {
        if (w.binary() && !w.redundant_binary() && stamp[negate(w.blit)] == now) {
          stamp[negate(w.blit)] = 0;
          ++cnt;
        }
      }
      if (cnt != k - 1) return false;
    }
  }
  // 3. Edges: (-q[i][u] v -q[j][v] v e) gives the edge literal e of {u, v}; then the colour
  //    clauses (-e v -a v -b): a and b in the colour clauses of u and v, of the same colour.
  std::vector<Lit> edge(size_t{n} * n, kNoLit);
  std::vector<uint32_t> edge_of(nl, kNone);  // edge literal -> u * n + v (u < v)
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size != 3) continue;
    if (++st.work > cap) return false;
    uint32_t qs[3], nq = 0;
    Lit other = kNoLit;
    for (uint32_t j = 0; j < 3; ++j) {
      const uint32_t qp = qpos[negate(c.lits()[j])];
      if (qp != kNone) {
        qs[nq++] = qp;
      } else {
        other = c.lits()[j];
      }
    }
    if (nq != 2 || other == kNoLit || qpos[other] != kNone || qpos[negate(other)] != kNone) continue;
    uint32_t u = qs[0] % n, v = qs[1] % n;
    if (qs[0] / n == qs[1] / n || u == v) continue;
    if (u > v) std::swap(u, v);
    Lit& e = edge[size_t{u} * n + v];
    if (e == kNoLit) {
      if (edge_of[other] != kNone) return false;
      e = other;
      edge_of[other] = u * n + v;
    } else if (e != other) {
      return false;
    }
    st.long_sum += 3;
  }
  // Colour clauses: exactly-one clauses outside the position system.
  std::vector<uint32_t> cu(nl);
  std::iota(cu.begin(), cu.end(), 0u);
  std::vector<std::pair<uint64_t, uint32_t>> votes;  // (vertex, colour clause) per colour clause occurrence
  std::vector<uint32_t> records(n, 0);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size != 3) continue;
    if (++st.work > cap) return false;
    uint32_t ei = kNone;
    Lit ab[3];
    uint32_t nab = 0;
    for (uint32_t j = 0; j < 3; ++j) {
      const Lit y = negate(c.lits()[j]);
      if (edge_of[y] != kNone && ei == kNone) {
        ei = edge_of[y];
      } else {
        ab[nab++] = y;
      }
    }
    if (ei == kNone || nab != 2) continue;
    const uint32_t ca = owner[ab[0]], cb = owner[ab[1]];
    if (ca >= kMulti || cb >= kMulti || position[ca] != kNone || position[cb] != kNone || ca == cb) continue;
    const uint32_t u = ei / n, v = ei % n;
    for (const uint32_t w : {u, v}) {
      votes.emplace_back(uint64_t{w} << 32 | ca, 1);
      votes.emplace_back(uint64_t{w} << 32 | cb, 1);
      ++records[w];
    }
    cu[find(cu, ab[0])] = find(cu, ab[1]);
  }
  if (votes.empty()) return false;
  std::sort(votes.begin(), votes.end());
  // The colour clause of vertex u: the one in every colour clause on an edge of u.
  std::vector<uint32_t> colour_clause(n, kNone), clause_vertex(eo.size(), kNone);
  for (size_t i = 0; i < votes.size();) {
    size_t j = i;
    while (j < votes.size() && votes[j].first == votes[i].first) ++j;
    const auto u = static_cast<uint32_t>(votes[i].first >> 32), cl = static_cast<uint32_t>(votes[i].first);
    if (j - i == records[u]) {
      if (colour_clause[u] != kNone || clause_vertex[cl] != kNone) return false;
      colour_clause[u] = cl;
      clause_vertex[cl] = u;
    }
    i = j;
  }
  // Colours: classes of colour literals joined by the colour clauses (one literal per class).
  std::vector<uint32_t> colour_of_root(nl, kNone);
  uint32_t colours = 0;
  for (uint32_t u = 0; u < n; ++u) {
    if (colour_clause[u] == kNone) return false;
    const Clause& c = clause(eo[colour_clause[u]]);
    if (u == 0) {
      colours = c.size;
      st.r.assign(size_t{n} * colours, kNoLit);
    }
    if (c.size != colours) return false;
    for (uint32_t j = 0; j < c.size; ++j) {
      const Lit a = c.lits()[j];
      const uint32_t r = find(cu, a);
      if (u == 0) {
        if (colour_of_root[r] != kNone) return false;
        colour_of_root[r] = j;
      }
      const uint32_t col = colour_of_root[r];
      if (col == kNone || st.r[size_t{u} * colours + col] != kNoLit) return false;
      st.r[size_t{u} * colours + col] = a;
    }
  }
  if (k <= colours) return false;
  st.kind = kClique;
  st.positions = k;
  st.vertices = n;
  st.colours = colours;
  st.vars.clear();
  for (const Lit x : st.q) st.vars.push_back(var_of(x));
  for (const Lit x : st.r) st.vars.push_back(var_of(x));
  std::sort(st.vars.begin(), st.vars.end());
  if (std::adjacent_find(st.vars.begin(), st.vars.end()) != st.vars.end()) return false;
  // (The edges get occurrence lists too: the clauses that imply a checked one are found there.)
  for (const Lit e : edge) {
    if (e != kNoLit) st.extra_vars.push_back(var_of(e));
  }
  st.all_vars = st.q.size();
  for (const Lit x : st.q) {
    st.degree_sum += watches_[negate(x)].size();
    st.long_sum += n;
  }
  const uint64_t pairs = uint64_t{n} * (n - 1);
  for (uint64_t lvl = 1; lvl <= colours; ++lvl) {
    st.steps_pr += lvl * (lvl - 1) * pairs;
    st.steps_units += lvl * (pairs + n);
  }
  st.steps_units += n;
  return true;
}

// Pigeonhole systems inside a larger formula (graph colouring with a clique larger than the number
// of colours, ...). Pigeons are long clauses of one size s whose literals exclude, hole by hole,
// one literal of every other pigeon (k = 1). From a seed clause P0: a clause Q is aligned if each
// of its literals excludes exactly one literal of P0 (its hole) and the holes are a permutation;
// then a greedy clique of aligned clauses whose same-hole literals exclude each other. More
// pigeons than holes: the subsystem is unsatisfiable, whatever else the formula says; it is
// refuted on its own (counting_isolated).
bool Solver::counting_detect_embedded(CountingState& st) {
  const size_t nv = num_vars_, nl = 2 * nv;
  // Budget: four passes over the clauses; one with virtual exclusions (after probing).
  const uint64_t passes = st.virt ? 1 : 4;
  const uint64_t cap = st.work + passes * (arena_.size() + 2 * binaries_irredundant_) + (st.virt ? 2'000'000 : 8'000'000);
  // The literals x excludes: binary clauses (-x v -y), and the virtual exclusions if any.
  auto virtual_count = [&st](Lit x) -> size_t { return st.virt ? st.voff[x + 1] - st.voff[x] : 0; };
  // (charge: count the scan as work; the adjacency pass counts the occurrences it visits instead)
  auto exclusions = [&](Lit x, bool charge, auto&& visit) {
    for (const Watch& w : watches_[negate(x)]) {
      if (w.binary() && !w.redundant_binary()) visit(negate(w.blit));
    }
    if (st.virt) {
      for (uint32_t i = st.voff[x]; i < st.voff[x + 1]; ++i) visit(st.vlit[i]);
    }
    if (charge) st.work += (watches_[negate(x)].size() + virtual_count(x)) / 4 + 1;
  };
  // Candidate pigeons: long clauses whose literals each exclude at least s other literals.
  std::vector<uint32_t> cand;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    if (++st.work > cap) return false;
    const Lit* lits = c.lits();
    bool ok = true;
    for (uint32_t k = 0; k < c.size && ok; ++k) {
      ok = !vals_[lits[k]] && watches_[negate(lits[k])].size() + virtual_count(lits[k]) >= c.size;
    }
    if (!ok) continue;
    for (uint32_t k = 0; k < c.size && ok; ++k) {
      uint32_t cnt = 0;
      exclusions(lits[k], true, [&cnt](Lit) { ++cnt; });
      ok = cnt >= c.size;
    }
    if (!ok) continue;
    cand.push_back(ref);
  }
  if (cand.size() < 4 || st.work > cap) return false;
  // Literal -> candidate clauses.
  std::vector<uint32_t> off(nl + 1, 0);
  for (const uint32_t ref : cand) {
    const Clause& c = clause(ref);
    for (uint32_t k = 0; k < c.size; ++k) ++off[c.lits()[k] + 1];
  }
  for (size_t l = 0; l < nl; ++l) off[l + 1] += off[l];
  std::vector<uint32_t> occ(off[nl]);
  {
    std::vector<uint32_t> pos(off.begin(), off.end() - 1);
    for (uint32_t i = 0; i < cand.size(); ++i) {
      const Clause& c = clause(cand[i]);
      for (uint32_t k = 0; k < c.size; ++k) occ[pos[c.lits()[k]]++] = i;
    }
  }
  st.work += occ.size();
  // Clause graph: candidates of one size joined by a binary clause between their literals. A
  // pigeon of an s + 1 clique has s neighbours: the s-core (clauses with s neighbours among the
  // remaining ones, repeatedly) keeps every such clique, and usually little else.
  std::vector<std::vector<uint32_t>> adj(cand.size());
  std::vector<uint32_t> qstamp(cand.size(), 0);
  uint32_t now = 0;
  for (uint32_t i = 0; i < cand.size(); ++i) {
    if (st.work > cap) return false;
    const Clause& c = clause(cand[i]);
    qstamp[i] = ++now;
    const uint32_t size = c.size;
    for (uint32_t k = 0; k < size; ++k) {
      exclusions(clause(cand[i]).lits()[k], false, [&](Lit y) {
        for (uint32_t t = off[y]; t < off[y + 1]; ++t) {
          if (qstamp[occ[t]] == now || clause(cand[occ[t]]).size != size) continue;
          qstamp[occ[t]] = now;
          adj[i].push_back(occ[t]);
        }
        st.work += off[y + 1] - off[y] + 1;
      });
    }
  }
  std::vector<uint32_t> degree(cand.size()), queue;
  std::vector<uint8_t> alive(cand.size(), 1);
  for (uint32_t i = 0; i < cand.size(); ++i) {
    degree[i] = static_cast<uint32_t>(adj[i].size());
    if (degree[i] < clause(cand[i]).size) queue.push_back(i);
  }
  while (!queue.empty()) {
    const uint32_t i = queue.back();
    queue.pop_back();
    if (!alive[i]) continue;
    alive[i] = 0;
    for (const uint32_t t : adj[i]) {
      if (alive[t] && degree[t]-- == clause(cand[t]).size) queue.push_back(t);
    }
    st.work += adj[i].size() + 1;
  }
  std::vector<uint32_t> order;
  for (uint32_t i = 0; i < cand.size(); ++i) {
    if (alive[i]) order.push_back(i);
  }
  if (order.size() < 4) return false;
  std::stable_sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) { return degree[a] > degree[b]; });
  std::vector<uint32_t> tstamp(nl, 0), tlab(nl, 0), vstamp(nv, 0);
  uint32_t tnow = 0;
  std::vector<uint32_t> nbrs, rowref, chosen, pool, next;
  std::vector<std::vector<Lit>> rows;
  std::vector<uint8_t> compat;
  constexpr size_t kMaxRows = 512;
  for (const uint32_t si : order) {
    if (st.work > cap) return false;
    const uint32_t s = clause(cand[si]).size;
    ++now;
    rows.assign(1, std::vector<Lit>(clause(cand[si]).lits(), clause(cand[si]).lits() + s));
    rowref.assign(1, cand[si]);
    for (uint32_t j = 0; j < s; ++j) vstamp[var_of(rows[0][j])] = now;
    nbrs.clear();
    for (const uint32_t t : adj[si]) {
      if (alive[t]) nbrs.push_back(t);
    }
    if (nbrs.size() < s) continue;
    // Aligned clauses: each literal excludes exactly one seed literal, the holes a permutation.
    // (Tags: the literals a seed literal excludes, with its hole; kAmbiguous if two do.)
    constexpr uint32_t kAmbiguous = UINT32_MAX;
    ++tnow;
    for (uint32_t j = 0; j < s; ++j) {
      exclusions(rows[0][j], true, [&](Lit y) {
        if (tstamp[y] == tnow) {
          if (tlab[y] != j) tlab[y] = kAmbiguous;
        } else {
          tstamp[y] = tnow;
          tlab[y] = j;
        }
      });
    }
    for (const uint32_t t : nbrs) {
      if (rows.size() >= kMaxRows) break;
      const Clause& q = clause(cand[t]);
      if (q.size != s) continue;
      std::vector<Lit> row(s, kNoLit);
      bool ok = true;
      for (uint32_t k = 0; k < s && ok; ++k) {
        const Lit x = q.lits()[k];
        ok = vstamp[var_of(x)] != now && tstamp[x] == tnow && tlab[x] != kAmbiguous && row[tlab[x]] == kNoLit;
        if (ok) row[tlab[x]] = x;
      }
      st.work += s / 4 + 1;
      if (!ok) continue;
      rows.push_back(std::move(row));
      rowref.push_back(cand[t]);
    }
    if (rows.size() <= s) continue;
    // Compatibility: the same-hole literals of two rows exclude each other.
    const size_t n = rows.size();
    compat.assign(n * n, 0);
    for (size_t a = 0; a < n; ++a) {
      ++tnow;
      for (uint32_t h = 0; h < s; ++h) {
        exclusions(rows[a][h], true, [&](Lit y) {
          tstamp[y] = tnow;
          tlab[y] = h;
        });
      }
      for (size_t b = a + 1; b < n; ++b) {
        bool ok = true;
        for (uint32_t h = 0; h < s && ok; ++h) ok = tstamp[rows[b][h]] == tnow && tlab[rows[b][h]] == h;
        compat[a * n + b] = compat[b * n + a] = ok;
      }
      st.work += n * s / 4 + 1;
    }
    if (st.work > cap) return false;
    // Greedy clique from the seed: each time the candidate compatible with most of the others.
    chosen.assign(1, 0);
    pool.clear();
    for (uint32_t b = 1; b < n; ++b) {
      if (compat[b]) pool.push_back(b);
    }
    ++now;
    for (const Lit x : rows[0]) vstamp[var_of(x)] = now;
    while (!pool.empty() && chosen.size() <= s) {
      uint32_t best = UINT32_MAX;
      size_t best_deg = 0;
      for (const uint32_t c : pool) {
        size_t deg = 0;
        for (const uint32_t d : pool) deg += compat[size_t{c} * n + d];
        if (best == UINT32_MAX || deg > best_deg) {
          best = c;
          best_deg = deg;
        }
      }
      st.work += pool.size() * pool.size() / 8 + 1;
      bool disjoint = true;
      for (const Lit x : rows[best]) disjoint = disjoint && vstamp[var_of(x)] != now;
      if (disjoint) {
        chosen.push_back(best);
        for (const Lit x : rows[best]) vstamp[var_of(x)] = now;
      }
      next.clear();
      for (const uint32_t c : pool) {
        if (c != best && compat[size_t{c} * n + best]) next.push_back(c);
      }
      pool.swap(next);
    }
    if (chosen.size() <= s) continue;
    // Pigeonhole s + 1 -> s (the smallest refutable subsystem).
    st.kind = kPigeonhole;
    st.embedded = true;
    st.pigeons = s + 1;
    st.holes = s;
    st.k = 1;
    st.cell.clear();
    st.longs.clear();
    st.vars.clear();
    for (uint32_t i = 0; i <= s; ++i) {
      st.cell.insert(st.cell.end(), rows[chosen[i]].begin(), rows[chosen[i]].end());
      st.longs.push_back(rowref[chosen[i]]);
    }
    for (const Lit x : st.cell) st.vars.push_back(var_of(x));
    std::sort(st.vars.begin(), st.vars.end());
    st.all_vars = st.vars.size();
    for (uint64_t m = 1; m <= s; ++m) {
      st.steps_pr += m * (m - 1);
      st.steps_units += m;
    }
    st.degree_sum = uint64_t{s} * st.all_vars;  // (in the isolated subsystem: about s per literal)
    st.long_sum = uint64_t{s} * st.all_vars;
    return true;
  }
  return false;
}

// Pigeonhole systems on a sparse graph (randomG-n18-d05: 19 pigeons, 18 holes, half of the pairs
// absent, i.e. no perfect matching of an unbalanced bipartite graph).
//  - Vertex clauses are the candidate pigeons: long clauses whose variables occur in at most two
//    long clauses, with one polarity, and clauses of two literals that occur in no other clause of
//    two literals (the squares with two neighbours of a mutilated chessboard). A variable in two
//    vertex clauses is an edge of a graph given with the at-least-one clauses of both sides
//    (randomG-B): the clause graph is 2-coloured, and each side in turn gives the pigeons (the
//    larger side of each component first); components with an odd cycle are left out.
//  - Exclusions: binary clauses between structure literals of different pigeons, and with `probe`
//    also pairs where one literal falsifies the other by propagation over the binary clauses
//    (at-most-one constraints over auxiliary variables; the proof derives them by RUP). The
//    propagation stops at falsified structure literals: (y v z) of a short pigeon would carry on
//    from -y to z and its exclusions, in other holes.
//  - Holes: the classes of structure literals joined by exclusions. A class that is no clique is
//    split into cliques greedily (the literal with the most exclusions first, then the candidates
//    with the most exclusions among the candidates): other exclusions between the pigeons'
//    variables (blocked clauses added to the formula) are no reason to give up. Any partition
//    into cliques is sound; a coarser one finds more.
//  - A maximum matching of pigeons to holes that leaves a pigeon unmatched gives a Hall violator:
//    the pigeons S reached from it by alternating paths have |S| - 1 holes between them. That
//    subsystem is refuted in isolation by elimination (counting_isolated_sparse), with new
//    variables only where a pigeon needs another one's hole.
// Clauses satisfied at the root do not count, and literals false at the root are left out (a unit
// clause of the input takes a pigeon's hole: the pigeon clause is satisfied, the other pigeons
// lose the hole). The formula may say anything else: other clauses are ignored here and deleted
// from the proof.
bool Solver::counting_detect_sparse(CountingState& st, bool probe) {
  const size_t nv = num_vars_, nl = 2 * nv;
  constexpr uint32_t kNone = UINT32_MAX;
  const uint64_t cap = st.work + 4 * (arena_.size() + 2 * binaries_irredundant_) + 8'000'000;
  // 1. Vertex clauses. The unassigned literals of vertex clause i are clits[coff[i] .. coff[i + 1]);
  //    cref[i] is its clause, or none for a binary clause. The long ones come first.
  auto unassigned = [this](const Clause& c) {  // the number of unassigned literals; 0 if satisfied
    uint32_t n = 0;
    for (uint32_t k = 0; k < c.size; ++k) {
      const int8_t v = vals_[c.lits()[k]];
      if (v > 0) return 0u;
      n += !v;
    }
    return n;
  };
  std::vector<uint8_t> mult(nv, 0), pol(nv, 0);  // long clauses of a variable (up to 3), its polarities there
  std::vector<uint32_t> two, more;               // long clauses with two unassigned literals, with more
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    st.work += c.size / 4 + 1;
    const uint32_t n = unassigned(c);
    if (n < 2) continue;
    if (n == 2) {
      two.push_back(ref);
      continue;
    }
    more.push_back(ref);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit l = c.lits()[k];
      if (vals_[l]) continue;
      uint8_t& m = mult[var_of(l)];
      if (m < 3) ++m;
      pol[var_of(l)] |= is_negative(l) ? 2 : 1;
    }
  }
  std::vector<uint32_t> cref, coff(1, 0);
  std::vector<Lit> clits;
  for (const uint32_t ref : more) {
    const Clause& c = clause(ref);
    const size_t start = clits.size();
    bool ok = true;
    for (uint32_t k = 0; k < c.size && ok; ++k) {
      const Lit l = c.lits()[k];
      if (vals_[l]) continue;
      ok = mult[var_of(l)] <= 2 && pol[var_of(l)] != 3;
      clits.push_back(l);
    }
    if (!ok) {
      clits.resize(start);
      continue;
    }
    cref.push_back(ref);
    coff.push_back(static_cast<uint32_t>(clits.size()));
  }
  st.work += more.size() / 2 + nv / 16;
  const auto nlong = static_cast<uint32_t>(cref.size());
  if (nlong < 3 || st.work > cap) return false;
  // Short vertex clauses (y v z): y and z occur in no other clause of two literals, and their
  // variables in at most one long clause, there with the same polarity. Where the long vertex
  // clauses have literals of one sign only, so have the short ones (the binary clauses of a
  // sequential counter are no pigeons). Two short vertex clauses with y and -y end up on
  // different sides below.
  {
    uint8_t sign = 3;  // of the long vertex clauses' literals: 1 positive, 2 negative, 0 both
    for (const Lit l : clits) sign &= is_negative(l) ? 2 : 1;
    auto fits = [&](Lit l) {  // (but for the other clauses of two literals)
      const Var v = var_of(l);
      if (vals_[l] || (sign && sign != (is_negative(l) ? 2 : 1))) return false;
      return mult[v] <= 1 && !(pol[v] & (is_negative(l) ? 1 : 2));
    };
    auto add = [&](Lit a, Lit b, uint32_t ref) {
      clits.push_back(a);
      clits.push_back(b);
      cref.push_back(ref);
      coff.push_back(static_cast<uint32_t>(clits.size()));
    };
    // The unassigned literals of the long clauses with two of them, sorted.
    std::vector<Lit> twolits;
    for (const uint32_t ref : two) {
      const Clause& c = clause(ref);
      for (uint32_t k = 0; k < c.size; ++k) {
        if (!vals_[c.lits()[k]]) twolits.push_back(c.lits()[k]);
      }
    }
    std::sort(twolits.begin(), twolits.end());
    auto in_two = [&](Lit l) {
      const auto r = std::equal_range(twolits.begin(), twolits.end(), l);
      return static_cast<size_t>(r.second - r.first);
    };
    // Literals with one binary clause: (literal, the other one), ascending.
    std::vector<std::pair<Lit, Lit>> single;
    for (Lit l = 0; l < nl; ++l) {
      if (!fits(l)) continue;
      uint32_t n = 0, seen = 0;
      Lit other = kNoLit;
      for (const Watch& w : watches_[l]) {
        ++seen;
        if (!w.binary() || w.redundant_binary() || vals_[w.blit]) continue;
        other = w.blit;
        if (++n > 1) break;
      }
      st.work += seen / 4 + 1;
      if (n == 1 && !in_two(l)) single.emplace_back(l, other);
    }
    if (st.work > cap) return false;
    for (const auto& s : single) {
      if (s.first < s.second && var_of(s.first) != var_of(s.second) &&
          std::binary_search(single.begin(), single.end(), std::make_pair(s.second, s.first))) {
        add(s.first, s.second, kNone);
      }
    }
    auto no_binary = [&](Lit l) {
      for (const Watch& w : watches_[l]) {
        if (w.binary() && !w.redundant_binary() && !vals_[w.blit]) return false;
      }
      return true;
    };
    for (const uint32_t ref : two) {
      const Clause& c = clause(ref);
      Lit ab[2] = {kNoLit, kNoLit};
      uint32_t n = 0;
      for (uint32_t k = 0; k < c.size && n < 2; ++k) {
        if (!vals_[c.lits()[k]]) ab[n++] = c.lits()[k];
      }
      if (var_of(ab[0]) == var_of(ab[1]) || !fits(ab[0]) || !fits(ab[1])) continue;
      if (in_two(ab[0]) != 1 || in_two(ab[1]) != 1 || !no_binary(ab[0]) || !no_binary(ab[1])) continue;
      add(ab[0], ab[1], ref);
    }
    st.work += single.size() + 4 * two.size();
  }
  const auto nvert = static_cast<uint32_t>(cref.size());
  // 2. The clause graph (vertex clauses sharing a variable) and its 2-colouring. side[i]: 0 or 1,
  //    2 in a component with an odd cycle.
  std::vector<uint8_t> side(nvert, 3);
  std::vector<uint32_t> queue;
  bool two_sided = false;
  {
    std::vector<uint32_t> first(nv, kNone), second(nv, kNone);
    for (uint32_t i = 0; i < nvert; ++i) {
      for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
        const Var v = var_of(clits[k]);
        (first[v] == kNone ? first[v] : second[v]) = i;
      }
    }
    for (uint32_t s = 0; s < nvert; ++s) {
      if (side[s] != 3) continue;
      queue.assign(1, s);
      side[s] = 0;
      bool odd = false;
      uint32_t zeros = 0;
      for (size_t at = 0; at < queue.size(); ++at) {
        const uint32_t i = queue[at];
        zeros += side[i] == 0;
        for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
          const Var v = var_of(clits[k]);
          const uint32_t j = first[v] == i ? second[v] : first[v];
          if (j == kNone) continue;
          if (side[j] == 3) {
            side[j] = side[i] ^ 1;
            queue.push_back(j);
          } else if (side[j] == side[i]) {
            odd = true;
          }
        }
        st.work += coff[i + 1] - coff[i];
      }
      const bool flip = 2 * zeros < queue.size();  // (side 0: the larger one)
      for (const uint32_t i : queue) side[i] = odd ? 2 : side[i] ^ (flip ? 1 : 0);
      two_sided = two_sided || (!odd && queue.size() > 1);
    }
    st.work += nv / 8;
  }
  if (st.work > cap) return false;
  // 3. Each side in turn: exclusions, holes, a maximum matching, a Hall violator; first with the
  //    exclusions of binary clauses, then with those found by probing too. The structure
  //    literals of a side are numbered pigeon by pigeon: those of pigeon p are
  //    slits[poff[p] .. poff[p + 1]), and rank[v] is the number of the one on variable v.
  std::vector<uint32_t> rank(nv, kNone);
  std::vector<uint32_t> pig, poff, ownr, hole, parent, degree, stamp, xoff, xadj;
  std::vector<Lit> slits, trail;
  std::vector<uint8_t> alive;
  std::vector<std::pair<uint32_t, uint32_t>> edges;  // exclusions, between structure literals, both ways
  std::vector<std::pair<Lit, Lit>> virt;             // those found by probing
  std::vector<int8_t> val;
  uint32_t now = 0, np = 0, ns = 0;
  auto find = [&](uint32_t v) {
    while (parent[v] != v) v = parent[v] = parent[parent[v]];
    return v;
  };
  // Holes, matching and violator with the exclusions in `edges`: 1 found (st is filled), 0 not,
  // -1 out of budget.
  auto attempt = [&]() -> int {
    std::sort(edges.begin(), edges.end());
    edges.erase(std::unique(edges.begin(), edges.end()), edges.end());
    st.work += edges.size();
    xoff.assign(ns + 1, 0);
    for (const auto& e : edges) ++xoff[e.first + 1];
    for (uint32_t v = 0; v < ns; ++v) xoff[v + 1] += xoff[v];
    xadj.resize(edges.size());
    for (size_t i = 0; i < edges.size(); ++i) xadj[i] = edges[i].second;
    // A short pigeon needs an exclusion with a long pigeon's literal (others are no part of this).
    alive.assign(np, 1);
    for (uint32_t p = 0; p < np; ++p) {
      if (pig[p] < nlong) continue;
      bool any = false;
      for (uint32_t v = poff[p]; v < poff[p + 1] && !any; ++v) {
        for (uint32_t e = xoff[v]; e < xoff[v + 1] && !any; ++e) any = pig[ownr[xadj[e]]] < nlong;
      }
      alive[p] = any;
    }
    // Holes: classes of the exclusion graph, split into cliques where they are none.
    parent.resize(ns);
    std::iota(parent.begin(), parent.end(), 0u);
    for (const auto& e : edges) {
      if (e.first < e.second && alive[ownr[e.first]] && alive[ownr[e.second]]) parent[find(e.first)] = find(e.second);
    }
    std::vector<uint32_t> members;  // the live structure literals, by class
    {
      std::vector<uint32_t> start(ns + 1, 0);
      uint32_t count = 0;
      for (uint32_t v = 0; v < ns; ++v) {
        if (!alive[ownr[v]]) continue;
        ++start[find(v) + 1];
        ++count;
      }
      for (uint32_t v = 0; v < ns; ++v) start[v + 1] += start[v];
      members.resize(count);
      for (uint32_t v = 0; v < ns; ++v) {
        if (alive[ownr[v]]) members[start[find(v)]++] = v;
      }
      st.work += 2 * ns;
    }
    hole.assign(ns, kNone);
    degree.assign(ns, 0);
    stamp.assign(ns, 0);
    now = 0;
    uint32_t holes = 0;
    std::vector<uint32_t> cs, next, chosen;
    for (size_t a = 0; a < members.size();) {
      size_t b = a;
      const uint32_t root = find(members[a]);
      while (b < members.size() && find(members[b]) == root) ++b;
      const size_t size = b - a;
      bool clique = true;
      for (size_t i = a; i < b; ++i) {
        const uint32_t v = members[i];
        uint32_t d = 0;
        for (uint32_t e = xoff[v]; e < xoff[v + 1]; ++e) d += alive[ownr[xadj[e]]];
        degree[v] = d;
        clique = clique && d + 1 == size;
        st.work += xoff[v + 1] - xoff[v] + 1;
      }
      if (clique) {
        for (size_t i = a; i < b; ++i) hole[members[i]] = holes;
        ++holes;
        a = b;
        continue;
      }
      if (size > 4096) return 0;
      // (In the order of the exclusions within the class, most first.)
      std::sort(members.begin() + static_cast<std::ptrdiff_t>(a), members.begin() + static_cast<std::ptrdiff_t>(b),
                [&](uint32_t x, uint32_t y) { return degree[x] != degree[y] ? degree[x] > degree[y] : x < y; });
      st.work += size;
      for (size_t i = a; i < b; ++i) {
        const uint32_t v = members[i];
        if (hole[v] != kNone) continue;
        // The clique of v: of the unassigned literals it excludes, the one with the most
        // exclusions among them, then the same among those that one excludes too, and so on.
        cs.clear();
        for (uint32_t e = xoff[v]; e < xoff[v + 1]; ++e) {
          const uint32_t u = xadj[e];
          if (alive[ownr[u]] && hole[u] == kNone) cs.push_back(u);
        }
        chosen.assign(1, v);
        while (!cs.empty()) {
          ++now;
          for (const uint32_t u : cs) stamp[u] = now;
          uint32_t best = kNone, most = 0;
          for (const uint32_t u : cs) {
            uint32_t d = 0;
            for (uint32_t e = xoff[u]; e < xoff[u + 1]; ++e) d += stamp[xadj[e]] == now;
            st.work += xoff[u + 1] - xoff[u] + 1;
            if (best == kNone || d > most) {
              best = u;
              most = d;
            }
          }
          chosen.push_back(best);
          next.clear();
          for (uint32_t e = xoff[best]; e < xoff[best + 1]; ++e) {
            if (stamp[xadj[e]] == now) next.push_back(xadj[e]);
          }
          cs.swap(next);
        }
        for (const uint32_t u : chosen) hole[u] = holes;
        ++holes;
        if (st.work > cap) return -1;
      }
      a = b;
    }
    if (st.work > cap) return -1;
    // A maximum matching of the live pigeons to holes: greedy, then augmenting paths
    // (breadth-first).
    std::vector<uint32_t> match_hole(holes, kNone), match_pig(np, kNone);
    uint32_t live = 0;
    for (uint32_t p = 0; p < np; ++p) {
      if (!alive[p]) continue;
      ++live;
      for (uint32_t v = poff[p]; v < poff[p + 1]; ++v) {
        const uint32_t h = hole[v];
        if (match_hole[h] != kNone) continue;
        match_hole[h] = p;
        match_pig[p] = h;
        break;
      }
      st.work += (poff[p + 1] - poff[p]) / 4 + 1;
    }
    if (live < 3) return 0;
    std::vector<uint32_t> pstamp(np, 0), hstamp(holes, 0), reached(holes, kNone), best_pigeons, best_holes, hs;
    uint32_t run = 0;
    // The pigeons and holes reached from p0 by alternating paths; true if a free hole ended one
    // (then the matching grew by one).
    auto search = [&](uint32_t p0) {
      ++run;
      queue.assign(1, p0);
      hs.clear();
      pstamp[p0] = run;
      for (size_t at = 0; at < queue.size(); ++at) {
        const uint32_t q = queue[at];
        st.work += poff[q + 1] - poff[q] + 1;
        for (uint32_t v = poff[q]; v < poff[q + 1]; ++v) {
          const uint32_t h = hole[v];
          if (hstamp[h] == run) continue;
          hstamp[h] = run;
          reached[h] = q;
          hs.push_back(h);
          const uint32_t m = match_hole[h];
          if (m == kNone) {  // augment along the path back to p0
            for (uint32_t hh = h, pp = q;;) {
              const uint32_t before = match_pig[pp];
              match_hole[hh] = pp;
              match_pig[pp] = hh;
              if (pp == p0) break;
              hh = before;
              pp = reached[hh];
            }
            return true;
          }
          if (pstamp[m] != run) {
            pstamp[m] = run;
            queue.push_back(m);
          }
        }
      }
      return false;
    };
    for (uint32_t p = 0; p < np; ++p) {
      if (!alive[p] || match_pig[p] != kNone) continue;
      search(p);
      if (st.work > cap) return -1;
    }
    // The smallest Hall violator among those of the first unmatched pigeons. (Three holes or
    // more: then a pigeon of two literals has an absent pair, and its clause is replaced.)
    uint32_t tried = 0;
    for (uint32_t p = 0; p < np && tried < 16; ++p) {
      if (!alive[p] || match_pig[p] != kNone) continue;
      ++tried;
      if (search(p)) return -1;  // (cannot happen: the matching is maximum)
      if (st.work > cap) return -1;
      if (queue.size() != hs.size() + 1) return -1;
      if (hs.size() < 3) continue;
      if (best_pigeons.empty() || queue.size() < best_pigeons.size()) {
        best_pigeons = queue;
        best_holes = hs;
      }
    }
    if (best_pigeons.empty()) return 0;  // every pigeon has a hole
    const auto pigeons = static_cast<uint32_t>(best_pigeons.size()), nholes = static_cast<uint32_t>(best_holes.size());
    if (uint64_t{pigeons} * nholes > (uint64_t{1} << 24)) return 0;
    std::sort(best_pigeons.begin(), best_pigeons.end());
    std::sort(best_holes.begin(), best_holes.end());
    std::vector<uint32_t> local(holes, kNone);
    for (uint32_t i = 0; i < nholes; ++i) local[best_holes[i]] = i;
    st.cell.assign(size_t{pigeons} * nholes, kNoLit);
    for (uint32_t i = 0; i < pigeons; ++i) {
      const uint32_t p = best_pigeons[i];
      st.longs.push_back(cref[pig[p]]);
      for (uint32_t v = poff[p]; v < poff[p + 1]; ++v) {
        st.cell[size_t{i} * nholes + local[hole[v]]] = slits[v];
        st.vars.push_back(var_of(slits[v]));
      }
    }
    std::sort(st.vars.begin(), st.vars.end());
    if (!virt.empty()) {
      std::sort(virt.begin(), virt.end());
      virt.erase(std::unique(virt.begin(), virt.end()), virt.end());
      st.voff.assign(nl + 1, 0);
      for (const auto& pr : virt) ++st.voff[pr.first + 1];
      for (size_t l = 0; l < nl; ++l) st.voff[l + 1] += st.voff[l];
      st.vlit.resize(virt.size());
      for (size_t i = 0; i < virt.size(); ++i) st.vlit[i] = virt[i].second;
      st.virt = true;
      st.work += virt.size();
    }
    st.missing = static_cast<uint32_t>(std::count(st.cell.begin(), st.cell.end(), kNoLit));
    st.kind = kPigeonhole;
    st.embedded = true;
    st.sparse = true;
    st.pigeons = pigeons;
    st.holes = nholes;
    st.k = 1;
    st.graph_pigeons = live;
    st.graph_holes = holes;
    return 1;  // (the steps and the work estimate: counting_plan)
  };
  // One side: 1 found, 0 not, -1 out of budget.
  auto run_side = [&]() -> int {
    // Exclusions by binary clauses.
    edges.clear();
    virt.clear();
    for (uint32_t x = 0; x < ns; ++x) {
      const Lit nx = negate(slits[x]);
      for (const Watch& w : watches_[nx]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const uint32_t u = rank[var_of(w.blit)];
        if (u == kNone || ownr[u] == ownr[x] || slits[u] != negate(w.blit)) continue;
        edges.emplace_back(x, u);
      }
      st.work += watches_[nx].size() / 4 + 1;
      if (st.work > cap || edges.size() > 8'000'000) return -1;
    }
    if (!edges.empty()) {  // (else no hole has two pigeons)
      const int r = attempt();
      if (r) return r;
    }
    if (!probe) return 0;
    // Exclusions by probing: each structure literal is propagated over the binary clauses; a
    // literal that falsifies a structure literal is recorded and not followed. Given up after
    // 256 probes without any, and within a budget of its own (a probe through a sequential
    // counter of m literals costs m: 4M covers 126 holes of 127 pigeons each).
    if (val.empty()) val.assign(vals_.begin(), vals_.end());
    const uint64_t probe_cap = std::min(cap, st.work + (arena_.size() + 2 * binaries_irredundant_) / 32 + 4'000'000);
    stamp.assign(ns, 0);
    now = 0;
    for (uint32_t x = 0; x < ns; ++x) {
      if (x == 256 && virt.empty()) return 0;
      const Lit lx = slits[x];
      trail.assign(1, lx);
      val[lx] = 1;
      val[negate(lx)] = -1;
      bool conflict = false;
      size_t leaves = 0;
      for (size_t head = 0; head < trail.size() && !conflict && trail.size() < 4096; ++head) {
        const Lit t = trail[head];
        const uint32_t r = rank[var_of(t)];
        if (head && r != kNone && slits[r] == negate(t)) {
          ++leaves;
          continue;
        }
        const Lit f = negate(t);
        for (const Watch& w : watches_[f]) {  // binary clauses (f v b): b
          if (!w.binary() || w.redundant_binary()) continue;
          const int8_t v = val[w.blit];
          if (v > 0) continue;
          if (v < 0) {
            conflict = true;
            break;
          }
          val[w.blit] = 1;
          val[negate(w.blit)] = -1;
          trail.push_back(w.blit);
        }
        st.work += watches_[f].size() / 4 + 1;
      }
      if (!conflict && leaves) {
        ++now;
        for (const Watch& w : watches_[negate(lx)]) {  // (excluded by a binary clause: known)
          if (!w.binary() || w.redundant_binary()) continue;
          const uint32_t u = rank[var_of(w.blit)];
          if (u != kNone) stamp[u] = now;
        }
        for (size_t m = 1; m < trail.size(); ++m) {
          const uint32_t u = rank[var_of(trail[m])];
          if (u == kNone || ownr[u] == ownr[x] || slits[u] != negate(trail[m]) || stamp[u] == now) continue;
          edges.emplace_back(x, u);
          edges.emplace_back(u, x);
          virt.emplace_back(lx, slits[u]);
          virt.emplace_back(slits[u], lx);
        }
      }
      for (const Lit t : trail) val[t] = val[negate(t)] = 0;
      if (st.work > probe_cap || edges.size() > 8'000'000) return st.work > cap ? -1 : 0;
    }
    if (virt.empty()) return 0;  // (the same exclusions as before)
    return attempt();
  };
  for (uint8_t which = 0; which < (two_sided ? 2 : 1); ++which) {
    pig.clear();
    poff.assign(1, 0);
    slits.clear();
    ownr.clear();
    for (uint32_t i = 0; i < nvert; ++i) {
      if (side[i] != which) continue;
      for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
        rank[var_of(clits[k])] = static_cast<uint32_t>(slits.size());
        slits.push_back(clits[k]);
        ownr.push_back(static_cast<uint32_t>(pig.size()));
      }
      pig.push_back(i);
      poff.push_back(static_cast<uint32_t>(slits.size()));
    }
    np = static_cast<uint32_t>(pig.size());
    ns = static_cast<uint32_t>(slits.size());
    st.work += nvert / 4 + ns;
    const int r = np < 3 ? 0 : run_side();
    if (r) return r > 0;
    for (const Lit l : slits) rank[var_of(l)] = kNone;
  }
  return false;
}

// Refutes the embedded subsystem on its own: a solver on its pigeon clauses and its at-most-one
// binary clauses (renumbered variables) runs the pass. If it refutes them, the proof deletes every
// other clause (the checker then sees the subsystem only, as the isolated solver did) and
// continues with the isolated solver's proof, which ends with the empty clause. Refuting a subset
// of the clauses refutes the formula. Otherwise nothing is written.
bool Solver::counting_isolated(CountingState& st) {
  if (st.sparse) return counting_isolated_sparse(st);
  const uint32_t holes = st.holes, pigeons = st.pigeons;
  // The isolated solver's variable of a cell is the cell's index (pigeon * holes + hole).
  std::vector<uint32_t> where(num_vars_, UINT32_MAX);
  std::vector<Lit> to_main;
  for (uint32_t i = 0; i < pigeons * holes; ++i) {
    const Var v = var_of(st.cell[i]);
    if (where[v] != UINT32_MAX) {
      st.failure = "variable in two cells";
      return false;
    }
    where[v] = i;
    // (its proof is copied into this one as encoded: in the input numbering)
    to_main.push_back(external_lit(make_lit(v, false)));
    to_main.push_back(external_lit(make_lit(v, true)));
  }
  auto dimacs = [&](Lit x) { return to_dimacs(make_lit(where[var_of(x)], is_negative(x))); };
  // In the subsystem: (-a v -b) for structure literals a, b of one hole and different pigeons, or
  // of one pigeon.
  auto in_subsystem = [&](Lit a, Lit b) {  // the binary clause (-a v -b)
    const uint32_t wa = where[var_of(a)], wb = where[var_of(b)];
    if (wa == UINT32_MAX || wb == UINT32_MAX || st.cell[wa] != a || st.cell[wb] != b || wa == wb) return false;
    return (wa / holes != wb / holes) == (wa % holes == wb % holes);
  };
  Options o = opts_;
  o.counting = 1;
  o.lucky = 0;
  o.verbose = 0;
  o.cardinality = 0;
  o.renumber = 0;
  o.linmod = 0;
  Solver iso(o);
  iso.counting_isolated_ = true;
  iso.start_ = start_;  // (the same clock, time limit and terminate flag: see stop_requested())
  iso.time_limit_ = time_limit_;
  iso.terminate_ = terminate_;
  std::string buffer;
  {
    ProofWriter iso_proof([&buffer](const char* d, size_t n) { buffer.append(d, n); },
                          proof_ ? proof_->binary() : true);
    iso_proof.set_map(&to_main);
    if (proof_) iso.set_proof(&iso_proof);
    iso.reserve(static_cast<int>(to_main.size() / 2));
    std::vector<int> cl;
    for (uint32_t i = 0; i < pigeons; ++i) {
      cl.clear();
      for (uint32_t h = 0; h < holes; ++h) cl.push_back(dimacs(st.cell[i * holes + h]));
      iso.add_clause(cl.data(), cl.size());
    }
    // Its at-most-one clauses: binary clauses of the formula, and virtual exclusions, which the
    // proof derives by RUP before the auxiliary clauses are deleted.
    std::vector<Lit> lemmas;  // pairs
    std::vector<uint64_t> fed;
    for (uint32_t i = 0; i < pigeons * holes; ++i) {
      const Lit a = st.cell[i];
      for (const Watch& w : watches_[negate(a)]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const Lit b = negate(w.blit);
        if (a < b && in_subsystem(a, b)) {
          const int bin[2] = {dimacs(negate(a)), dimacs(negate(b))};
          iso.add_clause(bin, 2);
          fed.push_back(uint64_t{a} << 32 | b);
        }
      }
    }
    if (st.virt) {
      std::sort(fed.begin(), fed.end());
      for (uint32_t i = 0; i < pigeons * holes; ++i) {
        const Lit a = st.cell[i];
        for (uint32_t k = st.voff[a]; k < st.voff[a + 1]; ++k) {
          const Lit b = st.vlit[k];
          if (!(a < b) || !in_subsystem(a, b)) continue;
          const uint64_t key = uint64_t{a} << 32 | b;
          if (std::binary_search(fed.begin(), fed.end(), key)) continue;
          lemmas.push_back(a);
          lemmas.push_back(b);
          const int bin[2] = {dimacs(negate(a)), dimacs(negate(b))};
          iso.add_clause(bin, 2);
        }
      }
    }
    iso.set_conflict_limit(0);
    const int res = iso.solve();
    stop_after(iso);
    stats_.counting_work += iso.stats().counting_work;
    if (res != kUnsat || !iso.stats().counting_found) {
      st.failure = "the isolated subsystem was not refuted";
      return false;
    }
    iso_proof.flush();
    // The virtual exclusions as RUP lemmas (checked here; with a proof also written).
    if (!lemmas.empty() && propagated_ < trail_.size() && !propagate()) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
      return true;
    }
    for (size_t i = 0; i < lemmas.size(); i += 2) {
      const Lit bin[2] = {negate(lemmas[i]), negate(lemmas[i + 1])};
      if (!counting_refutes(bin, 2)) {
        st.failure = "a virtual exclusion is not RUP";
        return false;
      }
    }
    if (proof_) {
      for (size_t i = 0; i < lemmas.size(); i += 2) {
        const Lit bin[2] = {negate(lemmas[i]), negate(lemmas[i + 1])};
        proof_->add(bin, 2);
      }
      stats_.counting_lemmas += lemmas.size() / 2;
      // Delete every other clause, then the isolated refutation. The PR checks need the other
      // clauses on the subsystem's variables gone (the checker then sees the subsystem only, as
      // the isolated solver did); the rest goes too, since dpr-trim and cake_lpr visit every
      // clause of the formula for each PR clause (exam_90_80: dpr-trim 2729 s for a 0.8 s solve).
      std::vector<uint32_t> keep = st.longs;
      std::sort(keep.begin(), keep.end());
      for (const uint32_t ref : clauses_) {
        const Clause& c = clause(ref);
        if (c.garbage || std::binary_search(keep.begin(), keep.end(), ref)) continue;
        proof_->del(c.lits(), c.size);
      }
      for (Lit l = 0; l < 2 * num_vars_; ++l) {
        for (const Watch& w : watches_[l]) {
          if (!w.binary()) continue;
          const Lit b = w.blit;
          if (b < l) continue;  // (deleted from b's list)
          if (in_subsystem(negate(l), negate(b))) continue;
          const Lit bin[2] = {l, b};
          proof_->del(bin, 2);
        }
      }
      proof_->raw(buffer.data(), buffer.size(), iso_proof.added(), iso_proof.deleted(), iso_proof.pr(),
                  iso_proof.deleted_bytes());
    }
  }
  stats_.counting_pr += iso.stats().counting_pr;
  stats_.counting_units += iso.stats().counting_units;
  stats_.counting_lemmas += iso.stats().counting_lemmas;
  counting_added_ = true;
  inconsistent_ = true;
  return true;
}

// The elimination plan of a sparse pigeonhole (see Elimination): the structure in the plan's
// numbering (the cells in the order of st.cell), and a first run that counts its steps and new
// variables for the report and the work estimate. Over the budget, or without a refutation at the
// end, the estimate is set beyond every budget.
void Solver::counting_plan(CountingState& st) {
  CountingPlan& plan = st.plan;
  plan.pigeons = st.pigeons;
  plan.holes = st.holes;
  plan.poff.assign(1, 0);
  for (uint32_t i = 0; i < st.pigeons; ++i) {
    for (uint32_t h = 0; h < st.holes; ++h) {
      if (st.cell[size_t{i} * st.holes + h] != kNoLit) plan.hole.push_back(h);
    }
    plan.poff.push_back(static_cast<uint32_t>(plan.hole.size()));
  }
  const uint64_t budget = static_cast<uint64_t>(opts_.countingeffort) * 1000000;
  Elimination elim(plan.pigeons, plan.holes, plan.poff, plan.hole);
  std::vector<uint32_t> ops;
  bool over = false;
  while (!elim.done() && !over) {
    elim.round(ops);
    over = 16 * (elim.steps_pr + elim.steps_units + elim.steps_lemmas) > budget || elim.work > budget / 4;
  }
  st.work += elim.work;
  plan.fresh = elim.cells() - static_cast<uint32_t>(plan.hole.size());
  plan.steps_pr = st.steps_pr = elim.steps_pr;
  plan.steps_units = st.steps_units = elim.steps_units;
  // The estimate's averages, over the PR clauses and units: the cells of the holes a step looks
  // at (the other clauses' share added), and one pigeon clause.
  st.all_vars = std::max<uint64_t>(1, elim.steps_pr + elim.steps_units);
  st.degree_sum = elim.degree + 4 * elim.steps_lemmas;
  st.long_sum = st.all_vars;
  if (over || !elim.refuted()) st.steps_pr = UINT64_MAX / 4096;
}

// A sparse pigeonhole (a Hall violator of the graph: st.pigeons pigeons with st.holes holes between
// them) is refuted in isolation by elimination: a separate solver gets the pigeon clauses and the
// exclusions within the holes, with the plan's cells as its variables and room for the plan's new
// ones (above this solver's variables in the proof; they exist in that solver and in the proof
// only: this solver ends here if the refutation succeeds, and nothing is written if it does not),
// and runs the plan (counting_certify), checking every step on its clauses. The proof first gets
// the exclusions found by probing (RUP) and the pigeon clauses without their literals false at the
// root (the isolated solver's clauses must be the checker's: it deletes a pigeon clause when it
// widens it), then deletes every other clause, then continues with the isolated refutation.
bool Solver::counting_isolated_sparse(CountingState& st) {
  constexpr uint32_t kNone = UINT32_MAX;
  const uint32_t holes = st.holes, pigeons = st.pigeons;
  const CountingPlan& plan = st.plan;
  std::vector<uint32_t> where(num_vars_, kNone);  // variable -> index in st.cell
  std::vector<uint32_t> id(st.cell.size(), kNone);  // index in st.cell -> the plan's cell
  std::vector<Lit> to_main;
  uint32_t cells = 0;
  for (uint32_t c = 0; c < st.cell.size(); ++c) {
    const Lit l = st.cell[c];
    if (l == kNoLit) continue;
    if (where[var_of(l)] != kNone) {
      st.failure = "variable in two cells";
      return false;
    }
    where[var_of(l)] = c;
    id[c] = cells++;
    // (the isolated proof is copied into this one as encoded: in the input numbering; a cell is
    // the positive literal of its variable there, whatever its sign here)
    to_main.push_back(external_lit(l));
    to_main.push_back(external_lit(negate(l)));
  }
  for (uint32_t k = 0; k < plan.fresh; ++k) {  // (beyond the proof writer's map: written as they are)
    to_main.push_back(make_lit(num_vars_ + k, false));
    to_main.push_back(make_lit(num_vars_ + k, true));
  }
  // In the subsystem: (-a v -b) for structure literals a, b of one hole and different pigeons.
  auto in_subsystem = [&](Lit a, Lit b) {
    const uint32_t wa = where[var_of(a)], wb = where[var_of(b)];
    if (wa == kNone || wb == kNone || st.cell[wa] != a || st.cell[wb] != b) return false;
    return wa / holes != wb / holes && wa % holes == wb % holes;
  };
  auto exclusion = [&](Lit a, Lit b, int* bin) {
    bin[0] = -static_cast<int>(id[where[var_of(a)]] + 1);
    bin[1] = -static_cast<int>(id[where[var_of(b)]] + 1);
  };
  Options o = opts_;
  o.counting = 1;
  o.lucky = 0;
  o.verbose = 0;
  o.cardinality = 0;
  o.renumber = 0;
  o.linmod = 0;
  o.xorsub = 0;
  Solver iso(o);
  iso.counting_isolated_ = true;
  iso.counting_plan_ = &plan;
  iso.start_ = start_;  // (the same clock, time limit and terminate flag: see stop_requested())
  iso.time_limit_ = time_limit_;
  iso.terminate_ = terminate_;
  std::string buffer;
  {
    ProofWriter iso_proof([&buffer](const char* d, size_t n) { buffer.append(d, n); },
                          proof_ ? proof_->binary() : true);
    iso_proof.set_map(&to_main);
    if (proof_) iso.set_proof(&iso_proof);
    iso.reserve(static_cast<int>(to_main.size() / 2));
    std::vector<int> cl;
    for (uint32_t i = 0; i < pigeons; ++i) {
      cl.clear();
      for (uint32_t c = plan.poff[i]; c < plan.poff[i + 1]; ++c) cl.push_back(static_cast<int>(c) + 1);
      iso.add_clause(cl.data(), cl.size());
    }
    // Its at-most-one clauses: binary clauses of the formula, and virtual exclusions, which the
    // proof derives by RUP before the auxiliary clauses are deleted.
    std::vector<Lit> lemmas;  // pairs
    std::vector<uint64_t> fed;
    int bin[2];
    for (const Lit a : st.cell) {
      if (a == kNoLit) continue;
      for (const Watch& w : watches_[negate(a)]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const Lit b = negate(w.blit);
        if (a < b && in_subsystem(a, b)) {
          exclusion(a, b, bin);
          iso.add_clause(bin, 2);
          fed.push_back(uint64_t{a} << 32 | b);
        }
      }
    }
    if (st.virt) {
      std::sort(fed.begin(), fed.end());
      for (const Lit a : st.cell) {
        if (a == kNoLit) continue;
        for (uint32_t k = st.voff[a]; k < st.voff[a + 1]; ++k) {
          const Lit b = st.vlit[k];
          if (!(a < b) || !in_subsystem(a, b)) continue;
          const uint64_t key = uint64_t{a} << 32 | b;
          if (std::binary_search(fed.begin(), fed.end(), key)) continue;
          lemmas.push_back(a);
          lemmas.push_back(b);
          exclusion(a, b, bin);
          iso.add_clause(bin, 2);
        }
      }
    }
    iso.set_conflict_limit(0);
    const int res = iso.solve();
    stop_after(iso);
    stats_.counting_work += iso.stats().counting_work;
    st.work += iso.stats().counting_work;  // (for the report)
    if (res != kUnsat || !iso.stats().counting_found) {
      st.failure = "the isolated subsystem was not refuted";
      return false;
    }
    iso_proof.flush();
    // The virtual exclusions as RUP lemmas (checked here; with a proof also written).
    if (!lemmas.empty() && propagated_ < trail_.size() && !propagate()) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
      return true;
    }
    for (size_t i = 0; i < lemmas.size(); i += 2) {
      const Lit pair[2] = {negate(lemmas[i]), negate(lemmas[i + 1])};
      if (!counting_refutes(pair, 2)) {
        st.failure = "a virtual exclusion is not RUP";
        return false;
      }
    }
    if (proof_) {
      for (size_t i = 0; i < lemmas.size(); i += 2) {
        const Lit pair[2] = {negate(lemmas[i]), negate(lemmas[i + 1])};
        proof_->add(pair, 2);
      }
      stats_.counting_lemmas += lemmas.size() / 2;
      // The pigeon clauses as the isolated solver has them: a clause with literals false at the
      // root is replaced by its cells (implied; the longer clause goes with the rest), a clause of
      // two literals of the formula stays (one copy of it).
      std::vector<uint32_t> keep;
      std::vector<uint64_t> keep_bin;
      std::vector<Lit> mine;
      for (uint32_t i = 0; i < pigeons; ++i) {
        mine.clear();
        for (uint32_t h = 0; h < holes; ++h) {
          if (st.cell[size_t{i} * holes + h] != kNoLit) mine.push_back(st.cell[size_t{i} * holes + h]);
        }
        if (st.longs[i] == kNone) {
          keep_bin.push_back(uint64_t{std::min(mine[0], mine[1])} << 32 | std::max(mine[0], mine[1]));
        } else if (clause(st.longs[i]).size == mine.size()) {
          keep.push_back(st.longs[i]);
        } else {
          proof_->add(mine.data(), mine.size());
          ++stats_.counting_lemmas;
        }
      }
      // Delete every other clause, then the isolated refutation. The PR checks need the other
      // clauses on the subsystem's variables gone (the checker then sees the subsystem only, as
      // the isolated solver did); the rest goes too, since dpr-trim and cake_lpr visit every
      // clause of the formula for each PR clause.
      std::sort(keep.begin(), keep.end());
      std::sort(keep_bin.begin(), keep_bin.end());
      std::vector<uint8_t> kept(keep_bin.size(), 0);
      for (const uint32_t ref : clauses_) {
        const Clause& c = clause(ref);
        if (c.garbage || std::binary_search(keep.begin(), keep.end(), ref)) continue;
        proof_->del(c.lits(), c.size);
      }
      for (Lit l = 0; l < 2 * num_vars_; ++l) {
        for (const Watch& w : watches_[l]) {
          if (!w.binary()) continue;
          const Lit b = w.blit;
          if (b < l) continue;  // (deleted from b's list)
          if (in_subsystem(negate(l), negate(b))) continue;
          const auto it = std::lower_bound(keep_bin.begin(), keep_bin.end(), uint64_t{l} << 32 | b);
          if (it != keep_bin.end() && *it == (uint64_t{l} << 32 | b) && !kept[it - keep_bin.begin()]) {
            kept[it - keep_bin.begin()] = 1;
            continue;
          }
          const Lit pair[2] = {l, b};
          proof_->del(pair, 2);
        }
      }
      proof_->raw(buffer.data(), buffer.size(), iso_proof.added(), iso_proof.deleted(), iso_proof.pr(),
                  iso_proof.deleted_bytes());
    }
  }
  stats_.counting_pr += iso.stats().counting_pr;
  stats_.counting_units += iso.stats().counting_units;
  stats_.counting_lemmas += iso.stats().counting_lemmas;
  counting_added_ = true;
  inconsistent_ = true;
  return true;
}


// Relativized pigeonhole (rphp_p<n>_r<n>): n pigeons rest at n places (pp[i][u]: at least one
// place per pigeon; a place hosts at most one pigeon), a place in use (pp[i][u] -> used[u]) maps to
// one of h holes ((-used[u] v qq[u][0] v .. v qq[u][h-1])), two places in use not to the same hole
// ((-used[u] v -used[v] v -qq[u][k] v -qq[v][k])); h < n. Recognised from the clauses; the PR
// checks decide whether the plan goes through.
bool Solver::counting_detect_rphp(CountingState& st) {
  const size_t nv = num_vars_, nl = 2 * nv;
  const uint64_t cap = st.work + 2 * (arena_.size() + 2 * binaries_irredundant_) + 2'000'000;
  constexpr uint32_t kNone = UINT32_MAX, kMulti = UINT32_MAX - 1;
  // 1. Pigeon clauses: long clauses whose literals each have two or more binary clauses (an
  //    exclusion and the implication of the place's in-use literal).
  std::vector<uint32_t> owner(nl, kNone), cand;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    if (++st.work > cap) return false;
    const Lit* lits = c.lits();
    bool ok = true;
    for (uint32_t k = 0; k < c.size && ok; ++k) ok = !vals_[lits[k]] && watches_[negate(lits[k])].size() >= 2;
    for (uint32_t k = 0; k < c.size && ok; ++k) {
      uint32_t cnt = 0;
      for (const Watch& w : watches_[negate(lits[k])]) cnt += w.binary() && !w.redundant_binary();
      st.work += watches_[negate(lits[k])].size() / 4 + 1;
      ok = cnt >= 2;
    }
    if (!ok) continue;
    const auto idx = static_cast<uint32_t>(cand.size());
    cand.push_back(ref);
    for (uint32_t k = 0; k < c.size; ++k) owner[lits[k]] = owner[lits[k]] == kNone ? idx : kMulti;
  }
  if (cand.size() < 4 || st.work > cap) return false;
  // Places: classes of pigeon literals joined across clauses by exclusions; the pigeons: the
  // largest system of clauses joined through classes.
  std::vector<uint32_t> up(nl);
  std::iota(up.begin(), up.end(), 0u);
  auto find = [](std::vector<uint32_t>& u, uint32_t x) {
    while (u[x] != x) x = u[x] = u[u[x]];
    return x;
  };
  for (uint32_t idx = 0; idx < cand.size(); ++idx) {
    const Clause& c = clause(cand[idx]);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (owner[x] != idx) continue;
      for (const Watch& w : watches_[negate(x)]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const Lit y = negate(w.blit);
        if (owner[y] < kMulti && owner[y] != idx) up[find(up, x)] = find(up, y);
      }
      st.work += watches_[negate(x)].size() / 4 + 1;
    }
  }
  if (st.work > cap) return false;
  std::vector<uint32_t> cup(cand.size()), first_clause(nl, kNone), members(cand.size(), 0);
  std::iota(cup.begin(), cup.end(), 0u);
  for (uint32_t idx = 0; idx < cand.size(); ++idx) {
    const Clause& c = clause(cand[idx]);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (owner[x] != idx) continue;
      const uint32_t r = find(up, x);
      if (first_clause[r] == kNone) {
        first_clause[r] = idx;
      } else {
        cup[find(cup, idx)] = find(cup, first_clause[r]);
      }
    }
  }
  for (uint32_t idx = 0; idx < cand.size(); ++idx) ++members[find(cup, idx)];
  uint32_t best = kNone;
  for (uint32_t idx = 0; idx < cand.size(); ++idx) {
    if (members[idx] >= 4 && (best == kNone || members[idx] > members[best])) best = idx;
  }
  if (best == kNone) return false;
  std::vector<uint32_t> pigeons;
  for (uint32_t idx = 0; idx < cand.size(); ++idx) {
    if (find(cup, idx) == best) pigeons.push_back(idx);
  }
  const auto n = static_cast<uint32_t>(pigeons.size());
  const uint32_t nplaces = clause(cand[pigeons[0]]).size;
  if (nplaces < n) return false;
  std::vector<uint32_t> place_of_root(nl, kNone), place(nl, kNone);  // place: literal -> pigeon * places + place
  st.pp.assign(size_t{n} * nplaces, kNoLit);
  uint32_t places = 0;
  for (uint32_t i = 0; i < n; ++i) {
    const Clause& c = clause(cand[pigeons[i]]);
    if (c.size != nplaces) return false;
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (owner[x] != pigeons[i]) return false;
      const uint32_t r = find(up, x);
      if (place_of_root[r] == kNone) {
        if (places == nplaces) return false;
        place_of_root[r] = places++;
      }
      const uint32_t u = place_of_root[r];
      if (st.pp[size_t{i} * nplaces + u] != kNoLit) return false;
      st.pp[size_t{i} * nplaces + u] = x;
      place[x] = i * nplaces + u;
    }
  }
  if (places != nplaces) return false;
  // A place hosts at most one pigeon; every pigeon literal of a place implies the same literal,
  // the place's "in use".
  // (a_rphp of the SAT Competition 2018: some places have a second such literal, with further
  // clauses that exclude it against the in-use literals of other places. The in-use literal is
  // then the one with a hole clause: a clause with its negation and otherwise only variables
  // that are neither pigeon variables nor such literals.)
  std::vector<uint32_t> used_place(nl, kNone);
  st.used.assign(nplaces, kNoLit);
  std::vector<std::vector<Lit>> implied(nplaces);  // per place: implied by each of its pigeon literals
  std::vector<Lit> mine;
  bool choice = false;
  for (uint32_t u = 0; u < nplaces; ++u) {
    for (uint32_t i = 0; i < n; ++i) {
      const Lit x = st.pp[size_t{i} * nplaces + u];
      uint32_t excl = 0;
      mine.clear();
      for (const Watch& w : watches_[negate(x)]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const uint32_t pl = place[negate(w.blit)];
        if (pl != kNone && pl % nplaces == u && pl / nplaces != i) {
          ++excl;
        } else {
          mine.push_back(w.blit);
        }
      }
      st.work += watches_[negate(x)].size() / 4 + 1;
      if (excl < n - 1) return false;
      std::sort(mine.begin(), mine.end());
      mine.erase(std::unique(mine.begin(), mine.end()), mine.end());
      if (i == 0) {
        implied[u] = mine;
      } else {
        std::vector<Lit> both;
        std::set_intersection(implied[u].begin(), implied[u].end(), mine.begin(), mine.end(), std::back_inserter(both));
        if (both.size() != mine.size() || both.size() != implied[u].size()) return false;  // (the same for every pigeon)
      }
    }
    if (implied[u].empty()) return false;
    for (const Lit c : implied[u]) {
      if (place[c] != kNone || place[negate(c)] != kNone) return false;
    }
    choice = choice || implied[u].size() > 1;
  }
  if (!choice) {
    for (uint32_t u = 0; u < nplaces; ++u) {
      const Lit c = implied[u][0];
      if (used_place[c] != kNone) return false;
      st.used[u] = c;
      used_place[c] = u;
    }
  } else {
    std::vector<uint32_t> cand_place(nl, kNone);  // candidate literal -> its place
    std::vector<uint8_t> cand_var(nv, 0);
    for (uint32_t u = 0; u < nplaces; ++u) {
      for (const Lit c : implied[u]) {
        if (cand_place[c] != kNone || cand_place[negate(c)] != kNone) return false;
        cand_place[c] = u;
        cand_var[var_of(c)] = 1;
      }
    }
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant || c.size < 4) continue;
      if (++st.work > cap) return false;
      Lit head = kNoLit;
      bool ok = true;
      for (uint32_t k = 0; k < c.size && ok; ++k) {
        const Lit x = c.lits()[k];
        if (cand_place[negate(x)] != kNone && head == kNoLit) {
          head = negate(x);
        } else {
          ok = !cand_var[var_of(x)] && place[x] == kNone && place[negate(x)] == kNone;
        }
      }
      st.work += c.size / 4;
      if (!ok || head == kNoLit) continue;
      const uint32_t u = cand_place[head];
      if (st.used[u] != kNoLit && st.used[u] != head) return false;
      st.used[u] = head;
      used_place[head] = u;
    }
    for (uint32_t u = 0; u < nplaces; ++u) {
      if (st.used[u] == kNoLit) return false;
    }
  }
  // Variables of pigeon literals and of the other literals implied by them: no hole clause has one.
  std::vector<uint8_t> not_hole(nv, 0);
  for (const Lit x : st.pp) not_hole[var_of(x)] = 1;
  for (uint32_t u = 0; u < nplaces; ++u) {
    for (const Lit c : implied[u]) {
      if (c != st.used[u]) not_hole[var_of(c)] = 1;
    }
  }
  // Hole clauses (-used[u] v holes of u) and hole classes from the clauses
  // (-used[u] v -used[v] v -a v -b), a and b holes of u and v.
  std::vector<uint32_t> hole_clause(nplaces, kNone), hole_owner(nl, kNone);
  uint32_t holes = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size < 3) continue;
    if (++st.work > cap) return false;
    uint32_t u = kNone, uses = 0;
    for (uint32_t k = 0; k < c.size; ++k) {
      const uint32_t pl = used_place[negate(c.lits()[k])];
      if (pl != kNone) {
        u = pl;
        ++uses;
      }
    }
    if (uses != 1 || c.size < 4) continue;
    if (choice) {  // (the further clauses of a second in-use literal are no hole clauses)
      bool other = false;
      for (uint32_t k = 0; k < c.size && !other; ++k) other = not_hole[var_of(c.lits()[k])] != 0;
      if (other) continue;
    }
    if (hole_clause[u] != kNone) return false;
    hole_clause[u] = ref;
    if (!holes) holes = c.size - 1;
    if (c.size - 1 != holes) return false;
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (x == negate(st.used[u])) continue;
      if (vals_[x] || hole_owner[x] != kNone || place[x] != kNone || place[negate(x)] != kNone) return false;
      hole_owner[x] = u;
    }
  }
  if (!holes || holes >= n) return false;
  std::vector<uint32_t> hu(nl);
  std::iota(hu.begin(), hu.end(), 0u);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size != 4) continue;
    if (++st.work > cap) return false;
    Lit h[2];
    uint32_t nh = 0, uses = 0;
    for (uint32_t k = 0; k < 4; ++k) {
      const Lit y = negate(c.lits()[k]);
      if (used_place[y] != kNone) {
        ++uses;
      } else if (hole_owner[y] != kNone && nh < 2) {
        h[nh++] = y;
      }
    }
    if (uses == 2 && nh == 2 && hole_owner[h[0]] != hole_owner[h[1]]) hu[find(hu, h[0])] = find(hu, h[1]);
  }
  std::vector<uint32_t> hole_of_root(nl, kNone);
  st.qq.assign(size_t{nplaces} * holes, kNoLit);
  for (uint32_t u = 0; u < nplaces; ++u) {
    if (hole_clause[u] == kNone) return false;
    const Clause& c = clause(hole_clause[u]);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (x == negate(st.used[u])) continue;
      const uint32_t r = find(hu, x);
      if (u == 0) {
        if (hole_of_root[r] != kNone) return false;
        hole_of_root[r] = k;  // (renumbered below)
      }
      if (hole_of_root[r] == kNone) return false;
    }
  }
  // Hole indices 0..holes-1 in the order of place 0's hole clause.
  {
    const Clause& c0 = clause(hole_clause[0]);
    uint32_t next = 0;
    for (uint32_t k = 0; k < c0.size; ++k) {
      const Lit x = c0.lits()[k];
      if (x != negate(st.used[0])) hole_of_root[find(hu, x)] = next++;
    }
  }
  for (uint32_t u = 0; u < nplaces; ++u) {
    const Clause& c = clause(hole_clause[u]);
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit x = c.lits()[k];
      if (x == negate(st.used[u])) continue;
      Lit& slot = st.qq[size_t{u} * holes + hole_of_root[find(hu, x)]];
      if (slot != kNoLit) return false;
      slot = x;
    }
  }
  st.kind = kRphp;
  st.relativized = true;
  st.pigeons = n;
  st.holes = holes;
  st.vertices = nplaces;
  st.vars.clear();
  for (const Lit x : st.pp) st.vars.push_back(var_of(x));
  for (const Lit x : st.qq) st.vars.push_back(var_of(x));
  std::sort(st.vars.begin(), st.vars.end());
  if (std::adjacent_find(st.vars.begin(), st.vars.end()) != st.vars.end()) return false;
  for (const Lit x : st.used) st.extra_vars.push_back(var_of(x));
  st.all_vars = st.vars.size();
  for (const Var v : st.vars) {
    st.degree_sum += watches_[make_lit(v, false)].size() + watches_[make_lit(v, true)].size();
    st.long_sum += nplaces + holes;
  }
  if (nplaces == n) {
    for (uint64_t m = 1; m < n; ++m) {
      st.steps_pr += m * m;
      st.steps_units += m;
    }
    for (uint64_t m = 1; m <= holes; ++m) {
      st.steps_pr += m * (m - 1);
      st.steps_units += m;
    }
    return true;
  }
  // More places than pigeons: not every place is in use; the clique-colouring plan with the
  // pigeons as positions, the places as vertices and the holes as colours (pigeons swap places).
  st.kind = kClique;
  st.positions = n;
  st.colours = holes;
  st.q = st.pp;
  st.r = st.qq;
  const uint64_t pairs = uint64_t{nplaces} * (nplaces - 1);
  for (uint64_t lvl = 1; lvl <= holes; ++lvl) {
    st.steps_pr += lvl * (lvl - 1) * pairs;
    st.steps_units += lvl * (pairs + nplaces);
  }
  st.steps_units += nplaces;
  return true;
}

// Virtual exclusions: at-most-one constraints over auxiliary variables (sequential counters,
// ladders, commander and product encodings) have no binary clause (-x v -y), but x implies -y
// through binary clauses over the auxiliary variables, so (-x v -y) is RUP. Each literal of a long
// clause (one of the candidate pigeons) is assumed and propagated over the binary clauses only
// (read-only: the solver's watches and values are not touched; these encodings need no longer
// clause for the exclusion), and the literals of long clauses it falsifies without a binary
// clause between them are recorded, both ways. Bounded: a quarter of a pass over the clauses, 4096
// implied literals per probe; stops after the first 64 probes unless one of them found two such
// exclusions with literals of other long clauses.
bool Solver::counting_virtual(CountingState& st) {
  const size_t nl = 2 * size_t{num_vars_};
  const uint64_t cap = st.work + (arena_.size() + 2 * binaries_irredundant_) / 4 + 1'000'000;
  constexpr uint32_t kMulti = UINT32_MAX - 1;
  // Candidate literals: those of long clauses without assigned literals (and their clause).
  std::vector<uint32_t> owner(nl, UINT32_MAX);
  std::vector<uint32_t> longs;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size > 4096) continue;
    if (++st.work > cap) return false;
    bool free = true;
    for (uint32_t k = 0; k < c.size && free; ++k) free = !vals_[c.lits()[k]];
    if (!free) continue;
    const auto idx = static_cast<uint32_t>(longs.size());
    longs.push_back(ref);
    for (uint32_t k = 0; k < c.size; ++k) {
      uint32_t& o = owner[c.lits()[k]];
      o = o == UINT32_MAX ? idx : kMulti;
    }
  }
  if (longs.size() < 4) return false;
  std::vector<int8_t> val(vals_.begin(), vals_.end());
  std::vector<Lit> trail;
  std::vector<uint8_t> probed(nl, 0);
  std::vector<uint32_t> direct(nl, 0);  // stamp: excluded by a binary clause
  std::vector<uint32_t> excluded(nl, 0);  // per probed literal: literals of long clauses it excludes
  std::vector<std::pair<Lit, Lit>> pairs;
  uint64_t probes = 0, useful = 0;
  bool stop = false;
  for (uint32_t i = 0; i < longs.size() && !stop; ++i) {
    const Clause& c0 = clause(longs[i]);
    for (uint32_t k = 0; k < c0.size; ++k) {
      const Lit x = c0.lits()[k];
      if (probed[x]) continue;
      probed[x] = 1;
      if (st.work > cap || (probes >= 64 && !useful) || pairs.size() > 4'000'000) {  // (what was found so far)
        stop = true;
        break;
      }
      ++probes;
      // Propagate x over the binary clauses.
      trail.assign(1, x);
      val[x] = 1;
      val[negate(x)] = -1;
      bool conflict = false;
      for (size_t head = 0; head < trail.size() && !conflict && trail.size() < 4096; ++head) {
        const Lit f = negate(trail[head]);
        for (const Watch& w : watches_[f]) {  // binary clauses (f v b): b
          if (!w.binary() || w.redundant_binary()) continue;
          const int8_t v = val[w.blit];
          if (v > 0) continue;
          if (v < 0) {
            conflict = true;
            break;
          }
          val[w.blit] = 1;
          val[negate(w.blit)] = -1;
          trail.push_back(w.blit);
        }
        st.work += watches_[f].size() / 4 + 1;
      }
      if (!conflict) {
        const auto stamp = static_cast<uint32_t>(probes);
        for (const Watch& w : watches_[negate(x)]) {
          if (!w.binary() || w.redundant_binary()) continue;
          direct[negate(w.blit)] = stamp;
          excluded[x] += owner[negate(w.blit)] != UINT32_MAX;
        }
        uint32_t others = 0;
        for (size_t m = 1; m < trail.size(); ++m) {
          const Lit y = negate(trail[m]);
          if (owner[y] == UINT32_MAX || y == negate(x) || direct[y] == stamp) continue;
          pairs.emplace_back(x, y);
          ++excluded[x];
          others += owner[y] != owner[x] || owner[x] == kMulti;  // (in two clauses: counted)
        }
        useful += others >= 2;
      }
      for (const Lit t : trail) val[t] = val[negate(t)] = 0;
    }
  }
  if (pairs.empty() || !useful) return false;
  // A pigeon of a pigeonhole with s holes excludes at least s literals with each of its literals:
  // without four such clauses no detection follows.
  uint32_t pigeons = 0;
  for (uint32_t i = 0; i < longs.size() && pigeons < 4; ++i) {
    const Clause& c = clause(longs[i]);
    bool ok = true;
    for (uint32_t k = 0; k < c.size && ok; ++k) ok = probed[c.lits()[k]] && excluded[c.lits()[k]] >= c.size;
    pigeons += ok;
  }
  if (pigeons < 4) return false;
  // Both directions, deduplicated.
  const size_t n = pairs.size();
  for (size_t i = 0; i < n; ++i) pairs.emplace_back(pairs[i].second, pairs[i].first);
  std::sort(pairs.begin(), pairs.end());
  pairs.erase(std::unique(pairs.begin(), pairs.end()), pairs.end());
  st.voff.assign(nl + 1, 0);
  for (const auto& pr : pairs) ++st.voff[pr.first + 1];
  for (size_t l = 0; l < nl; ++l) st.voff[l + 1] += st.voff[l];
  st.vlit.resize(pairs.size());
  for (size_t i = 0; i < pairs.size(); ++i) st.vlit[i] = pairs[i].second;
  st.virt = true;
  st.work += pairs.size();
  return true;
}

// True if propagating the negations of lits[0..n) on a new decision level gives a conflict (also
// when one of them is true already). Backtracks to the current level.
bool Solver::counting_refutes(const Lit* lits, size_t n) {
  control_.push_back(static_cast<uint32_t>(trail_.size()));
  bool conflict = false;
  for (size_t i = 0; i < n && !conflict; ++i) {
    const int8_t v = vals_[lits[i]];
    if (v > 0) {
      conflict = true;
    } else if (!v) {
      assign(negate(lits[i]), kNoReason);
    }
  }
  if (!conflict) conflict = !propagate();
  backtrack(level() - 1);
  return conflict;
}

// True if the clause lits[0..n) is implied under the current assignment (a decision level above
// the root): a clause in the shortest occurrence list of its literals has all its literals false
// or in lits (assigning their negations falsifies it; usually the image of the checked clause
// under the witness's swap), or else propagating the negations gives a conflict.
bool Solver::counting_implied(CountingState& st, const Lit* lits, size_t n) {
  const std::vector<uint32_t>* shortest = nullptr;
  for (size_t i = 0; i < n; ++i) {
    const std::vector<uint32_t>* o = st.occ_of(lits[i]);
    if (o && (!shortest || o->size() < shortest->size())) shortest = o;
  }
  bool found = false;
  if (shortest) {
    for (size_t i = 0; i < n; ++i) st.mark[lits[i]] |= 2;
    for (const uint32_t ref : *shortest) {
      const Clause& d = clause(ref);
      if (d.garbage) continue;
      bool all = true;
      for (uint32_t j = 0; j < d.size && all; ++j) all = (st.mark[d.lits()[j]] & 2) || vals_[d.lits()[j]] < 0;
      st.work += d.size / 2 + 1;
      if (all) {
        found = true;
        break;
      }
    }
    for (size_t i = 0; i < n; ++i) st.mark[lits[i]] &= static_cast<uint8_t>(~2u);
  }
  return found || counting_refutes(lits, n);
}

bool Solver::counting_check_pr(CountingState& st, const Lit* c, size_t nc, const Lit* w, size_t nw) {
  // The witness: distinct, consistent literals of structure variables, the first one the clause's
  // first literal, none false at the root.
  if (!nw || w[0] != c[0]) {
    st.failure = "witness does not start with the clause's first literal";
    return false;
  }
  for (size_t i = 0; i < nw; ++i) {
    if (vals_[w[i]] < 0) {
      st.failure = "witness literal false at the root";
      return false;
    }
    if (!st.occ_of(w[i])) {
      st.failure = "witness literal outside the structure";
      return false;
    }
    for (size_t j = i + 1; j < nw; ++j) {
      if (var_of(w[i]) == var_of(w[j])) {
        st.failure = "witness repeats a variable";
        return false;
      }
    }
  }
  // A: the negation of the clause, propagated at decision level 1. A conflict: C is RUP.
  control_.push_back(static_cast<uint32_t>(trail_.size()));
  for (size_t i = 0; i < nc; ++i) {
    if (!vals_[c[i]]) assign(negate(c[i]), kNoReason);
  }
  if (!propagate()) {
    backtrack(0);
    return true;
  }
  for (size_t i = 0; i < nw; ++i) st.mark[w[i]] |= 1;
  bool ok = true;
  for (size_t i = 0; i < nw && ok; ++i) {
    const Lit nl = negate(w[i]);
    // Binary clauses (nl v o): copied first (propagation reorders the watch lists).
    st.others.clear();
    for (const Watch& x : watches_[nl]) {
      if (x.binary()) st.others.push_back(x.blit);
    }
    st.work += watches_[nl].size() / 4 + 1;
    for (const Lit o : st.others) {
      if (st.mark[o] & 1) continue;  // satisfied by the witness
      if (st.mark[negate(o)] & 1) {  // reduced to the empty clause
        ok = false;
        break;
      }
      const int8_t v = vals_[o];
      if (v > 0) continue;  // true under A
      if (v < 0 || !counting_implied(st, &o, 1)) {
        ok = false;
        break;
      }
    }
    // Long clauses with nl (by index: the list does not change during the check).
    const std::vector<uint32_t>& occ = *st.occ_of(nl);
    for (size_t k = 0; ok && k < occ.size(); ++k) {
      const Clause& d = clause(occ[k]);
      if (d.garbage) continue;
      st.rest.clear();
      bool sat = false;
      for (uint32_t j = 0; j < d.size && !sat; ++j) {
        const Lit x = d.lits()[j];
        if (st.mark[x] & 1) {
          sat = true;  // satisfied by the witness
        } else if (st.mark[negate(x)] & 1) {
          continue;  // removed by the witness
        } else if (vals_[x] > 0) {
          sat = true;  // true under A
        } else if (!vals_[x]) {
          st.rest.push_back(x);
        }
      }
      st.work += d.size;
      if (sat) continue;
      if (st.rest.empty() || !counting_implied(st, st.rest.data(), st.rest.size())) ok = false;
    }
  }
  for (size_t i = 0; i < nw; ++i) st.mark[w[i]] &= static_cast<uint8_t>(~1u);
  backtrack(0);
  if (!ok) st.failure = "PR check";
  return ok;
}

// Adds the clause c[0..nc) to the formula and the proof: a PR clause with the witness w[0..nw), or,
// without a witness, a RUP clause (a unit is assigned at the root). Each is checked first; false
// if the check fails (nothing written).
bool Solver::counting_add(CountingState& st, const Lit* c, size_t nc, const Lit* w, size_t nw) {
  for (size_t i = 0; i < nc; ++i) {
    if (vals_[c[i]] > 0) return true;  // satisfied at the root: not needed
  }
  for (size_t i = 0; i < nc; ++i) {
    if (vals_[c[i]] < 0) {
      st.failure = "clause literal false at the root";
      return false;
    }
  }
  // Fault injection (--countingfault, tests): a wrong witness that the check has to refuse.
  Lit faulty[8];
  if (nw >= 3 && nw <= 8 && opts_.countingfault && ++st.steps_tried == static_cast<uint64_t>(opts_.countingfault)) {
    std::copy(w, w + nw, faulty);
    faulty[2] = negate(faulty[2]);
    w = faulty;
  }
  if (nw) {
    if (!counting_check_pr(st, c, nc, w, nw)) return false;
  } else if (!counting_refutes(c, nc)) {
    st.failure = "RUP check";
    return false;
  }
  if (proof_) {
    if (nw) {
      proof_->add_pr(c, nc, w, nw);
    } else if (nc > 1) {
      proof_->add(c, nc);  // (a unit is written when it is assigned)
    }
    if (nc >= 3) {
      st.round.push_back(static_cast<Lit>(nc));
      st.round.insert(st.round.end(), c, c + nc);
    }
  }
  counting_added_ = true;
  if (nw) {
    ++stats_.counting_pr;
  } else if (nc == 1) {
    ++stats_.counting_units;
  } else {
    ++stats_.counting_lemmas;
  }
  if (nc == 1) {
    assign(c[0], kNoReason);  // at the root: written to the proof
    if (!propagate()) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
    }
  } else if (nc == 2) {
    add_binary(c[0], c[1], false);
  } else {
    const uint32_t ref = new_clause(c, static_cast<uint32_t>(nc), false, 0, true);
    for (size_t i = 0; i < nc; ++i) {
      if (std::vector<uint32_t>* o = st.occ_of(c[i])) o->push_back(ref);
    }
  }
  return true;
}

bool Solver::counting_add_unit(CountingState& st, Lit u) {
  if (vals_[u] > 0) return true;  // implied at the root (and in the proof) already
  if (vals_[u] < 0) {
    st.failure = "RUP check of a unit";
    return false;
  }
  return counting_add(st, &u, 1, nullptr, 0);
}

// Long clauses split into short ones (e_rphp, ae_rphp of the SAT Competition 2018: every clause of
// a relativized pigeonhole cut into clauses of three literals, chained by auxiliary variables)
// hide a structure from the detectors. An auxiliary variable of such a chain occurs in two clauses
// of three or more literals, once with each sign, and nowhere else; resolving the two gives the
// clause back. If no structure was found and at least a tenth of the variables are of that kind,
// the detection is tried on a copy of the formula with them eliminated (a separate solver; this
// one is not touched). Only if the copy is refuted by a counting certificate, the proof gets the
// eliminations (each resolvent is RUP, then its two parents are deleted) followed by the copy's
// refutation. Not after units or learned clauses (the copy must be the formula the checker has).
bool Solver::counting_collapse(CountingState& st) {
  if (!trail_.empty() || redundant_ || binaries_redundant_ || input_shortened_) return false;
  const size_t nv = num_vars_, nl = 2 * nv;
  std::vector<uint32_t> count(nl, 0);
  uint64_t literals = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    for (uint32_t k = 0; k < c.size; ++k) ++count[c.lits()[k]];
    literals += c.size;
  }
  st.work += literals / 4 + clauses_.size();
  if (literals > 50'000'000) return false;
  std::vector<uint8_t> aux(nv, 0);
  uint32_t candidates = 0;
  for (Var v = 0; v < nv; ++v) {
    const Lit x = make_lit(v, false);
    if (count[x] != 1 || count[negate(x)] != 1) continue;
    bool binary = false;
    for (const Lit y : {x, negate(x)}) {
      for (const Watch& w : watches_[y]) binary = binary || w.binary();
    }
    if (binary) continue;
    aux[v] = 1;
    ++candidates;
  }
  st.work += nv;
  if (candidates < 16 || candidates < nv / 10) return false;
  // The copy's long clauses, and for each candidate the two clauses it is in.
  std::vector<std::vector<Lit>> cls;
  std::vector<uint8_t> dead;
  std::vector<uint32_t> at(nl, UINT32_MAX);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    const auto idx = static_cast<uint32_t>(cls.size());
    cls.emplace_back(c.lits(), c.lits() + c.size);
    for (const Lit x : cls.back()) {
      if (aux[var_of(x)]) at[x] = idx;
    }
  }
  dead.assign(cls.size(), 0);
  struct Step {
    uint32_t pos, neg, res;
  };
  std::vector<Step> steps;
  std::vector<uint8_t> seen(nl, 0);
  for (Var v = 0; v < nv; ++v) {
    if (!aux[v]) continue;
    const Lit x = make_lit(v, false);
    const uint32_t i = at[x], j = at[negate(x)];
    if (i == j || cls[i].size() < 3 || cls[j].size() < 3) continue;
    std::vector<Lit> res;
    bool ok = true;
    for (const uint32_t k : {i, j}) {
      for (const Lit y : cls[k]) {
        if (var_of(y) == v) continue;
        if (seen[y] || seen[negate(y)]) ok = false;  // a repeated literal or a tautology: left alone
        seen[y] = 1;
        res.push_back(y);
      }
    }
    for (const Lit y : res) seen[y] = 0;
    st.work += res.size();
    if (!ok) continue;
    const auto idx = static_cast<uint32_t>(cls.size());
    for (const Lit y : res) {
      if (aux[var_of(y)]) at[y] = idx;
    }
    cls.push_back(std::move(res));
    dead.push_back(0);
    dead[i] = dead[j] = 1;
    steps.push_back({i, j, idx});
  }
  if (steps.size() < 16 || steps.size() < nv / 10) return false;
  // The copy: the same variables (its proof lines are written in the input numbering).
  std::vector<Lit> to_main(nl);
  for (Lit l = 0; l < nl; ++l) to_main[l] = external_lit(l);
  Options o = opts_;
  o.counting = 1;
  o.countingcollapse = 0;
  o.lucky = 0;
  o.verbose = 0;
  o.cardinality = 0;
  o.renumber = 0;
  o.linmod = 0;
  o.xorsub = 0;
  Solver iso(o);
  iso.start_ = start_;  // (the same clock, time limit and terminate flag: see stop_requested())
  iso.time_limit_ = time_limit_;
  iso.terminate_ = terminate_;
  std::string buffer;
  ProofWriter iso_proof([&buffer](const char* d, size_t n) { buffer.append(d, n); }, proof_ ? proof_->binary() : true);
  // (the copy's own isolated refutations write their lines through external_lit(): the same map)
  iso.outer_map_ = &to_main;
  iso_proof.set_map(&to_main);
  if (proof_) iso.set_proof(&iso_proof);
  iso.reserve(static_cast<int>(nv));
  auto dimacs = [](Lit l) { return is_negative(l) ? -static_cast<int>(var_of(l) + 1) : static_cast<int>(var_of(l) + 1); };
  std::vector<int> cl;
  for (size_t k = 0; k < cls.size(); ++k) {
    if (dead[k]) continue;
    cl.clear();
    for (const Lit y : cls[k]) cl.push_back(dimacs(y));
    iso.add_clause(cl.data(), cl.size());
    st.work += cl.size();
  }
  for (Lit l = 0; l < nl; ++l) {
    for (const Watch& w : watches_[l]) {
      if (!w.binary() || w.blit < l) continue;  // (once, from the smaller literal's list)
      const int bin[2] = {dimacs(l), dimacs(w.blit)};
      iso.add_clause(bin, 2);
    }
  }
  iso.set_conflict_limit(0);
  const int res = iso.solve();
  stop_after(iso);
  st.work += iso.stats().counting_work;  // (booked with this solver's counting work by the caller)
  if (res != kUnsat || !iso.stats().counting_found || iso.stats().conflicts) return false;
  if (proof_) {
    iso_proof.flush();
    for (const Step& t : steps) {
      proof_->add(cls[t.res].data(), cls[t.res].size());
      proof_->del(cls[t.pos].data(), cls[t.pos].size());
      proof_->del(cls[t.neg].data(), cls[t.neg].size());
    }
    proof_->raw(buffer.data(), buffer.size(), iso_proof.added(), iso_proof.deleted(), iso_proof.pr(),
                iso_proof.deleted_bytes());
  }
  ++stats_.counting_found;
  stats_.counting_pr += iso.stats().counting_pr;
  stats_.counting_units += iso.stats().counting_units;
  stats_.counting_lemmas += iso.stats().counting_lemmas + steps.size();
  counting_desc_ = iso.counting_desc_ + ", after eliminating " + std::to_string(steps.size()) + " variables with two occurrences";
  counting_added_ = true;
  inconsistent_ = true;
  return true;
}

// Refutation by extension, for a clique-colouring or a relativized pigeonhole with more places than
// pigeons whose own plan is over budget (its PR clauses grow with the square of the vertices or
// places). Pigeons i (positions), intermediates u (vertices, places) and holes k (colours):
// P[i][u] = st.q, Q[u][k] = st.r, and "u is taken" O[u] (the in-use literal of a place; for a
// vertex a new variable o[u] = OR_i P[i][u]). New variables from `base` on, each defined by
// clauses that are RAT on it:
//   w[u][k] = O[u] and Q[u][k]            (the taken intermediate u has hole k)
//   z[i][u][k] = P[i][u] and w[u][k]      (pigeon i, by way of u, has hole k)
//   y[i][k] = OR_u z[i][u][k]             (pigeon i has hole k)
// for the pigeons i <= holes only. RUP lemmas then give a plain pigeonhole on y:
//   clique-colouring: (-P[i][u] v -o[v] v -Q[u][k] v -Q[v][k]), u != v (another position at v
//     makes u and v adjacent);
//   (-w[u][k] v -w[v][k]), u < v;
//   (-z[i][u][k] v -y[j][k]), i != j;  then (-y[i][k] v -y[j][k]);
//   (-P[i][u] v y[i][0] v .. v y[i][h-1]);  then (y[i][0] v .. v y[i][h-1]).
// Every other clause with a y variable is then deleted (the swap witnesses of the pigeonhole plan
// would falsify the definitions), and st becomes the pigeonhole of holes + 1 pigeons on y, which
// counting_certify refutes. Each step is checked on the clauses before it is written; a failed
// check leaves definitions and implied lemmas behind, and the search goes on.
bool Solver::counting_extend(CountingState& st, uint32_t base) {
  const uint32_t n = st.positions, r = st.vertices, h = st.colours, m = h + 1;
  const bool rel = st.relativized;
  auto P = [&](uint32_t i, uint32_t u) { return st.q[size_t{i} * r + u]; };
  auto Q = [&](uint32_t u, uint32_t k) { return st.r[size_t{u} * h + k]; };
  const uint32_t o0 = base, w0 = o0 + (rel ? 0 : r), z0 = w0 + r * h, y0 = z0 + m * r * h;
  auto O = [&](uint32_t u) { return rel ? st.used[u] : make_lit(o0 + u, false); };
  auto W = [&](uint32_t u, uint32_t k) { return make_lit(w0 + u * h + k, false); };
  auto Z = [&](uint32_t i, uint32_t u, uint32_t k) { return make_lit(z0 + (i * r + u) * h + k, false); };
  auto Y = [&](uint32_t i, uint32_t k) { return make_lit(y0 + i * h + k, false); };
  auto over = [&]() {
    if (st.work + (stats_.ticks - st.ticks0) > st.limit) {
      st.failure = "budget";
      return true;
    }
    if (stop_requested()) {
      st.failure = "stopped (time limit or interrupted)";
      return true;
    }
    return false;
  };
  // A definition clause: RAT on its first literal (checked as a PR clause with that witness).
  auto define = [&](const Lit* d, size_t nd) {
    if (!counting_check_pr(st, d, nd, d, 1)) return false;
    if (proof_) proof_->add(d, nd);
    counting_added_ = true;
    ++stats_.counting_lemmas;
    if (nd == 2) {
      add_binary(d[0], d[1], false);
    } else {
      const uint32_t ref = new_clause(d, static_cast<uint32_t>(nd), false, 0, true);
      for (size_t i = 0; i < nd; ++i) {
        if (std::vector<uint32_t>* o = st.occ_of(d[i])) o->push_back(ref);
      }
    }
    return true;
  };
  auto define2 = [&](Lit a, Lit b) {
    const Lit d[2] = {a, b};
    return define(d, 2);
  };
  auto lemma2 = [&](Lit a, Lit b) {
    const Lit d[2] = {a, b};
    return counting_add(st, d, 2, nullptr, 0);
  };
  std::vector<Lit> c;
  std::vector<uint32_t> drop;       // long clauses with a y variable, deleted before the pigeonhole plan
  std::vector<Lit> drop_bin;        // binary ones (pairs)
  auto last_clause = [&](size_t before) {  // the long clause just added, if it was
    if (clauses_.size() == before) {
      if (!st.failure) st.failure = "a lemma was not added";
      return false;
    }
    drop.push_back(clauses_.back());
    return true;
  };
  if (!rel) {  // o[u] = OR_i P[i][u]
    for (uint32_t u = 0; u < r; ++u) {
      if (over()) return false;
      for (uint32_t i = 0; i < n; ++i) {
        if (!define2(O(u), negate(P(i, u)))) return false;
      }
      c.assign(1, negate(O(u)));
      for (uint32_t i = 0; i < n; ++i) c.push_back(P(i, u));
      if (!define(c.data(), c.size())) return false;
    }
  }
  for (uint32_t u = 0; u < r; ++u) {
    if (over()) return false;
    for (uint32_t k = 0; k < h; ++k) {
      const Lit w = W(u, k);
      const Lit d[3] = {w, negate(O(u)), negate(Q(u, k))};
      if (!define2(negate(w), O(u)) || !define2(negate(w), Q(u, k)) || !define(d, 3)) return false;
    }
  }
  for (uint32_t i = 0; i < m; ++i) {
    for (uint32_t u = 0; u < r; ++u) {
      if (over()) return false;
      for (uint32_t k = 0; k < h; ++k) {
        const Lit z = Z(i, u, k);
        const Lit d[3] = {z, negate(P(i, u)), negate(W(u, k))};
        if (!define2(negate(z), P(i, u)) || !define2(negate(z), W(u, k)) || !define(d, 3)) return false;
      }
    }
    for (uint32_t k = 0; k < h; ++k) {
      for (uint32_t u = 0; u < r; ++u) {
        if (!define2(Y(i, k), negate(Z(i, u, k)))) return false;
        drop_bin.push_back(Y(i, k));
        drop_bin.push_back(negate(Z(i, u, k)));
      }
      c.assign(1, negate(Y(i, k)));
      for (uint32_t u = 0; u < r; ++u) c.push_back(Z(i, u, k));
      const size_t before = clauses_.size();
      if (!define(c.data(), c.size()) || !last_clause(before)) return false;
    }
  }
  if (!rel) {
    for (uint32_t i = 0; i < n; ++i) {
      for (uint32_t u = 0; u < r; ++u) {
        if (over()) return false;
        for (uint32_t v = 0; v < r; ++v) {
          if (v == u) continue;
          for (uint32_t k = 0; k < h; ++k) {
            const Lit d[4] = {negate(P(i, u)), negate(O(v)), negate(Q(u, k)), negate(Q(v, k))};
            if (!counting_add(st, d, 4, nullptr, 0)) return false;
          }
        }
      }
    }
  }
  for (uint32_t u = 0; u < r; ++u) {
    if (over()) return false;
    for (uint32_t v = u + 1; v < r; ++v) {
      for (uint32_t k = 0; k < h; ++k) {
        if (!lemma2(negate(W(u, k)), negate(W(v, k)))) return false;
      }
    }
  }
  for (uint32_t i = 0; i < m; ++i) {
    for (uint32_t j = 0; j < m; ++j) {
      if (j == i) continue;
      for (uint32_t u = 0; u < r; ++u) {
        if (over()) return false;
        for (uint32_t k = 0; k < h; ++k) {
          if (!lemma2(negate(Z(i, u, k)), negate(Y(j, k)))) return false;
          drop_bin.push_back(negate(Z(i, u, k)));
          drop_bin.push_back(negate(Y(j, k)));
        }
      }
    }
  }
  for (uint32_t i = 0; i < m; ++i) {
    for (uint32_t j = i + 1; j < m; ++j) {
      for (uint32_t k = 0; k < h; ++k) {
        if (!lemma2(negate(Y(i, k)), negate(Y(j, k)))) return false;
      }
    }
  }
  for (uint32_t i = 0; i < m; ++i) {
    if (over()) return false;
    for (uint32_t u = 0; u < r; ++u) {
      c.assign(1, negate(P(i, u)));
      for (uint32_t k = 0; k < h; ++k) c.push_back(Y(i, k));
      const size_t before = clauses_.size();
      if (!counting_add(st, c.data(), c.size(), nullptr, 0) || !last_clause(before)) return false;
    }
    c.clear();
    for (uint32_t k = 0; k < h; ++k) c.push_back(Y(i, k));
    if (!counting_add(st, c.data(), c.size(), nullptr, 0)) return false;
  }
  for (const uint32_t ref : drop) delete_irredundant(ref);
  for (size_t i = 0; i < drop_bin.size(); i += 2) {
    delete_binary(drop_bin[i], drop_bin[i + 1]);
    --binaries_irredundant_;
  }
  st.round.clear();
  st.kind = kPigeonhole;
  st.pigeons = m;
  st.holes = h;
  st.k = 1;
  st.cell.resize(size_t{m} * h);
  for (uint32_t i = 0; i < m; ++i) {
    for (uint32_t k = 0; k < h; ++k) st.cell[size_t{i} * h + k] = Y(i, k);
  }
  return true;
}

bool Solver::counting_certify(CountingState& st) {
  auto over = [&]() {
    if (st.work + (stats_.ticks - st.ticks0) > st.limit) {
      st.failure = "budget";
      return true;
    }
    if (stop_requested()) {
      st.failure = "stopped (time limit or interrupted)";
      return true;
    }
    return false;
  };
  // At the end of a round (its units derived), the proof drops what the checker no longer needs:
  // dpr-trim and cake_lpr visit every clause of the formula for each PR clause, so the formula
  // they see should shrink as the plan goes on instead of growing by every round's clauses.
  // Dropped: the clauses that the units (and their root propagation) satisfy, the round's PR
  // clauses among them; with `subsumed`, also the round's clauses of three or more literals (the
  // clique-colouring plan: its binary lemmas subsume them). The solver keeps them all (the search
  // goes on unchanged if the plan stops early); ProofWriter::forget leaves out its later deletions.
  // (Not booked as counting work: the budget, and with it the search, must not depend on the proof.)
  st.round.clear();
  st.round_trail = trail_.size();
  auto end_round = [&](bool subsumed) {
    if (!proof_ || inconsistent_) return;
    if (subsumed) {
      for (size_t at = 0; at < st.round.size(); at += st.round[at] + 1) {
        proof_->forget(st.round.data() + at + 1, st.round[at]);
      }
    }
    st.round.clear();
    if (st.dropped.empty()) st.dropped.assign(2 * size_t{num_vars_}, 0);
    for (size_t t = st.round_trail; t < trail_.size(); ++t) {
      const Lit u = trail_[t];
      for (const Watch& w : watches_[u]) {
        if (!w.binary() || st.dropped[w.blit]) continue;  // (dropped with the other literal)
        const Lit bin[2] = {u, w.blit};
        if (!st.take_upfront(bin, 2)) proof_->forget(bin, 2);
      }
      if (const std::vector<uint32_t>* o = st.occ_of(u)) {
        for (const uint32_t ref : *o) {
          const Clause& c = clause(ref);
          if (c.garbage) continue;
          bool done = false;
          for (uint32_t k = 0; k < c.size && !done; ++k) done = st.dropped[c.lits()[k]] != 0;
          if (!done && !st.take_upfront(c.lits(), c.size)) proof_->forget(c.lits(), c.size);
        }
      }
      st.dropped[u] = 1;
    }
    st.round_trail = trail_.size();
  };
  if (st.kind == kPigeonhole) {
    const uint32_t holes = st.holes, k = st.k;
    auto p = [&](uint32_t i, uint32_t h, uint32_t j) { return st.cell[(size_t{i} * holes + h) * k + j]; };
    for (uint32_t m = holes; m > 0; --m) {  // hole m - 1 for pigeon m
      const uint32_t hole = m - 1, s = m;
      for (uint32_t i = 0; i < m; ++i) {
        for (uint32_t x = 0; x < hole; ++x) {
          if (over()) return false;
          for (uint32_t a = 0; a < k; ++a) {
            for (uint32_t b = 0; b < k; ++b) {
              const Lit va = p(i, hole, a), vb = p(s, x, b);
              const Lit c[2] = {negate(va), negate(vb)};
              const Lit w[4] = {negate(va), p(i, x, b), p(s, hole, a), negate(vb)};
              if (!counting_add(st, c, 2, w, 4)) return false;
            }
          }
        }
      }
      for (uint32_t i = 0; i < m; ++i) {
        for (uint32_t a = 0; a < k; ++a) {
          if (!counting_add_unit(st, negate(p(i, hole, a)))) return false;
          if (inconsistent_) return true;
        }
      }
      end_round(false);
    }
    return true;
  }
  if (st.kind == kElimination) {
    // The plan's steps (see Elimination), each checked on the clauses before it is written. The
    // plan's cells are this solver's variables.
    const CountingPlan& plan = *counting_plan_;
    constexpr uint32_t none = UINT32_MAX;
    Elimination elim(plan.pigeons, plan.holes, plan.poff, plan.hole);
    // The pigeon clauses: a pigeon of two cells has a binary clause (until it is widened).
    std::vector<uint32_t> owner(plan.hole.size()), cref(plan.pigeons, none);
    for (uint32_t p = 0; p < plan.pigeons; ++p) {
      for (uint32_t c = plan.poff[p]; c < plan.poff[p + 1]; ++c) owner[c] = p;
    }
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (!c.garbage && !c.redundant && var_of(c.lits()[0]) < owner.size()) cref[owner[var_of(c.lits()[0])]] = ref;
    }
    // A clause that is RAT on its first literal: every clause with that literal's negation is
    // satisfied (the PR check with the literal as the whole witness). Written as a plain lemma.
    auto rat = [&](const Lit* c, size_t nc) {
      for (size_t i = 0; i < nc; ++i) {
        if (vals_[c[i]] > 0) return true;  // satisfied at the root: not needed
      }
      for (size_t i = 0; i < nc; ++i) {
        if (vals_[c[i]] < 0) {
          st.failure = "clause literal false at the root";
          return false;
        }
      }
      if (!counting_check_pr(st, c, nc, c, 1)) return false;
      counting_added_ = true;
      if (nc == 1) {
        ++stats_.counting_units;
        assign(c[0], kNoReason);  // at the root: written to the proof
        if (!propagate()) {
          inconsistent_ = true;
          if (proof_) proof_->add_empty();
        }
      } else {
        ++stats_.counting_lemmas;
        if (proof_) proof_->add(c, nc);
        add_binary(c[0], c[1], false);
      }
      return true;
    };
    std::vector<uint32_t> ops;
    std::vector<Lit> wide;
    while (!elim.done()) {
      if (over()) return false;
      elim.round(ops);
      for (size_t at = 0; at < ops.size();) {
        const uint32_t* const op = ops.data() + at;
        if (op[0] == Elimination::kExclude) {
          const Lit c[2] = {make_lit(op[1], true), make_lit(op[2], true)};
          if (!rat(c, 2)) return false;
          at += 3;
        } else if (op[0] == Elimination::kWiden) {
          // The pigeon clause with the new cells (and without its literals false at the root)
          // replaces the one in the formula.
          const uint32_t p = op[1], n = op[2];
          wide.clear();
          if (cref[p] != none) {
            const Clause& c = clause(cref[p]);
            for (uint32_t k = 0; k < c.size; ++k) {
              if (!vals_[c.lits()[k]]) wide.push_back(c.lits()[k]);
            }
          } else {
            if (plan.poff[p + 1] - plan.poff[p] != 2) {
              st.failure = "no clause of a pigeon";
              return false;
            }
            wide.push_back(make_lit(plan.poff[p], false));
            wide.push_back(make_lit(plan.poff[p] + 1, false));
          }
          const size_t narrow = wide.size();
          for (uint32_t k = 0; k < n; ++k) wide.push_back(make_lit(op[3 + k], false));
          const size_t before = clauses_.size();
          if (narrow < 2 || !counting_add(st, wide.data(), wide.size(), nullptr, 0) || clauses_.size() == before) {
            if (!st.failure) st.failure = "a pigeon clause was not widened";
            return false;
          }
          if (cref[p] != none) {
            delete_irredundant(cref[p]);
          } else {
            delete_binary(wide[0], wide[1]);
            --binaries_irredundant_;
          }
          cref[p] = clauses_.back();
          at += 3 + n;
        } else if (op[0] == Elimination::kPr) {
          const Lit a = make_lit(op[1], false), b = make_lit(op[2], false);
          const Lit c[2] = {negate(a), negate(b)};
          const Lit w[4] = {negate(a), make_lit(op[3], false), make_lit(op[4], false), negate(b)};
          if (!counting_add(st, c, 2, w, 4)) return false;
          at += 5;
        } else if (op[0] == Elimination::kUnit) {
          if (!counting_add_unit(st, make_lit(op[1], true))) return false;
          at += 2;
        } else {
          const Lit u = make_lit(op[1] >> 1, op[1] & 1);
          if (!rat(&u, 1)) return false;
          at += 2;
        }
        if (inconsistent_) return true;
      }
      end_round(false);
    }
    return true;
  }
  if (st.kind == kRphp) {
    // First "pigeon m rests at place m", m = n-1 .. 1: PR clauses (-pp[i][m] v -pp[m][x]) for
    // i, x < m, the witness swaps pigeons i and m; then the RUP units -pp[i][m]. Afterwards root
    // propagation puts pigeon m at place m for every m, so every place is in use; then the places
    // into the holes are a plain pigeonhole (the plan above on qq, with the in-use literals true).
    const uint32_t n = st.pigeons, holes = st.holes;
    auto pv = [&](uint32_t i, uint32_t u) { return st.pp[size_t{i} * n + u]; };
    auto qv = [&](uint32_t u, uint32_t k) { return st.qq[size_t{u} * holes + k]; };
    for (uint32_t m = n - 1; m > 0; --m) {
      for (uint32_t i = 0; i < m; ++i) {
        if (over()) return false;
        for (uint32_t x = 0; x < m; ++x) {
          const Lit cl[2] = {negate(pv(i, m)), negate(pv(m, x))};
          const Lit wit[4] = {negate(pv(i, m)), pv(i, x), pv(m, m), negate(pv(m, x))};
          if (!counting_add(st, cl, 2, wit, 4)) return false;
        }
      }
      for (uint32_t i = 0; i < m; ++i) {
        if (!counting_add_unit(st, negate(pv(i, m)))) return false;
        if (inconsistent_) return true;
      }
      end_round(false);
    }
    for (uint32_t m = holes; m > 0; --m) {  // hole m - 1 for place m
      const uint32_t hole = m - 1, s = m;
      for (uint32_t i = 0; i < m; ++i) {
        if (over()) return false;
        for (uint32_t x = 0; x < hole; ++x) {
          const Lit cl[2] = {negate(qv(i, hole)), negate(qv(s, x))};
          const Lit wit[4] = {negate(qv(i, hole)), qv(i, x), qv(s, hole), negate(qv(s, x))};
          if (!counting_add(st, cl, 2, wit, 4)) return false;
        }
      }
      for (uint32_t i = 0; i < m; ++i) {
        if (!counting_add_unit(st, negate(qv(i, hole)))) return false;
        if (inconsistent_) return true;
      }
      end_round(false);
    }
    return true;
  }
  if (st.kind == kClique) {
    // For colour c = m-1 .. 0, reserved for position c+1: the PR clauses "positions i <= c and
    // c+1 do not have colours c and x < c" (the witness swaps the two positions), then by RUP
    // "positions i <= c do not have colour c". Finally position 0 has no colour.
    const uint32_t n = st.vertices, m = st.colours;
    auto qv = [&](uint32_t i, uint32_t u) { return st.q[size_t{i} * n + u]; };
    auto rv = [&](uint32_t u, uint32_t c) { return st.r[size_t{u} * m + c]; };
    for (uint32_t lvl = m; lvl > 0; --lvl) {
      const uint32_t hole = lvl - 1, s = lvl;
      for (uint32_t i = 0; i < lvl; ++i) {
        for (uint32_t x = 0; x < hole; ++x) {
          if (over()) return false;
          for (uint32_t u = 0; u < n; ++u) {
            for (uint32_t v = 0; v < n; ++v) {
              if (u == v) continue;
              const Lit cl[4] = {negate(qv(i, u)), negate(rv(u, hole)), negate(qv(s, v)), negate(rv(v, x))};
              const Lit wit[4] = {negate(qv(i, u)), qv(i, v), qv(s, u), negate(qv(s, v))};
              if (!counting_add(st, cl, 4, wit, 4)) return false;
            }
          }
        }
      }
      for (uint32_t i = 0; i < lvl; ++i) {
        for (uint32_t u = 0; u < n; ++u) {
          if (over()) return false;
          for (uint32_t v = 0; v < n; ++v) {
            if (u == v) continue;
            const Lit cl[3] = {negate(qv(i, u)), negate(rv(u, hole)), negate(qv(s, v))};
            if (!counting_add(st, cl, 3, nullptr, 0)) return false;
          }
          const Lit cl[2] = {negate(qv(i, u)), negate(rv(u, hole))};
          if (!counting_add(st, cl, 2, nullptr, 0)) return false;
        }
      }
      end_round(true);
    }
    for (uint32_t u = 0; u < n; ++u) {
      if (!counting_add_unit(st, negate(qv(0, u)))) return false;
      if (inconsistent_) return true;
    }
    return true;
  }
  std::vector<uint32_t> verts(st.n);
  std::iota(verts.begin(), verts.end(), 0u);
  if (st.kind == kParity) {
    while (verts.size() >= 3) {  // the last vertex m is matched to q
      const uint32_t m = verts.back(), q = verts[verts.size() - 2];
      verts.resize(verts.size() - 2);
      for (const uint32_t u : verts) {
        if (over()) return false;
        for (const uint32_t w : verts) {
          if (u == w) continue;
          const Lit c[2] = {negate(st.e(m, u)), negate(st.e(q, w))};
          const Lit wit[4] = {negate(st.e(m, u)), st.e(m, q), st.e(u, w), negate(st.e(q, w))};
          if (!counting_add(st, c, 2, wit, 4)) return false;
        }
      }
      for (const uint32_t u : verts) {
        if (!counting_add_unit(st, negate(st.e(m, u)))) return false;
        if (inconsistent_) return true;
      }
      if (!counting_add_unit(st, st.e(m, q))) return false;
      if (inconsistent_) return true;
      end_round(false);
    }
    return true;
  }
  std::vector<uint32_t> rest, others;
  while (verts.size() >= 4) {  // the triple of the last point m: first q joins, then r
    const size_t sz = verts.size();
    const uint32_t m = verts[sz - 1], q = verts[sz - 2], r = verts[sz - 3];
    const std::vector<uint32_t> no_q(verts.begin(), verts.end() - 2);  // without m and q
    for (size_t ia = 0; ia < no_q.size(); ++ia) {
      for (size_t ib = ia + 1; ib < no_q.size(); ++ib) {
        if (over()) return false;
        const uint32_t a = no_q[ia], b = no_q[ib];
        rest.clear();
        for (const uint32_t v : no_q) {
          if (v != a && v != b) rest.push_back(v);
        }
        for (size_t ic = 0; ic < rest.size(); ++ic) {
          for (size_t id = ic + 1; id < rest.size(); ++id) {
            const uint32_t c = rest[ic], d = rest[id];
            const Lit cl[2] = {negate(st.t(m, a, b)), negate(st.t(q, c, d))};
            const Lit wit[4] = {negate(st.t(m, a, b)), st.t(m, q, b), st.t(a, c, d), negate(st.t(q, c, d))};
            if (!counting_add(st, cl, 2, wit, 4)) return false;
          }
        }
      }
    }
    for (size_t ia = 0; ia < no_q.size(); ++ia) {
      for (size_t ib = ia + 1; ib < no_q.size(); ++ib) {
        if (!counting_add_unit(st, negate(st.t(m, no_q[ia], no_q[ib])))) return false;
        if (inconsistent_) return true;
      }
    }
    end_round(false);
    others.assign(verts.begin(), verts.end() - 3);  // without m, q and r
    for (const uint32_t b : others) {
      if (over()) return false;
      rest.clear();
      for (const uint32_t v : others) {
        if (v != b) rest.push_back(v);
      }
      for (size_t ic = 0; ic < rest.size(); ++ic) {
        for (size_t id = ic + 1; id < rest.size(); ++id) {
          const uint32_t c = rest[ic], d = rest[id];
          const Lit cl[2] = {negate(st.t(m, q, b)), negate(st.t(r, c, d))};
          const Lit wit[4] = {negate(st.t(m, q, b)), st.t(m, q, r), st.t(b, c, d), negate(st.t(r, c, d))};
          if (!counting_add(st, cl, 2, wit, 4)) return false;
        }
      }
    }
    for (const uint32_t b : others) {
      if (!counting_add_unit(st, negate(st.t(m, q, b)))) return false;
      if (inconsistent_) return true;
    }
    if (!counting_add_unit(st, st.t(m, q, r))) return false;
    if (inconsistent_) return true;
    end_round(false);
    verts = others;
  }
  return true;
}

void Solver::counting() {
  if (counting_tried_ || inconsistent_ || level() != 0) return;
  counting_tried_ = true;
  // The checks see the solver's clauses, which must be the checker's: not after input tautologies
  // or duplicate literals (see input_irregular_). (Clauses satisfied at the root are no problem:
  // no witness falsifies a root literal.)
  if (input_irregular_) return;
  const PassTimer pass_timer(*this, kPassCounting);
  const double t0 = seconds();
  CountingState st;
  bool found = false;
  if (counting_plan_) {  // the isolated solver of a sparse pigeonhole: the structure is given
    found = true;
    st.kind = kElimination;
    st.steps_pr = counting_plan_->steps_pr;
    st.steps_units = counting_plan_->steps_units;
    st.all_vars = num_vars_;
    st.vars.resize(num_vars_);
    std::iota(st.vars.begin(), st.vars.end(), Var{0});
  } else {
    found = counting_detect(st);
  }
  if (!found) {  // the whole formula is not one of those; a clique-colouring formula?
    const uint64_t work = st.work;
    st = CountingState();
    st.work = work;
    found = counting_detect_clique(st);
  }
  if (!found) {  // a relativized pigeonhole?
    const uint64_t work = st.work;
    st = CountingState();
    st.work = work;
    found = counting_detect_rphp(st);
  }
  if (!found && !input_shortened_ && !counting_isolated_) {  // a pigeonhole system inside the formula?
    const uint64_t work = st.work;
    st = CountingState();
    st.work = work;
    found = counting_detect_embedded(st);
    if (!found && opts_.countingprobe) {  // at-most-one constraints over auxiliary variables (exclusions by probing)?
      const uint64_t work2 = st.work;
      st = CountingState();
      st.work = work2;
      found = counting_virtual(st) && counting_detect_embedded(st);
    }
    // A pigeonhole system on a sparse graph? (After root propagation: assigned literals are left
    // out, and the holes taken at the root must be gone.)
    if (!found && opts_.countingsparse && propagated_ == trail_.size()) {
      const uint64_t work2 = st.work;
      st = CountingState();
      st.work = work2;
      found = counting_detect_sparse(st, opts_.countingsparse > 1);
      if (found) counting_plan(st);
    }
  }
  if (!found && opts_.countingcollapse && !counting_isolated_) {  // long clauses split into short ones?
    const uint64_t work = st.work;
    st = CountingState();
    st.work = work;
    if (counting_collapse(st)) {
      stats_.counting_work += st.work;
      if (opts_.verbose) {
        std::printf("c [%.2f s] counting: %s: refuted, %llu PR clauses, %llu units, work %.0fM, %.2f s\n", seconds(),
                    counting_desc_.c_str(), static_cast<unsigned long long>(stats_.counting_pr),
                    static_cast<unsigned long long>(stats_.counting_units), static_cast<double>(st.work) / 1e6, seconds() - t0);
        std::fflush(stdout);
      }
      return;
    }
  }
  stats_.counting_work += st.work;
  const uint64_t detect_work = st.work;
  if (!found) return;
  ++stats_.counting_found;
  char desc[256];
  if (st.sparse) {
    std::snprintf(desc, sizeof desc, "sparse pigeonhole %u pigeons, %u holes, %u of %u pairs absent (of %u pigeons, %u holes)%s, %u new variables",
                  st.pigeons, st.holes, st.missing, st.pigeons * st.holes, st.graph_pigeons, st.graph_holes,
                  st.virt ? ", exclusions by probing" : "", st.plan.fresh);
  } else if (st.kind == kElimination) {
    std::snprintf(desc, sizeof desc, "pigeonhole by elimination, %u pigeons, %u holes", counting_plan_->pigeons,
                  counting_plan_->holes);
  } else if (st.kind == kPigeonhole) {
    std::snprintf(desc, sizeof desc, "%spigeonhole %u pigeons, %u holes, %u variables per pair%s",
                  st.virt ? "embedded (exclusions by probing) " : st.embedded ? "embedded " : "", st.pigeons, st.holes, st.k,
                  st.systems > 1 ? " (one of several independent systems)" : "");
  } else if (st.relativized) {
    std::snprintf(desc, sizeof desc, "relativized pigeonhole %u pigeons, %u places, %u holes", st.pigeons, st.vertices,
                  st.holes);
  } else if (st.kind == kClique) {
    std::snprintf(desc, sizeof desc, "clique-colouring %u positions, %u vertices, %u colours", st.positions,
                  st.vertices, st.colours);
  } else {
    std::snprintf(desc, sizeof desc, "%s %u %s", st.kind == kParity ? "parity" : "Count^3", st.n,
                  st.kind == kParity ? "vertices" : "points");
  }
  counting_desc_ = desc;
  // Work estimate: each step propagates the negation of its clause and visits the clauses of the
  // four witness literals (measured: about twice the actual work). Clique-colouring steps also
  // look up the clause implying each touched edge clause, and their occurrence lists grow with
  // the PR clauses: about a third of the vertices (measured: clqcl_25 5 to 7 times); for the
  // relativized pigeonhole about 2.5 times the places (190 times with 85 places).
  const double nvars = static_cast<double>(st.all_vars);
  const double degree = static_cast<double>(st.degree_sum) / nvars, occs = static_cast<double>(st.long_sum) / nvars;
  double factor = 1.0;
  if (st.kind == kClique) {
    factor = st.relativized ? std::max(6.0, 2.5 * st.vertices) : std::max(6.0, st.vertices / 3.0);
  }
  double estimate = static_cast<double>(st.steps_pr + st.steps_units) * (6 * degree + 4 * occs + 16) * factor;
  const double budget = static_cast<double>(opts_.countingeffort) * 1e6;
  auto report = [&](const char* outcome) {
    if (!opts_.verbose) return;
    std::printf("c [%.2f s] counting: %s: %s, %llu PR clauses, %llu units (planned %llu + %llu), work %.0fM of %.0fM estimated, %.2f s\n", seconds(),
                desc, outcome, static_cast<unsigned long long>(stats_.counting_pr),
                static_cast<unsigned long long>(stats_.counting_units), static_cast<unsigned long long>(st.steps_pr),
                static_cast<unsigned long long>(st.steps_units), static_cast<double>(st.work) / 1e6, estimate / 1e6, seconds() - t0);
    std::fflush(stdout);
  };
  // Over budget: a clique-colouring (or a relativized pigeonhole with its plan) may still be
  // refuted by extension (counting_extend), whose lemmas grow with vertices^2 x colours instead of
  // PR clauses with positions^2 x vertices^2 x colours.
  // Its work (measured on clqcl_* and rphp_p8_r*, within a factor of two): a lemma
  // (-z[i][u][k] v -y[j][k]) propagates over the places and the pigeons, a clique-colouring's
  // adjacency lemma over the vertices. With --countingextend=2 (the default) also whenever that is
  // the cheaper plan: on the clique-colourings the other plan solves, proofs are 3 to 9 times
  // shorter and dpr-trim checks them 15 to 45 times faster.
  uint32_t fresh = 0;
  if (st.kind == kClique && opts_.countingextend && st.colours >= 2 && st.positions > st.colours) {
    const double n = st.positions, m = st.colours + 1.0, r = st.vertices, h = st.colours;
    const double lemmas = (st.relativized ? 0.0 : n * r * r * h) + r * r * h / 2 + m * m * r * h + 8 * m * r * h;
    const double extended = 24 * lemmas + 1.5 * m * m * m * r * r * h + (st.relativized ? 0.0 : 9 * n * r * r * r * h);
    const double vars = (st.relativized ? 0.0 : r) + r * h + m * r * h + m * h;
    if (extended <= budget && vars <= 1e7 && (estimate > budget || (opts_.countingextend > 1 && extended < estimate))) {
      estimate = extended;
      fresh = static_cast<uint32_t>(vars);
      st.steps_pr = st.steps_units = 0;
      for (uint64_t lvl = 1; lvl <= st.colours; ++lvl) {
        st.steps_pr += lvl * (lvl - 1);
        st.steps_units += lvl;
      }
      const size_t len = std::strlen(desc);
      std::snprintf(desc + len, sizeof desc - len, ", by extension with %u new variables", fresh);
      counting_desc_ = desc;
    }
  }
  if (estimate > budget) {
    ++stats_.counting_skipped;
    report("over budget, skipped");
    return;
  }
  if (st.embedded) {
    const bool refuted = counting_isolated(st);
    if (!refuted) ++stats_.counting_failed;
    std::string outcome = refuted ? "refuted in isolation" : "abandoned";
    if (!refuted && st.failure) outcome += std::string(" (") + st.failure + ")";
    report(outcome.c_str());
    return;
  }
  // From here on the state changes: root propagation, then the checks' propagations (their ticks
  // are booked as counting work, not as search ticks; the saved phases are restored).
  if (propagated_ < trail_.size() && !propagate()) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return;
  }
  for (const Var v : st.vars) {
    if (vals_[make_lit(v, false)]) {
      ++stats_.counting_failed;
      report("abandoned (assigned at the root)");
      return;
    }
  }
  const uint32_t extend_base = num_vars_;
  if (fresh) {  // (before the per-variable arrays below, and before the saved phases are copied)
    grow_vars(num_vars_ + fresh);
    for (Var v = extend_base; v < num_vars_; ++v) st.extra_vars.push_back(v);
  }
  // Occurrence lists of the structure literals (both polarities) over all long clauses.
  st.slot.assign(num_vars_, UINT32_MAX);
  uint32_t slots = 0;
  for (const Var v : st.vars) st.slot[v] = slots++;
  for (const Var v : st.extra_vars) {
    if (st.slot[v] == UINT32_MAX) st.slot[v] = slots++;
  }
  st.occ.assign(2 * size_t{slots}, {});
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    for (uint32_t k = 0; k < c.size; ++k) {
      if (std::vector<uint32_t>* o = st.occ_of(c.lits()[k])) o->push_back(ref);
    }
    st.work += c.size / 4 + 1;
  }
  st.mark.assign(2 * size_t{num_vars_}, 0);
  st.limit = 2 * static_cast<uint64_t>(budget) + st.work;
  const std::vector<int8_t> saved = saved_;
  const uint64_t propagations0 = stats_.propagations;
  st.ticks0 = stats_.ticks;
  // Whole-formula pigeonhole: the plan needs the pigeon clauses of pigeons 0 .. holes and the
  // exclusions within a hole among them. If it refutes the formula, the proof first deletes the
  // rest (functional clauses "a pigeon in at most one hole", pigeons beyond holes + 1, other
  // independent systems, second copies of an exclusion: exam_90_80 57% of its clauses), which
  // dpr-trim and cake_lpr would visit for every PR clause. Whether it does is known at the end, so
  // its lines are buffered.
  ProofWriter* const main_proof = proof_;
  std::string buffer;
  std::unique_ptr<ProofWriter> buffered;
  // (Not after root-shortened input clauses: their deletions could not name the checker's.)
  if (proof_ && st.kind == kPigeonhole && !st.embedded && !input_shortened_ && proof_->shortened_live() == 0) {
    const uint32_t holes = st.holes, per_pigeon = st.holes * st.k;
    std::vector<uint32_t> where(num_vars_, UINT32_MAX);
    for (uint32_t c = 0; c < st.cell.size(); ++c) where[var_of(st.cell[c])] = c;
    auto cell = [&](Lit l) {  // cell index of a structure literal of a pigeon 0 .. holes, or none
      const uint32_t c = where[var_of(l)];
      return c != UINT32_MAX && st.cell[c] == l && c / per_pigeon <= holes ? c : UINT32_MAX;
    };
    auto add_upfront = [&](const Lit* lits, uint32_t n) {
      st.upfront.push_back(static_cast<Lit>(n));
      st.upfront.insert(st.upfront.end(), lits, lits + n);
      ++st.upfront_copies[CountingState::key(lits, n)];
    };
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage) continue;
      const uint32_t c0 = cell(c.lits()[0]);
      bool needed = c0 != UINT32_MAX;  // a pigeon clause: its cells, all of one pigeon
      for (uint32_t k = 1; k < c.size && needed; ++k) {
        const uint32_t ck = cell(c.lits()[k]);
        needed = ck != UINT32_MAX && ck / per_pigeon == c0 / per_pigeon;
      }
      if (!needed) add_upfront(c.lits(), c.size);
    }
    std::vector<uint64_t> kept;  // the exclusions kept, to delete second copies (miles1500.72 lists each twice)
    for (Lit l = 0; l < 2 * num_vars_; ++l) {
      for (const Watch& w : watches_[l]) {
        if (!w.binary() || w.blit < l) continue;
        const uint32_t a = cell(negate(l)), b = cell(negate(w.blit));
        const Lit bin[2] = {l, w.blit};
        if (a != UINT32_MAX && b != UINT32_MAX && (a / st.k) % holes == (b / st.k) % holes) {  // one hole
          kept.push_back(uint64_t{l} << 32 | w.blit);
          continue;
        }
        add_upfront(bin, 2);
      }
    }
    std::sort(kept.begin(), kept.end());
    for (size_t i = 1; i < kept.size(); ++i) {
      if (kept[i] != kept[i - 1]) continue;
      const Lit bin[2] = {static_cast<Lit>(kept[i] >> 32), static_cast<Lit>(kept[i] & 0xffffffffu)};
      add_upfront(bin, 2);
    }
    buffered = std::make_unique<ProofWriter>([&buffer](const char* d, size_t n) { buffer.append(d, n); }, proof_->binary());
    buffered->set_map(proof_->map());  // (the input numbering; an isolated subsystem's: the main solver's)
    buffered->set_source(proof_->source());
  }
  struct RestoreProof {
    Solver& s;
    ProofWriter* p;
    ~RestoreProof() { s.proof_ = p; }
  } restore_proof{*this, main_proof};
  if (buffered) proof_ = buffered.get();
  const bool ok = (!fresh || counting_extend(st, extend_base)) && counting_certify(st);
  if (buffered) {
    proof_ = main_proof;
    buffered->flush();
    if (inconsistent_) {
      for (size_t at = 0; at < st.upfront.size(); at += st.upfront[at] + 1) {
        if (st.upfront[at] > 1) proof_->del(st.upfront.data() + at + 1, st.upfront[at]);
      }
    }
    proof_->raw(buffer.data(), buffer.size(), buffered->added(), buffered->deleted(), buffered->pr(),
                buffered->deleted_bytes());
    proof_->adopt(*buffered);
  }
  const uint64_t ticks = stats_.ticks - st.ticks0;
  stats_.ticks = st.ticks0;
  stats_.propagations = propagations0;
  st.work += ticks;
  stats_.counting_work += st.work - detect_work;
  saved_ = saved;
  if (!ok) ++stats_.counting_failed;
  std::string outcome = inconsistent_ ? "refuted" : ok ? "certified, search goes on" : "abandoned";
  if (!ok && st.failure) outcome += std::string(" (") + st.failure + ")";
  report(outcome.c_str());
}

}  // namespace psat
