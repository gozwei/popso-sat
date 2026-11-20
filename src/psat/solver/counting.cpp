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
//   so is the formula.
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
#include <memory>
#include <numeric>
#include <string>
#include <unordered_map>

#include "psat/core/options.hpp"
#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

constexpr int kPigeonhole = 1, kParity = 2, kCount3 = 3, kClique = 4, kRphp = 5;

uint64_t choose2(uint64_t n) { return n < 2 ? 0 : n * (n - 1) / 2; }
uint64_t choose3(uint64_t n) { return n < 3 ? 0 : n * (n - 1) * (n - 2) / 6; }

// Index of the triple {a, b, c} (distinct) in the combinatorial number system.
size_t triple_index(uint32_t a, uint32_t b, uint32_t c) {
  if (a > b) std::swap(a, b);
  if (b > c) std::swap(b, c);
  if (a > b) std::swap(a, b);
  return static_cast<size_t>(choose3(c) + choose2(b) + a);
}

}  // namespace

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
// absent, i.e. no perfect matching of an unbalanced bipartite graph). Pigeons are long clauses
// whose variables occur in no other long clause; holes are the classes of their literals joined
// by exclusions (binary clauses) across pigeons, each class a clique with at most one literal of
// a pigeon; a pigeon may use only some of the holes. Pigeons in a class that is no such clique are
// dropped, and the classes formed again. A maximum matching of pigeons to holes that leaves a
// pigeon unmatched gives a Hall violator: the pigeons S reached from it by alternating paths
// have |S| - 1 holes between them. With a new variable for every absent (pigeon, hole) pair that
// subsystem is the pigeonhole formula |S| -> |S| - 1, refuted in isolation (counting_isolated).
// The formula may say anything else: other clauses are ignored here and deleted from the proof.
bool Solver::counting_detect_sparse(CountingState& st) {
  const size_t nv = num_vars_;
  constexpr uint32_t kNone = UINT32_MAX;
  const uint64_t cap = st.work + 4 * (arena_.size() + 2 * binaries_irredundant_) + 8'000'000;
  // 1. Candidate pigeons: long clauses with three or more unassigned literals, whose variables
  //    occur in no other long clause. Clauses satisfied at the root do not count, and literals
  //    false at the root are left out (a unit clause of the input takes a pigeon's hole: the
  //    pigeon clause is satisfied, the other pigeons lose the hole). The literals of candidate i
  //    are clits[coff[i] .. coff[i + 1]).
  auto satisfied = [this](const Clause& c) {
    for (uint32_t k = 0; k < c.size; ++k) {
      if (vals_[c.lits()[k]] > 0) return true;
    }
    return false;
  };
  std::vector<uint8_t> mult(nv, 0);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    st.work += c.size / 4 + 1;
    if (satisfied(c)) continue;
    for (uint32_t k = 0; k < c.size; ++k) {
      if (vals_[c.lits()[k]]) continue;
      uint8_t& m = mult[var_of(c.lits()[k])];
      if (m < 2) ++m;
    }
  }
  std::vector<uint32_t> cand, coff(1, 0), owner(nv, kNone);
  std::vector<Lit> clits, slit(nv, kNoLit);  // slit: the structure literal of a variable
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || satisfied(c)) continue;
    const size_t start = clits.size();
    bool ok = true;
    for (uint32_t k = 0; k < c.size && ok; ++k) {
      const Lit l = c.lits()[k];
      if (vals_[l]) continue;
      ok = mult[var_of(l)] == 1;
      clits.push_back(l);
    }
    if (!ok || clits.size() - start < 3) {
      clits.resize(start);
      continue;
    }
    for (size_t k = start; k < clits.size(); ++k) {
      owner[var_of(clits[k])] = static_cast<uint32_t>(cand.size());
      slit[var_of(clits[k])] = clits[k];
    }
    cand.push_back(ref);
    coff.push_back(static_cast<uint32_t>(clits.size()));
  }
  st.work += clauses_.size() / 4 + nv / 16;
  if (cand.size() < 3 || st.work > cap) return false;
  // 2. Holes: classes of structure literals joined by exclusions across pigeons.
  std::vector<uint8_t> dead(cand.size(), 0);
  auto find = [](std::vector<uint32_t>& up, uint32_t v) {
    while (up[v] != v) v = up[v] = up[up[v]];
    return v;
  };
  // The structure literals of other live pigeons that x excludes (duplicates included).
  auto exclusions = [&](Lit x, auto&& visit) {
    const uint32_t mine = owner[var_of(x)];
    for (const Watch& w : watches_[negate(x)]) {
      if (!w.binary() || w.redundant_binary()) continue;
      const Var u = var_of(w.blit);
      if (owner[u] == kNone || owner[u] == mine || dead[owner[u]] || slit[u] != negate(w.blit)) continue;
      visit(u);
    }
    st.work += watches_[negate(x)].size() / 4 + 1;
  };
  std::vector<uint32_t> parent(nv), hole(nv, kNone), hole_size, stamp(nv, 0), seen, kill;
  std::vector<uint8_t> bad;
  uint32_t holes = 0, now = 0;
  for (int round = 0;; ++round) {
    std::iota(parent.begin(), parent.end(), 0u);
    std::fill(hole.begin(), hole.end(), kNone);
    st.work += nv / 8;
    for (uint32_t i = 0; i < cand.size(); ++i) {
      if (dead[i]) continue;
      for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
        const Var v = var_of(clits[k]);
        exclusions(clits[k], [&](Var u) { parent[find(parent, u)] = find(parent, v); });
      }
      if (st.work > cap) return false;
    }
    holes = 0;
    hole_size.clear();
    for (uint32_t i = 0; i < cand.size(); ++i) {
      if (dead[i]) continue;
      for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
        const Var v = var_of(clits[k]);
        const uint32_t r = find(parent, v);
        if (hole[r] == kNone) {
          hole[r] = holes++;
          hole_size.push_back(0);
        }
        hole[v] = hole[r];
        ++hole_size[hole[v]];
      }
    }
    // A hole takes at most one literal of a pigeon, and its literals exclude each other.
    bad.assign(holes, 0);
    seen.assign(holes, kNone);
    for (uint32_t i = 0; i < cand.size(); ++i) {
      if (dead[i]) continue;
      for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
        const Var v = var_of(clits[k]);
        const uint32_t h = hole[v];
        if (seen[h] == i) bad[h] = 1;
        seen[h] = i;
        ++now;
        uint32_t count = 0;
        exclusions(clits[k], [&](Var u) {
          if (hole[u] != h || stamp[u] == now) return;
          stamp[u] = now;
          ++count;
        });
        if (count + 1 != hole_size[h]) bad[h] = 1;
      }
      if (st.work > cap) return false;
    }
    kill.clear();
    for (uint32_t i = 0; i < cand.size(); ++i) {
      if (dead[i]) continue;
      for (uint32_t k = coff[i]; k < coff[i + 1]; ++k) {
        if (!bad[hole[var_of(clits[k])]]) continue;
        kill.push_back(i);
        break;
      }
    }
    if (kill.empty()) break;
    if (round == 3) return false;
    for (const uint32_t i : kill) dead[i] = 1;
  }
  std::vector<uint32_t> pig;  // the live pigeons
  for (uint32_t i = 0; i < cand.size(); ++i) {
    if (!dead[i]) pig.push_back(i);
  }
  const auto np = static_cast<uint32_t>(pig.size());
  if (np < 3) return false;
  // 3. A maximum matching of pigeons to holes: greedy, then augmenting paths (breadth-first).
  std::vector<uint32_t> match_hole(holes, kNone), match_pig(np, kNone);
  auto hole_at = [&](uint32_t p, uint32_t k) { return hole[var_of(clits[coff[pig[p]] + k])]; };
  auto size_of = [&](uint32_t p) { return coff[pig[p] + 1] - coff[pig[p]]; };
  for (uint32_t p = 0; p < np; ++p) {
    for (uint32_t k = 0; k < size_of(p); ++k) {
      const uint32_t h = hole_at(p, k);
      if (match_hole[h] != kNone) continue;
      match_hole[h] = p;
      match_pig[p] = h;
      break;
    }
    st.work += size_of(p) / 4 + 1;
  }
  std::vector<uint32_t> pstamp(np, 0), hstamp(holes, 0), reached(holes, kNone), queue, best_pigeons, best_holes, hs;
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
      st.work += size_of(q) + 1;
      for (uint32_t k = 0; k < size_of(q); ++k) {
        const uint32_t h = hole_at(q, k);
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
    if (match_pig[p] != kNone) continue;
    search(p);
    if (st.work > cap) return false;
  }
  // 4. The smallest Hall violator among those of the first unmatched pigeons.
  uint32_t tried = 0;
  for (uint32_t p = 0; p < np && tried < 16; ++p) {
    if (match_pig[p] != kNone) continue;
    ++tried;
    if (search(p)) return false;  // (cannot happen: the matching is maximum)
    if (st.work > cap) return false;
    if (queue.size() != hs.size() + 1) return false;
    if (best_pigeons.empty() || queue.size() < best_pigeons.size()) {
      best_pigeons = queue;
      best_holes = hs;
    }
  }
  if (best_pigeons.empty() || best_holes.empty()) return false;  // every pigeon has a hole
  const auto pigeons = static_cast<uint32_t>(best_pigeons.size()), nholes = static_cast<uint32_t>(best_holes.size());
  if (uint64_t{pigeons} * nholes > (uint64_t{1} << 24)) return false;
  std::sort(best_pigeons.begin(), best_pigeons.end());
  std::sort(best_holes.begin(), best_holes.end());
  std::vector<uint32_t> local(holes, kNone);
  for (uint32_t i = 0; i < nholes; ++i) local[best_holes[i]] = i;
  st.cell.assign(size_t{pigeons} * nholes, kNoLit);
  for (uint32_t i = 0; i < pigeons; ++i) {
    const uint32_t ci = pig[best_pigeons[i]];
    st.longs.push_back(cand[ci]);
    for (uint32_t k = coff[ci]; k < coff[ci + 1]; ++k) {
      const Lit x = clits[k];
      st.cell[size_t{i} * nholes + local[hole[var_of(x)]]] = x;
      st.vars.push_back(var_of(x));
    }
  }
  std::sort(st.vars.begin(), st.vars.end());
  st.missing = static_cast<uint32_t>(std::count(st.cell.begin(), st.cell.end(), kNoLit));
  st.kind = kPigeonhole;
  st.embedded = true;
  st.sparse = true;
  st.pigeons = pigeons;
  st.holes = nholes;
  st.k = 1;
  st.graph_pigeons = np;
  st.graph_holes = holes;
  st.all_vars = st.cell.size();
  for (uint64_t m = 1; m <= nholes; ++m) {
    st.steps_pr += m * (m - 1);
    st.steps_units += m;
  }
  st.degree_sum = uint64_t{nholes} * st.all_vars;  // (in the completed subsystem: about one per pigeon)
  st.long_sum = uint64_t{nholes} * st.all_vars;
  return true;
}

// Refutes the embedded subsystem on its own: a solver on its pigeon clauses and its at-most-one
// binary clauses (renumbered variables) runs the pass. If it refutes them, the proof deletes every
// other clause (the checker then sees the subsystem only, as the isolated solver did) and
// continues with the isolated solver's proof, which ends with the empty clause. Refuting a subset
// of the clauses refutes the formula. Otherwise nothing is written.
bool Solver::counting_isolated(CountingState& st) {
  const uint32_t holes = st.holes, pigeons = st.pigeons;
  // The isolated solver's variable of a cell is the cell's index (pigeon * holes + hole).
  std::vector<uint32_t> where(num_vars_, UINT32_MAX);
  std::vector<Lit> to_main;
  // Sparse pigeonhole: a cell without a variable gets a new one, above the solver's variables (in
  // the isolated solver and in the proof only: this solver ends here if the refutation succeeds,
  // and nothing is written if it does not).
  Var fresh = num_vars_;
  for (uint32_t i = 0; i < pigeons * holes; ++i) {
    if (st.cell[i] == kNoLit) {
      to_main.push_back(make_lit(fresh, false));
      to_main.push_back(make_lit(fresh, true));
      ++fresh;
      continue;
    }
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
  // The literal of a cell in the isolated solver, and in this solver's proof (a new variable is
  // beyond the proof writer's map and written as it is).
  auto cell_dimacs = [&](uint32_t c) { return st.cell[c] == kNoLit ? static_cast<int>(c) + 1 : dimacs(st.cell[c]); };
  auto cell_lit = [&](uint32_t c) { return st.cell[c] == kNoLit ? to_main[2 * size_t{c}] : st.cell[c]; };
  // In the subsystem: (-a v -b) for structure literals a, b of one hole and different pigeons, or
  // of one pigeon (not in a sparse pigeonhole: the new variables have no such clauses, and the PR
  // checks need them for all of a pigeon's variables or for none).
  auto in_subsystem = [&](Lit a, Lit b) {  // the binary clause (-a v -b)
    const uint32_t wa = where[var_of(a)], wb = where[var_of(b)];
    if (wa == UINT32_MAX || wb == UINT32_MAX || st.cell[wa] != a || st.cell[wb] != b || wa == wb) return false;
    if (st.sparse) return wa / holes != wb / holes && wa % holes == wb % holes;
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
      for (uint32_t h = 0; h < holes; ++h) cl.push_back(cell_dimacs(i * holes + h));
      iso.add_clause(cl.data(), cl.size());
    }
    // Its at-most-one clauses: binary clauses of the formula, and virtual exclusions, which the
    // proof derives by RUP before the auxiliary clauses are deleted.
    std::vector<Lit> lemmas;  // pairs
    std::vector<uint64_t> fed;
    for (uint32_t i = 0; i < pigeons * holes; ++i) {
      const Lit a = st.cell[i];
      if (a == kNoLit) continue;
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
    // Sparse pigeonhole: a new variable excludes the other variables of its hole. Pairs of cells,
    // the first one new; in the proof each clause is RAT on its first literal, the negated new
    // variable, which no clause contains yet (the widened pigeon clauses come after all of them).
    std::vector<uint32_t> completion;
    if (st.sparse) {
      for (uint32_t h = 0; h < holes; ++h) {
        for (uint32_t i = 0; i < pigeons; ++i) {
          const uint32_t ci = i * holes + h;
          if (st.cell[ci] != kNoLit) continue;
          for (uint32_t j = 0; j < pigeons; ++j) {
            const uint32_t cj = j * holes + h;
            if (j == i || (st.cell[cj] == kNoLit && j > i)) continue;
            const int bin[2] = {-cell_dimacs(ci), -cell_dimacs(cj)};
            iso.add_clause(bin, 2);
            completion.push_back(ci);
            completion.push_back(cj);
          }
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
      // Sparse pigeonhole: the new variables' exclusions, then each pigeon clause widened by the
      // new variables of its absent holes (implied by the pigeon clause, whose other literals are
      // false at the root; that clause is deleted below: a witness may satisfy the wide clause by
      // a new variable and falsify the narrow one). A pigeon clause with every hole stays as it
      // is: its literals false at the root are false for the checker too.
      std::vector<uint32_t> keep;
      for (size_t i = 0; i < completion.size(); i += 2) {
        const Lit bin[2] = {negate(cell_lit(completion[i])), negate(cell_lit(completion[i + 1]))};
        proof_->add(bin, 2);
      }
      std::vector<Lit> wide;
      for (uint32_t i = 0; i < pigeons; ++i) {
        bool widened = false;
        wide.clear();
        for (uint32_t h = 0; h < holes; ++h) {
          widened = widened || st.cell[i * holes + h] == kNoLit;
          wide.push_back(cell_lit(i * holes + h));
        }
        if (!widened) {
          keep.push_back(st.longs[i]);
          continue;
        }
        proof_->add(wide.data(), wide.size());
        ++stats_.counting_lemmas;
      }
      stats_.counting_lemmas += completion.size() / 2;
      // Delete every other clause, then the isolated refutation. The PR checks need the other
      // clauses on the subsystem's variables gone (the checker then sees the subsystem only, as
      // the isolated solver did); the rest goes too, since dpr-trim and cake_lpr visit every
      // clause of the formula for each PR clause (exam_90_80: dpr-trim 2729 s for a 0.8 s solve).
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
  std::vector<uint32_t> used_place(nl, kNone);
  st.used.assign(nplaces, kNoLit);
  for (uint32_t u = 0; u < nplaces; ++u) {
    for (uint32_t i = 0; i < n; ++i) {
      const Lit x = st.pp[size_t{i} * nplaces + u];
      uint32_t excl = 0;
      Lit implied = kNoLit;
      for (const Watch& w : watches_[negate(x)]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const uint32_t pl = place[negate(w.blit)];
        if (pl != kNone && pl % nplaces == u && pl / nplaces != i) {
          ++excl;
        } else if (implied == kNoLit || implied == w.blit) {
          implied = w.blit;
        } else {
          return false;
        }
      }
      if (excl < n - 1 || implied == kNoLit) return false;
      if (st.used[u] == kNoLit) {
        if (used_place[implied] != kNone || place[implied] != kNone || place[negate(implied)] != kNone) return false;
        st.used[u] = implied;
        used_place[implied] = u;
      } else if (st.used[u] != implied) {
        return false;
      }
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
  bool found = counting_detect(st);
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
      found = counting_detect_sparse(st);
    }
  }
  stats_.counting_work += st.work;
  const uint64_t detect_work = st.work;
  if (!found) return;
  ++stats_.counting_found;
  char desc[192];
  if (st.sparse) {
    std::snprintf(desc, sizeof desc, "sparse pigeonhole %u pigeons, %u holes, %u of %u pairs absent (of %u pigeons, %u holes)",
                  st.pigeons, st.holes, st.missing, st.pigeons * st.holes, st.graph_pigeons, st.graph_holes);
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
  const double estimate = static_cast<double>(st.steps_pr + st.steps_units) * (6 * degree + 4 * occs + 16) * factor;
  const double budget = static_cast<double>(opts_.countingeffort) * 1e6;
  auto report = [&](const char* outcome) {
    if (!opts_.verbose) return;
    std::printf("c [%.2f s] counting: %s: %s, %llu PR clauses, %llu units (planned %llu + %llu), work %.0fM of %.0fM estimated, %.2f s\n", seconds(),
                desc, outcome, static_cast<unsigned long long>(stats_.counting_pr),
                static_cast<unsigned long long>(stats_.counting_units), static_cast<unsigned long long>(st.steps_pr),
                static_cast<unsigned long long>(st.steps_units), static_cast<double>(st.work) / 1e6, estimate / 1e6, seconds() - t0);
    std::fflush(stdout);
  };
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
  const bool ok = counting_certify(st);
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
