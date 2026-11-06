// CDCL solver: answers against a brute-force oracle, models against the formula, and every
// UNSAT answer's DRAT proof through the test-only RUP checker. Options that change schedules are
// pushed to extremes (tiny reduce / rephase / mode intervals) so that small formulas exercise
// reduction, garbage collection, mode switching and rephasing.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <random>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

#include "psat/io/dimacs.hpp"
#include "psat/io/input.hpp"
#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"
#include "rup_checker.hpp"
#include "test_framework.hpp"

using namespace psat;
using psat_test::ClauseList;

namespace {

struct Outcome {
  int result = 0;
  bool model_ok = false;
  bool proof_ok = false;
  std::string proof_error;
};

Outcome run(int n, const ClauseList& clauses, const Options& opts = Options(), bool check_proof = true) {
  Outcome out;
  std::string proof_text;
  ProofWriter proof([&](const char* d, size_t k) { proof_text.append(d, k); }, false);
  Solver s(opts);
  if (check_proof) s.set_proof(&proof);
  s.reserve(n);
  for (const auto& c : clauses) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  out.result = s.solve();
  proof.flush();
  if (out.result == kSat) {
    out.model_ok = true;
    for (const auto& c : clauses) {
      bool sat = false;
      for (int l : c) sat = sat || s.val(l) == l;
      if (!sat) out.model_ok = false;
    }
    for (int v = 1; v <= n; ++v) {
      if (s.val(v) != v && s.val(v) != -v) out.model_ok = false;
      if (s.val(-v) != s.val(v)) out.model_ok = false;  // IPASIR: val(-v) == val(v)
    }
  }
  if (out.result == kUnsat && check_proof) {
    psat_test::RupChecker checker(n);
    for (const auto& c : clauses) checker.add_original(c);
    const auto r = checker.check_text_proof(proof_text);
    out.proof_ok = r.ok && r.has_empty;
    out.proof_error = r.ok ? (r.has_empty ? "" : "no empty clause") : r.error;
  }
  return out;
}

ClauseList random_formula(std::mt19937_64& rng, int n, int m, int min_len, int max_len) {
  ClauseList cl;
  std::uniform_int_distribution<int> var(1, n), len(min_len, max_len), sign(0, 1);
  for (int i = 0; i < m; ++i) {
    std::vector<int> c;
    const int k = len(rng);
    for (int j = 0; j < k; ++j) c.push_back(sign(rng) ? var(rng) : -var(rng));
    cl.push_back(c);
  }
  return cl;
}

ClauseList pigeonhole(int holes) {
  ClauseList cl;
  auto x = [holes](int p, int h) { return p * holes + h + 1; };
  for (int p = 0; p <= holes; ++p) {
    std::vector<int> c;
    for (int h = 0; h < holes; ++h) c.push_back(x(p, h));
    cl.push_back(c);
  }
  for (int h = 0; h < holes; ++h) {
    for (int p = 0; p <= holes; ++p) {
      for (int q = p + 1; q <= holes; ++q) cl.push_back({-x(p, h), -x(q, h)});
    }
  }
  return cl;
}

// Option sets that stress the schedules on small formulas.
std::vector<Options> option_variants() {
  std::vector<Options> v;
  v.emplace_back();
  Options a;
  a.reduceint = 10;
  a.reducefraction = 90;
  a.modeinit = 10;
  a.rephaseint = 10;
  v.push_back(a);
  Options b;
  b.stable = 0;
  b.minimize = 0;
  b.bumpreasons = 0;
  v.push_back(b);
  Options k;  // chronological backtracking on every backjump, frequent restarts and reductions
  k.chrono = 1;
  k.chronolevels = 0;
  k.reduceint = 10;
  k.rephaseint = 10;
  k.modeinit = 10;
  k.eliminateint = 10;
  k.vivifyint = 10;
  v.push_back(k);
  k.chronolevels = 2;
  k.stable = 2;
  v.push_back(k);
  Options c;
  c.stable = 2;
  c.target = 2;
  c.reluctantint = 2;
  c.reduceint = 10;
  c.tier1 = 1;
  c.tier2 = 1;
  c.dynamictiers = 1;
  v.push_back(c);
  Options d;
  d.seed = 12345;
  d.phase = 0;
  d.modeinit = 10;
  d.modegrowth = 100;
  d.restartmargin = 0;
  d.minimizedepth = 1;
  d.shrink = 1;
  d.reusetrail = 0;  // the pre-0.3 search defaults
  d.modeschedule = 0;
  v.push_back(d);
  Options e;  // frequent elimination rounds with growing bounds, between restarts and reductions
  e.eliminateinit = 3;
  e.eliminateint = 10;
  e.reduceint = 10;
  e.eliminateclslim = 5;
  e.eliminatexorlim = 0;  // XOR merges allowed (limited by the default otherwise)
  v.push_back(e);
  e.vivifyint = 10;  // the same with frequent vivification, BVA, shrinking and sweeping
  e.probeuip = 1;  // (failed probes learn their first UIP)
  e.bva = 1;
  e.bvamin = 0;  // (replacements without a trial)
  e.shrink = 2;  // (with implied lower-level literals)
  e.vivifytier3 = 1;
  e.vivifyinst = 1;
  e.vivifyimplied = 1;
  e.vivifyasym = 1;
  e.unhide = 1;
  e.sweepsubst = 1;
  e.sweepgrow = 1;
  e.simeq = 1;
  e.simeqite = 1;
  e.simeqdepth = 2;  // (small windows: candidates that fail as well as ones that are proven)
  e.vivifyeffort = 10000;
  e.sweep = 1;
  e.sweepeffort = 10000;
  e.definitions = 1;
  v.push_back(e);
  e.sweepclasses = 0;  // the same with the earlier sweeping candidates (only with the swept variable)
  e.sweepgrow = 0;     // and fixed environment limits
  v.push_back(e);
  Options s;  // sweeping with small environments
  s.sweep = 1;
  s.sweepdepth = 1;
  s.sweepvars = 8;
  s.sweepclauses = 16;
  s.vivifyint = 20;
  s.probeuip = 1;
  v.push_back(s);
  Options f;  // no simplification at all
  f.eliminate = 0;
  f.vivify = 0;
  f.sweep = 0;
  v.push_back(f);
  Options g;  // elimination without subsumption, large bound from the start
  g.simeq = 0;              // (and the earlier congruence matching, no simulation)
  g.congruenceclosure = 0;
  g.subsume = 0;
  g.eliminategates = 0;
  g.bva = 1;
  g.bvamin = 0;  // (replacements without a trial)
  g.eliminatebound = 1024;
  g.eliminateint = 20;
  g.vivifyint = 15;
  g.vivifyirred = 0;
  v.push_back(g);
  g.definitions = 0;
  g.sweep = 0;
  g.bvahops = 1;
  v.push_back(g);  // the same without definitions and sweeping, 3-hop BVA tie-breaks
  g.bvafirst = 0;
  g.bvaticks = 1000;
  v.push_back(g);  // BVA after elimination, tiny budget
  g.bvafirst = 1;
  g.bvaticks = 1000000;
  g.bvaevery = 1;
  g.bvaprotect = 1;
  v.push_back(g);  // BVA in every round, its variables protected from elimination
  g.bvamin = 200;
  v.push_back(g);  // trial rounds first: replacements only where they remove a fifth of the clauses
  g.bvamin = 1;
  g.bvaevery = 0;
  g.bvaprotect = 0;
  v.push_back(g);  // a trial, then (almost always) the round
  Options h;  // semantic definitions only (no syntactic gates), frequent rounds
  h.eliminategates = 0;
  h.definitions = 1;
  h.definitionticks = 100000;
  h.eliminateinit = 2;
  h.eliminateint = 10;
  h.eliminatebound = 8;
  v.push_back(h);
  return v;
}

}  // namespace

TEST(solver_trivial_formulas) {
  CHECK_EQ(run(0, {}).result, kSat);
  CHECK_EQ(run(3, {}).result, kSat);
  Outcome e = run(1, {{}});
  CHECK_EQ(e.result, kUnsat);
  CHECK(e.proof_ok);
  Outcome u = run(1, {{1}, {-1}});
  CHECK_EQ(u.result, kUnsat);
  CHECK(u.proof_ok);
  Outcome t = run(2, {{1, -1}, {2, 2, 2}});
  CHECK_EQ(t.result, kSat);
  CHECK(t.model_ok);
  Outcome chain = run(4, {{1}, {-1, 2}, {-2, 3}, {-3, 4}, {-4, -1}});
  CHECK_EQ(chain.result, kUnsat);
  CHECK(chain.proof_ok);
}

TEST(solver_pigeonhole_unsat_with_proof) {
  for (int holes = 1; holes <= 6; ++holes) {
    for (const Options& o : option_variants()) {
      Outcome r = run(holes * (holes + 1), pigeonhole(holes), o);
      CHECK_EQ(r.result, kUnsat);
      CHECK(r.proof_ok);
      if (!r.proof_ok) std::fprintf(stderr, "  php %d: %s\n", holes, r.proof_error.c_str());
    }
  }
}

TEST(solver_random_vs_brute_force) {
  std::mt19937_64 rng(42);
  const auto variants = option_variants();
  int sat = 0, unsat = 0;
  for (int it = 0; it < 1500; ++it) {
    const int n = 3 + static_cast<int>(rng() % 12);
    const int m = static_cast<int>(n * (2 + rng() % 5));
    const ClauseList cl = random_formula(rng, n, m, 1 + static_cast<int>(rng() % 2), 3 + static_cast<int>(rng() % 3));
    const bool expected = psat_test::brute_force_sat(n, cl);
    const Options& o = variants[static_cast<size_t>(it) % variants.size()];
    Outcome r = run(n, cl, o);
    CHECK_EQ(r.result, expected ? kSat : kUnsat);
    if (r.result != (expected ? kSat : kUnsat) || (r.result == kSat && !r.model_ok)) {
      std::fprintf(stderr, "  variant %zu formula: p cnf %d %zu\n", static_cast<size_t>(it) % variants.size(), n,
                   cl.size());
      for (const auto& c : cl) {
        std::fprintf(stderr, "   ");
        for (int l : c) std::fprintf(stderr, " %d", l);
        std::fprintf(stderr, " 0\n");
      }
    }
    if (r.result == kSat) {
      ++sat;
      CHECK(r.model_ok);
    } else if (r.result == kUnsat) {
      ++unsat;
      CHECK(r.proof_ok);
      if (!r.proof_ok) std::fprintf(stderr, "  formula %d: %s\n", it, r.proof_error.c_str());
    }
  }
  CHECK(sat > 200);
  CHECK(unsat > 200);
}

TEST(solver_random_3sat_medium) {
  // Near the threshold, large enough for real search, restarts and reductions; proofs checked.
  std::mt19937_64 rng(7);
  const auto variants = option_variants();
  for (int it = 0; it < 40; ++it) {
    const int n = 40 + static_cast<int>(rng() % 40);
    const ClauseList cl = random_formula(rng, n, static_cast<int>(n * 4.3), 3, 3);
    const Options& o = variants[static_cast<size_t>(it) % variants.size()];
    Outcome r = run(n, cl, o);
    REQUIRE(r.result == kSat || r.result == kUnsat);
    if (r.result == kSat) CHECK(r.model_ok);
    if (r.result == kUnsat) {
      CHECK(r.proof_ok);
      if (!r.proof_ok) std::fprintf(stderr, "  formula %d: %s\n", it, r.proof_error.c_str());
    }
    // Same answer without proof logging and with another option set.
    Outcome r2 = run(n, cl, variants[static_cast<size_t>(it + 1) % variants.size()], false);
    CHECK_EQ(r2.result, r.result);
  }
}

namespace {

// Circuit builder for structured regression formulas (Tseitin encoding).
struct Circuit {
  int n = 0;
  ClauseList cl;
  int var() { return ++n; }
  int AND(int a, int b) {
    const int o = var();
    cl.push_back({-o, a});
    cl.push_back({-o, b});
    cl.push_back({o, -a, -b});
    return o;
  }
  int OR(int a, int b) { return -AND(-a, -b); }
  int XOR(int a, int b) {
    const int o = var();
    cl.push_back({-o, a, b});
    cl.push_back({-o, -a, -b});
    cl.push_back({o, -a, b});
    cl.push_back({o, a, -b});
    return o;
  }
};

// Miter of a ripple-carry adder (xor / majority) and a generate-propagate adder with swapped
// operands: unsatisfiable, rich in AND/XOR gates, equivalences and duplicate binaries.
std::pair<int, ClauseList> adder_miter(int bits) {
  Circuit c;
  std::vector<int> a, b;
  for (int i = 0; i < bits; ++i) a.push_back(c.var());
  for (int i = 0; i < bits; ++i) b.push_back(c.var());
  std::vector<int> s1, s2;
  int c1 = 0, c2 = 0;
  for (int i = 0; i < bits; ++i) {
    const int t = c.XOR(a[i], b[i]);
    if (i == 0) {
      s1.push_back(t);
      c1 = c.AND(a[i], b[i]);
    } else {
      s1.push_back(c.XOR(t, c1));
      c1 = c.OR(c.AND(a[i], b[i]), c.AND(t, c1));
    }
    const int g = c.AND(b[i], a[i]), p = c.OR(b[i], a[i]), h = c.XOR(b[i], a[i]);
    if (i == 0) {
      s2.push_back(h);
      c2 = g;
    } else {
      s2.push_back(c.XOR(c2, h));
      c2 = c.OR(g, c.AND(p, c2));
    }
  }
  std::vector<int> diff;
  for (int i = 0; i < bits; ++i) diff.push_back(c.XOR(s1[i], s2[i]));
  diff.push_back(c.XOR(c1, c2));
  c.cl.push_back(diff);
  return {c.n, c.cl};
}

}  // namespace

TEST(solver_structured_miters_with_invariants) {
  // Regression: removing the wrong copy of a duplicated binary clause during elimination left an
  // original clause on an eliminated variable (wrong SAT model on an adder miter).
  for (int bits : {4, 8, 16, 32}) {
    const auto f = adder_miter(bits);
    std::vector<Options> vs = option_variants();
    for (size_t i = 0; i < vs.size(); ++i) {
      Options o = vs[i];
      o.invariants = 1;
      Outcome r = run(f.first, f.second, o);
      CHECK_EQ(r.result, kUnsat);
      CHECK(r.proof_ok);
      if (!r.proof_ok || r.result != kUnsat) {
        std::fprintf(stderr, "  adder miter %d bits, variant %zu: result %d %s\n", bits, i, r.result,
                     r.proof_error.c_str());
      }
    }
  }
}

TEST(solver_regression_adder_miter_256) {
  // The formula that exposed the duplicate-binary bug: a 256-bit ripple-carry vs. generate/
  // propagate adder miter (tests/data/adder_miter_256.cnf.gz). With the bug, the second
  // elimination round (2000 conflicts) left a clause on an eliminated variable and the solver
  // reported a wrong model. Default options plus the invariant checks, proof checked.
  struct Collect : DimacsHandler {
    int vars = 0;
    ClauseList cl;
    void header(int v, int64_t) override { vars = v; }
    void clause(const int* lits, size_t k) override { cl.emplace_back(lits, lits + k); }
  } f;
  DimacsParser parser(f);
  stream_input(std::string(PSAT_SOURCE_DIR) + "/tests/data/adder_miter_256.cnf.gz",
               [&](const char* d, size_t k) { parser.feed(d, k); });
  parser.finish();
  Options o;
  o.invariants = 1;
  Outcome r = run(f.vars, f.cl, o);
  CHECK_EQ(r.result, kUnsat);
  CHECK(r.proof_ok);
}

TEST(solver_congruent_ite_gates) {
  // o4 = ITE(1,2,3); o5 = ITE(-1,3,2) (the same gate, condition negated); -o6 = ITE(1,-2,-3) (the
  // same gate, output negated). Congruence closure finds o4 = o5 = o6 (proved by case splits on
  // the condition); with o4 != o5 the formula is unsatisfiable, and every model has o4 = o5 = o6.
  auto ite = [](int o, int c, int t, int e) {
    return ClauseList{{-c, -t, o}, {-c, t, -o}, {c, -e, o}, {c, e, -o}};
  };
  ClauseList base;
  for (const auto& g : {ite(4, 1, 2, 3), ite(5, -1, 3, 2), ite(-6, 1, -2, -3)}) {
    base.insert(base.end(), g.begin(), g.end());
  }
  for (int variant = 0; variant < 2; ++variant) {
    ClauseList f = base;
    if (variant == 0) {
      f.push_back({4, 5});
      f.push_back({-4, -5});
    } else {
      f.push_back({4, 6});
      f.push_back({-5, 1});
    }
    std::string proof_text;
    ProofWriter proof([&](const char* d, size_t k) { proof_text.append(d, k); }, false);
    Options o;
    o.lucky = 0;
    o.walk = 0;
    Solver s(o);
    s.set_proof(&proof);
    s.reserve(6);
    for (const auto& c : f) {
      for (int l : c) s.add(l);
      s.add(0);
    }
    const int result = s.solve();
    proof.flush();
    CHECK(s.stats().congruent_ites >= 2);
    if (variant == 0) {
      CHECK_EQ(result, kUnsat);
      psat_test::RupChecker checker(6);
      for (const auto& c : f) checker.add_original(c);
      const auto r = checker.check_text_proof(proof_text);
      CHECK(r.ok && r.has_empty);
      if (!r.ok) std::fprintf(stderr, "  ite congruence proof: %s\n", r.error.c_str());
    } else {
      CHECK_EQ(result, kSat);
      for (const auto& c : f) {
        bool sat = false;
        for (int l : c) sat = sat || s.val(l) == l;
        CHECK(sat);
      }
      CHECK((s.val(4) > 0) == (s.val(5) > 0));
      CHECK((s.val(4) > 0) == (s.val(6) > 0));
    }
  }
}

TEST(solver_semantic_definition_keeps_gate_pairs) {
  // Regression guard (found by mutation testing, delta-debugged): with a semantic definition
  // (an unsat core), gate x gate resolvents are not tautologies and must be added; skipping them
  // as for syntactic gates gives a wrong model here.
  const ClauseList f = {{7, 5, 9},    {16, -17},     {11, 14},   {13, 2},   {5, -10},  {-2, 7, 15}, {8, 18},
                        {-12, -2},    {12, 5, -15},  {-1, 3},    {-5, -16}, {-7, -11}, {-3, -13},   {-18, 4},
                        {-15, 17, 7}, {15, -7, -5},  {2, 1},     {-14, -6}, {-8, 4}};
  for (const Options& base : option_variants()) {
    Options o = base;
    o.definitions = 1;
    o.eliminategates = 0;
    Outcome r = run(18, f, o);
    CHECK_EQ(r.result, kSat);
    CHECK(r.model_ok);
  }
}

TEST(solver_incremental_add_after_solve) {
  Options o;
  o.eliminate = 0;  // incremental use needs frozen variables (not yet)
  Solver s(o);
  s.add(1);
  s.add(2);
  s.add(0);
  CHECK_EQ(s.solve(), kSat);
  s.add(-1);
  s.add(0);
  CHECK_EQ(s.solve(), kSat);
  CHECK_EQ(s.val(2), 2);
  s.add(-2);
  s.add(0);
  CHECK_EQ(s.solve(), kUnsat);
}

TEST(solver_conflict_limit_unknown) {
  Options o;
  o.counting = 0;  // the counting pass refutes pigeonholes before search
  Solver s(o);
  for (const auto& c : pigeonhole(8)) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  s.set_conflict_limit(100);
  CHECK_EQ(s.solve(), kUnknown);
  CHECK(std::string(s.unknown_reason()) == "conflict limit");
}

TEST(solver_memory_limit_counts_resident_size) {
  // The memory limit includes the process's resident size, not only the solver's own structures
  // (a few kB here), and the search stops below the limit: 1 MB is exceeded at the first check.
  Solver s;
  for (const auto& c : pigeonhole(8)) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  CHECK(s.memory_bytes() < (size_t{1} << 20));
  s.set_memory_limit(uint64_t{1} << 20);
  CHECK_EQ(s.solve(), kUnknown);
  CHECK(std::string(s.unknown_reason()) == "memory limit");
  Solver t;
  for (const auto& c : pigeonhole(6)) {
    for (int l : c) t.add(l);
    t.add(0);
  }
  t.set_memory_limit(uint64_t{1} << 40);
  CHECK_EQ(t.solve(), kUnsat);
}

TEST(proof_write_error_is_sticky) {
  // A sink that fails on its first call (full disk): no exception leaves the solver, the proof
  // is marked failed and nothing more is written; the solver still answers.
  int calls = 0;
  ProofWriter proof([&](const char*, size_t) {
    ++calls;
    throw std::runtime_error("disk full");
  }, false);
  Solver s;
  s.set_proof(&proof);
  const ClauseList f = pigeonhole(5);
  s.reserve(30);
  for (const auto& c : f) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  CHECK_EQ(s.solve(), kUnsat);
  proof.flush();
  CHECK(proof.failed());
  CHECK_EQ(calls, 1);
  std::string ok_text;
  ProofWriter ok([&](const char* d, size_t k) { ok_text.append(d, k); }, false);
  const Lit a[1] = {from_dimacs(1)};
  ok.add(a, 1);
  ok.flush();
  CHECK(!ok.failed());
}

TEST(proof_binary_encoding) {
  std::string out;
  {
    ProofWriter p([&](const char* d, size_t k) { out.append(d, k); }, true);
    const Lit a[3] = {from_dimacs(1), from_dimacs(-2), from_dimacs(100)};
    p.add(a, 3);
    p.del(a, 1);
    p.add_empty();
  }
  // 1 -> 2, -2 -> 5, 100 -> 200 = 0xC8 -> varint C8 01.
  const std::string expected = std::string("a\x02\x05\xc8\x01\x00", 6) + std::string("d\x02\x00", 3) + std::string("a\x00", 2);
  CHECK(out == expected);
  std::string text;
  {
    ProofWriter p([&](const char* d, size_t k) { text.append(d, k); }, false);
    const Lit a[2] = {from_dimacs(-7), from_dimacs(3)};
    p.add(a, 2);
    p.del(a, 2);
  }
  CHECK(text == "-7 3 0\nd -7 3 0\n");
}

namespace {

// Runs cardinality detection (--cardinality) on a formula with a conflict limit of 1.
CardinalityStats detect(int n, const ClauseList& clauses) {
  Options o;
  o.cardinality = 1;
  Solver s(o);
  s.reserve(n);
  for (const auto& c : clauses) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  s.set_conflict_limit(1);
  s.solve();
  return s.cardinality_stats();
}

// Sinz's sequential counter for at-most-k over the DIMACS literals xs; auxiliary variables from
// next_var on (advanced).
void sequential_counter(ClauseList& cl, const std::vector<int>& xs, int k, int& next_var) {
  const int n = static_cast<int>(xs.size());
  std::vector<std::vector<int>> s(static_cast<size_t>(n), std::vector<int>(static_cast<size_t>(k) + 1, 0));
  for (int i = 0; i + 1 < n; ++i) {
    for (int j = 1; j <= k; ++j) s[i][j] = next_var++;
  }
  cl.push_back({-xs[0], s[0][1]});
  for (int j = 2; j <= k; ++j) cl.push_back({-s[0][j]});
  for (int i = 1; i + 1 < n; ++i) {
    cl.push_back({-xs[i], s[i][1]});
    cl.push_back({-s[i - 1][1], s[i][1]});
    for (int j = 2; j <= k; ++j) {
      cl.push_back({-xs[i], -s[i - 1][j - 1], s[i][j]});
      cl.push_back({-s[i - 1][j], s[i][j]});
    }
    cl.push_back({-xs[i], -s[i - 1][k]});
  }
  cl.push_back({-xs[n - 1], -s[n - 2][k]});
}

}  // namespace

TEST(cardinality_pigeonhole_cliques) {
  // PHP with h holes: one at-most-one clique of h + 1 pigeons per hole, all binary clauses inside
  // them; the pigeon clauses are at-least-one only.
  for (int holes = 3; holes <= 9; ++holes) {
    const CardinalityStats st = detect(holes * (holes + 1), pigeonhole(holes));
    CHECK_EQ(st.amo, static_cast<uint64_t>(holes));
    CHECK_EQ(st.amo_pos, static_cast<uint64_t>(holes));
    for (const uint32_t size : st.amo_sizes) CHECK_EQ(size, static_cast<uint32_t>(holes + 1));
    CHECK_EQ(st.amo_binaries, static_cast<uint64_t>(holes * holes * (holes + 1) / 2));
    CHECK_EQ(st.amo_binaries, st.binaries);
    CHECK_EQ(st.eo, 0u);
    CHECK_EQ(st.vars_covered, static_cast<uint64_t>(holes * (holes + 1)));
    CHECK(!st.incomplete);
  }
  // Functional PHP (pigeons also at most one hole, as php_sudoku): the pigeon clauses become
  // exactly-one constraints, each equal to a detected clique.
  const int holes = 6;
  ClauseList f = pigeonhole(holes);
  auto x = [](int p, int h) { return p * holes + h + 1; };
  for (int p = 0; p <= holes; ++p) {
    for (int h = 0; h < holes; ++h) {
      for (int g = h + 1; g < holes; ++g) f.push_back({-x(p, h), -x(p, g)});
    }
  }
  const CardinalityStats st = detect(holes * (holes + 1), f);
  CHECK_EQ(st.amo, static_cast<uint64_t>(2 * holes + 1));
  CHECK_EQ(st.eo, static_cast<uint64_t>(holes + 1));
  CHECK_EQ(st.eo_clique, static_cast<uint64_t>(holes + 1));
  CHECK_EQ(st.eo_exact, static_cast<uint64_t>(holes + 1));
  CHECK_EQ(st.vars_amo2, static_cast<uint64_t>(holes * (holes + 1)));
  CHECK_EQ(st.clauses_covered, st.binaries + st.long_clauses);
}

TEST(cardinality_auxiliary_encodings) {
  // Exactly-one with the at-most-one part as a sequential counter (ladder): found through binary
  // implication paths. At-most-2 as a sequential counter: found by propagation, with k = 2.
  const int n = 10;
  std::vector<int> xs;
  for (int i = 1; i <= n; ++i) xs.push_back(i);
  ClauseList eo;
  int next = n + 1;
  sequential_counter(eo, xs, 1, next);
  eo.push_back(xs);
  CardinalityStats st = detect(next - 1, eo);
  CHECK_EQ(st.eo, 1u);
  CHECK_EQ(st.eo_big, 1u);
  ClauseList am2;
  next = n + 1;
  sequential_counter(am2, xs, 2, next);
  st = detect(next - 1, am2);
  CHECK_EQ(st.amk, 1u);
  REQUIRE(!st.amk_sizes.empty());
  CHECK_EQ(st.amk_sizes[0].second, 2u);
  CHECK(st.amk_sizes[0].first >= static_cast<uint32_t>(n - 2));
}

TEST(cardinality_detection_keeps_the_search) {
  // Statistics only: the same search with and without detection (before search and after the
  // first elimination round).
  std::mt19937_64 rng(7);
  for (int it = 0; it < 20; ++it) {
    ClauseList f = it % 2 ? pigeonhole(5 + it % 3) : random_formula(rng, 60, 255, 2, 4);
    int n = 0;
    for (const auto& c : f) {
      for (int l : c) n = std::max(n, std::abs(l));
    }
    Stats ref;
    int ref_result = 0;
    for (int card = 0; card <= 2; ++card) {
      Options o;
      o.cardinality = card;
      o.bva = it % 4 == 1;
      Solver s(o);
      s.reserve(n);
      for (const auto& c : f) {
        for (int l : c) s.add(l);
        s.add(0);
      }
      const int r = s.solve();
      if (card == 0) {
        ref = s.stats();
        ref_result = r;
        continue;
      }
      CHECK_EQ(r, ref_result);
      CHECK_EQ(s.stats().conflicts, ref.conflicts);
      CHECK_EQ(s.stats().decisions, ref.decisions);
      CHECK_EQ(s.stats().propagations, ref.propagations);
      CHECK_EQ(s.stats().ticks, ref.ticks);
    }
  }
}

namespace {

// Counting principles as at-least-one clauses plus pairwise at-most-one binary clauses.

// Functional pigeonhole: pigeons in exactly one hole, holes with at most one pigeon.
ClauseList functional_php(int pigeons, int holes) {
  ClauseList cl;
  auto x = [holes](int p, int h) { return p * holes + h + 1; };
  for (int p = 0; p < pigeons; ++p) {
    std::vector<int> c;
    for (int h = 0; h < holes; ++h) c.push_back(x(p, h));
    cl.push_back(c);
    for (int h = 0; h < holes; ++h) {
      for (int g = h + 1; g < holes; ++g) cl.push_back({-x(p, h), -x(p, g)});
    }
  }
  for (int h = 0; h < holes; ++h) {
    for (int p = 0; p < pigeons; ++p) {
      for (int q = p + 1; q < pigeons; ++q) cl.push_back({-x(p, h), -x(q, h)});
    }
  }
  return cl;
}

// A clique of `slots` vertices in the complete `parts`-partite graph with parts of `size` vertices
// (clique_n<size>_k<slots> of the SAT competitions): every slot takes one vertex, two slots take
// adjacent vertices (of different parts). Pigeonhole with `size` variables per (slot, part).
ClauseList clique_formula(int slots, int parts, int size) {
  ClauseList cl;
  const int verts = parts * size;
  auto x = [verts](int s, int v) { return s * verts + v + 1; };
  for (int s = 0; s < slots; ++s) {
    std::vector<int> c;
    for (int v = 0; v < verts; ++v) c.push_back(x(s, v));
    cl.push_back(c);
    for (int v = 0; v < verts; ++v) {
      for (int w = v + 1; w < verts; ++w) cl.push_back({-x(s, v), -x(s, w)});
    }
  }
  for (int s = 0; s < slots; ++s) {
    for (int t = s + 1; t < slots; ++t) {
      for (int v = 0; v < verts; ++v) {
        for (int w = 0; w < verts; ++w) {
          if (v / size == w / size) cl.push_back({-x(s, v), -x(t, w)});  // same part: not adjacent
        }
      }
    }
  }
  return cl;
}

// Perfect matching of K_n (parity principle: unsatisfiable iff n is odd).
ClauseList matching(int n) {
  std::vector<std::vector<int>> e(static_cast<size_t>(n), std::vector<int>(static_cast<size_t>(n), 0));
  int vars = 0;
  for (int a = 0; a < n; ++a) {
    for (int b = a + 1; b < n; ++b) e[a][b] = e[b][a] = ++vars;
  }
  ClauseList cl;
  for (int a = 0; a < n; ++a) {
    std::vector<int> c;
    for (int b = 0; b < n; ++b) {
      if (b != a) c.push_back(e[a][b]);
    }
    cl.push_back(c);
    for (size_t i = 0; i < c.size(); ++i) {
      for (size_t j = i + 1; j < c.size(); ++j) cl.push_back({-c[i], -c[j]});
    }
  }
  return cl;
}

// Partition of n points into triples (Count^3: unsatisfiable iff n is not divisible by 3).
ClauseList triples(int n) {
  std::vector<std::vector<int>> through(static_cast<size_t>(n));
  int vars = 0;
  for (int a = 0; a < n; ++a) {
    for (int b = a + 1; b < n; ++b) {
      for (int c = b + 1; c < n; ++c) {
        ++vars;
        for (int p : {a, b, c}) through[p].push_back(vars);
      }
    }
  }
  ClauseList cl;
  for (const auto& c : through) {
    cl.push_back(c);
    for (size_t i = 0; i < c.size(); ++i) {
      for (size_t j = i + 1; j < c.size(); ++j) cl.push_back({-c[i], -c[j]});
    }
  }
  return cl;
}

int max_var_of(const ClauseList& f) {
  int n = 0;
  for (const auto& c : f) {
    for (int l : c) n = std::max(n, std::abs(l));
  }
  return n;
}

// Renames the variables, flips polarities and shuffles clauses and literals.
ClauseList scramble(const ClauseList& f, std::mt19937_64& rng) {
  const int vars = max_var_of(f);
  std::vector<int> perm(static_cast<size_t>(vars) + 1);
  for (int v = 0; v <= vars; ++v) perm[v] = v;
  std::shuffle(perm.begin() + 1, perm.end(), rng);
  std::vector<int> flip(static_cast<size_t>(vars) + 1);
  for (int v = 1; v <= vars; ++v) flip[v] = rng() % 2 ? -1 : 1;
  ClauseList out;
  for (const auto& c : f) {
    std::vector<int> d;
    for (int l : c) d.push_back((l > 0 ? 1 : -1) * flip[std::abs(l)] * perm[std::abs(l)]);
    std::shuffle(d.begin(), d.end(), rng);
    out.push_back(d);
  }
  std::shuffle(out.begin(), out.end(), rng);
  return out;
}

struct CountingCase {
  std::string name;
  ClauseList f;
};

// The unsatisfiable (or the satisfiable) members of the families, several sizes each.
std::vector<CountingCase> counting_cases(bool unsat) {
  std::vector<CountingCase> v;
  auto add = [&](const std::string& name, ClauseList f, bool u) {
    if (u == unsat) v.push_back({name, std::move(f)});
  };
  // (Sizes where the at-least-one clauses have 3 or more literals: binary ones are not looked at.)
  for (int h = 3; h <= 6; ++h) {
    const std::string hs = std::to_string(h);
    add("php" + hs, pigeonhole(h), true);
    add("fphp" + std::to_string(h + 1) + "_" + hs, functional_php(h + 1, h), true);
    add("fphp" + std::to_string(h + 3) + "_" + hs, functional_php(h + 3, h), true);
    add("fphp" + hs + "_" + hs, functional_php(h, h), false);
    add("fphp" + std::to_string(h - 1) + "_" + hs, functional_php(h - 1, h), false);
  }
  add("clique4_3x2", clique_formula(4, 3, 2), true);
  add("clique5_4x2", clique_formula(5, 4, 2), true);
  add("clique4_3x3", clique_formula(4, 3, 3), true);
  add("clique3_3x2", clique_formula(3, 3, 2), false);
  add("clique3_4x3", clique_formula(3, 4, 3), false);
  for (int n = 4; n <= 10; ++n) add("matching" + std::to_string(n), matching(n), n % 2 == 1);
  for (int n = 4; n <= 9; ++n) add("triples" + std::to_string(n), triples(n), n % 3 != 0);
  return v;
}

// Solves with --counting and a text proof; the proof is checked with the PR-aware test checker.
struct CountingRun {
  int result = 0;
  Stats stats;
  uint64_t proof_pr = 0;
  psat_test::RupResult check;
};

CountingRun run_counting(const ClauseList& f, const Options& o) {
  CountingRun out;
  const int n = max_var_of(f);
  std::string proof_text;
  ProofWriter proof([&](const char* d, size_t k) { proof_text.append(d, k); }, false);
  Solver s(o);
  s.set_proof(&proof);
  s.reserve(n);
  for (const auto& c : f) s.add_clause(c.data(), c.size());
  out.result = s.solve();
  proof.flush();
  out.stats = s.stats();
  out.proof_pr = proof.pr();
  if (out.result == kUnsat) {
    psat_test::RupChecker checker(n);
    for (const auto& c : f) checker.add_original(c);
    out.check = checker.check_text_proof(proof_text);
  }
  return out;
}

}  // namespace

TEST(proof_pr_lines) {
  // A PR line is the clause and then the witness, which repeats the clause's first literal; in
  // the binary format the same literals form one 'a' record.
  const Lit c[2] = {from_dimacs(-3), from_dimacs(-10)};
  const Lit w[4] = {from_dimacs(-3), from_dimacs(1), from_dimacs(12), from_dimacs(-10)};
  std::string text, bin;
  {
    ProofWriter p([&](const char* d, size_t k) { text.append(d, k); }, false);
    p.add_pr(c, 2, w, 4);
    CHECK_EQ(p.pr(), 1u);
    CHECK_EQ(p.added(), 1u);
  }
  CHECK(text == "-3 -10 -3 1 12 -10 0\n");
  {
    ProofWriter p([&](const char* d, size_t k) { bin.append(d, k); }, true);
    p.add_pr(c, 2, w, 4);
  }
  // -3 -> 7, -10 -> 21, 1 -> 2, 12 -> 24.
  CHECK(bin == std::string("a\x07\x15\x07\x02\x18\x15\x00", 8));
}

TEST(rup_checker_pr_lines) {
  // The test checker accepts a PR clause with a correct witness and rejects a wrong witness.
  // x1 v x2, -x1 v -x2 (exactly one of two): (-x1) is PR with the witness {-x1, x2}, not RUP.
  psat_test::RupChecker good(2);
  good.add_original({1, 2});
  good.add_original({-1, -2});
  CHECK(good.check_text_proof("-1 -1 2 0\n").ok);
  psat_test::RupChecker bad(2);
  bad.add_original({1, 2});
  bad.add_original({-1, -2});
  CHECK(!bad.check_text_proof("-1 -1 -2 0\n").ok);  // the witness falsifies x1 v x2
}

TEST(counting_certifies_counting_principles) {
  // Pigeonhole (plain, functional, clique formulas with k variables per pair), parity and Count^3,
  // also scrambled (renamed variables, flipped polarities): refuted by the PR clauses and units
  // before search; the proof (PR lines included) checks.
  std::mt19937_64 rng(11);
  for (const CountingCase& t : counting_cases(true)) {
    for (int scrambled = 0; scrambled < 2; ++scrambled) {
      Options o;
      o.counting = 1;
      o.lucky = scrambled;  // (the root propagated by lucky before the pass, or not)
      const CountingRun r = run_counting(scrambled ? scramble(t.f, rng) : t.f, o);
      CHECK_EQ(r.result, kUnsat);
      CHECK_EQ(r.stats.counting_found, 1u);
      CHECK_EQ(r.stats.counting_failed, 0u);
      CHECK_EQ(r.stats.conflicts, 0u);
      CHECK_EQ(r.proof_pr, r.stats.counting_pr);
      CHECK_EQ(r.check.pr, r.stats.counting_pr);
      CHECK(r.check.ok && r.check.has_empty);
      if (!r.check.ok || !r.check.has_empty || r.stats.counting_found != 1) {
        std::fprintf(stderr, "  %s (scrambled %d): %s\n", t.name.c_str(), scrambled, r.check.error.c_str());
      }
    }
  }
}

TEST(counting_independent_pigeonhole_systems) {
  // Disjoint pigeonhole systems (homer: two PHP 11 -> 10): the cheapest unsatisfiable one with a
  // valid structure is refuted, the others are left alone.
  auto shifted = [](ClauseList f, int by) {
    for (auto& c : f) {
      for (int& l : c) l += l > 0 ? by : -by;
    }
    return f;
  };
  auto join = [](ClauseList a, const ClauseList& b) {
    a.insert(a.end(), b.begin(), b.end());
    return a;
  };
  std::mt19937_64 rng(14);
  const ClauseList two = join(pigeonhole(5), shifted(pigeonhole(4), 30));  // PHP 6 -> 5 and 5 -> 4
  const ClauseList sat_and_unsat = join(functional_php(5, 5), shifted(functional_php(6, 5), 25));
  ClauseList broken = pigeonhole(4);  // PHP 5 -> 4 without one at-most-one clause: satisfiable
  broken.erase(std::find(broken.begin(), broken.end(), std::vector<int>{-1, -5}));
  const ClauseList broken_and_unsat = join(broken, shifted(pigeonhole(6), 20));
  for (const ClauseList& f : {two, sat_and_unsat, broken_and_unsat}) {
    for (int scrambled = 0; scrambled < 2; ++scrambled) {
      Options o;
      o.counting = 1;
      const CountingRun r = run_counting(scrambled ? scramble(f, rng) : f, o);
      CHECK_EQ(r.result, kUnsat);
      CHECK_EQ(r.stats.counting_found, 1u);
      CHECK_EQ(r.stats.counting_failed, 0u);
      CHECK_EQ(r.stats.conflicts, 0u);
      CHECK(r.check.ok && r.check.has_empty);
    }
  }
}

TEST(counting_satisfiable_variants) {
  // Pigeons <= holes, even K_n, 3 | n: nothing found, a correct model.
  std::mt19937_64 rng(12);
  for (const CountingCase& t : counting_cases(false)) {
    for (int scrambled = 0; scrambled < 2; ++scrambled) {
      Options o;
      o.counting = 1;
      const ClauseList f = scrambled ? scramble(t.f, rng) : t.f;
      Outcome r = run(max_var_of(f), f, o);
      CHECK_EQ(r.result, kSat);
      CHECK(r.model_ok);
      if (r.result != kSat || !r.model_ok) std::fprintf(stderr, "  %s (scrambled %d)\n", t.name.c_str(), scrambled);
    }
  }
}

TEST(counting_refuses_wrong_steps) {
  // A wrong witness (--countingfault) fails the PR check: nothing is written for it, the structure
  // is abandoned with the steps before it kept, and search finishes with a proof that checks.
  for (const CountingCase& t : counting_cases(true)) {
    for (int fault : {1, 2, 5}) {
      Options o;
      o.counting = 1;
      o.countingfault = fault;
      const CountingRun r = run_counting(t.f, o);
      CHECK_EQ(r.result, kUnsat);
      if (r.stats.counting_failed) CHECK_EQ(r.stats.counting_pr, static_cast<uint64_t>(fault - 1));
      CHECK(r.check.ok && r.check.has_empty);
      if (!r.check.ok || !r.check.has_empty) std::fprintf(stderr, "  %s fault %d: %s\n", t.name.c_str(), fault, r.check.error.c_str());
    }
  }
  // Where the plan has PR steps, the first fault is always caught.
  const CountingRun r = run_counting(functional_php(6, 5), [] {
    Options o;
    o.counting = 1;
    o.countingfault = 3;
    return o;
  }());
  CHECK_EQ(r.stats.counting_failed, 1u);
  CHECK_EQ(r.stats.counting_pr, 2u);
  CHECK_EQ(r.result, kUnsat);
  CHECK(r.check.ok && r.check.has_empty);
}

TEST(counting_keeps_the_search_without_structure) {
  // Nothing found: the same search with and without the pass (statistics compared).
  std::mt19937_64 rng(13);
  std::vector<ClauseList> formulas = {functional_php(6, 6), matching(8), triples(6), clique_formula(3, 3, 2)};
  for (int it = 0; it < 12; ++it) formulas.push_back(random_formula(rng, 60, 255, 2, 4));
  ClauseList php_less = pigeonhole(5);  // a pigeonhole without one at-most-one clause
  php_less.erase(std::find(php_less.begin(), php_less.end(), std::vector<int>{-1, -6}));
  formulas.push_back(php_less);
  // Input clauses with a repeated literal or a tautology: the checker's formula may differ from
  // the solver's (dpr-trim reads "-1 -1 -7 0" as a PR line), so the pass is not run.
  ClauseList php_dup = pigeonhole(5);
  php_dup.back().insert(php_dup.back().begin(), php_dup.back()[0]);
  formulas.push_back(php_dup);
  ClauseList php_taut = matching(7);
  php_taut.push_back({1, -1, 2});
  formulas.push_back(php_taut);
  for (const ClauseList& f : formulas) {
    const int n = max_var_of(f);
    Stats ref;
    int ref_result = 0;
    for (int counting = 0; counting <= 1; ++counting) {
      Options o;
      o.counting = counting;
      Solver s(o);
      s.reserve(n);
      for (const auto& c : f) s.add_clause(c.data(), c.size());
      const int r = s.solve();
      CHECK_EQ(s.stats().counting_found, 0u);
      if (!counting) {
        ref = s.stats();
        ref_result = r;
        continue;
      }
      CHECK_EQ(r, ref_result);
      CHECK_EQ(s.stats().conflicts, ref.conflicts);
      CHECK_EQ(s.stats().decisions, ref.decisions);
      CHECK_EQ(s.stats().propagations, ref.propagations);
      CHECK_EQ(s.stats().ticks, ref.ticks);
    }
  }
}

TEST(counting_with_option_variants) {
  // The pass under the schedule-stressing option sets (it runs before search either way).
  for (const Options& base : option_variants()) {
    Options o = base;
    o.counting = 1;
    for (const ClauseList& f : {functional_php(6, 5), matching(7), triples(7)}) {
      Outcome r = run(max_var_of(f), f, o);
      CHECK_EQ(r.result, kUnsat);
      CHECK(r.proof_ok);
      if (!r.proof_ok) std::fprintf(stderr, "  %s\n", r.proof_error.c_str());
    }
  }
}

TEST(counting_rejects_clauses_after_certificates) {
  // PR clauses are redundant for the formula they come from, not for an extension of it. (Here
  // two PR clauses are added before a fault stops the pass, and search stops at once.)
  Options o;
  o.counting = 1;
  o.countingfault = 3;
  o.eliminate = 0;
  Solver s(o);
  for (const auto& c : matching(7)) s.add_clause(c.data(), c.size());
  s.set_conflict_limit(0);
  CHECK_EQ(s.solve(), kUnknown);
  CHECK_EQ(s.stats().counting_pr, 2u);
  bool thrown = false;
  try {
    s.add(1);
    s.add(0);
  } catch (const std::logic_error&) {
    thrown = true;
  }
  CHECK(thrown);
}

namespace {

// Clique-colouring (clqcl_<n>_<k>_<m> of the SAT competitions): a graph on n vertices (edge
// variables) with a k-clique (positions pick vertices) that is m-colourable. Unsatisfiable iff
// k > m.
ClauseList clique_colouring(int n, int k, int m) {
  int next = 0;
  std::vector<std::vector<int>> e(static_cast<size_t>(n), std::vector<int>(static_cast<size_t>(n), 0));
  for (int u = 0; u < n; ++u) {
    for (int v = u + 1; v < n; ++v) e[u][v] = e[v][u] = ++next;
  }
  std::vector<std::vector<int>> q(static_cast<size_t>(k), std::vector<int>(static_cast<size_t>(n)));
  for (auto& row : q) {
    for (int& x : row) x = ++next;
  }
  std::vector<std::vector<int>> r(static_cast<size_t>(n), std::vector<int>(static_cast<size_t>(m)));
  for (auto& row : r) {
    for (int& x : row) x = ++next;
  }
  ClauseList cl;
  auto exactly_one = [&cl](const std::vector<int>& xs) {
    cl.push_back(xs);
    for (size_t i = 0; i < xs.size(); ++i) {
      for (size_t j = i + 1; j < xs.size(); ++j) cl.push_back({-xs[i], -xs[j]});
    }
  };
  for (const auto& row : q) exactly_one(row);
  for (int u = 0; u < n; ++u) {
    for (int i = 0; i < k; ++i) {
      for (int j = i + 1; j < k; ++j) cl.push_back({-q[i][u], -q[j][u]});
    }
  }
  for (int i = 0; i < k; ++i) {
    for (int j = i + 1; j < k; ++j) {
      for (int u = 0; u < n; ++u) {
        for (int v = 0; v < n; ++v) {
          if (u != v) cl.push_back({-q[i][u], -q[j][v], e[u][v]});
        }
      }
    }
  }
  for (const auto& row : r) exactly_one(row);
  for (int u = 0; u < n; ++u) {
    for (int v = u + 1; v < n; ++v) {
      for (int c = 0; c < m; ++c) cl.push_back({-e[u][v], -r[u][c], -r[v][c]});
    }
  }
  return cl;
}

// Colouring with m colours of a random graph on n vertices (edge probability p) with a planted
// clique on the first `clique` vertices; at-most-one colour per vertex if `amo`.
ClauseList graph_colouring(int n, int m, int clique, double p, bool amo, std::mt19937_64& rng) {
  auto x = [m](int u, int c) { return u * m + c + 1; };
  ClauseList cl;
  for (int u = 0; u < n; ++u) {
    std::vector<int> c;
    for (int i = 0; i < m; ++i) c.push_back(x(u, i));
    cl.push_back(c);
    if (!amo) continue;
    for (int i = 0; i < m; ++i) {
      for (int j = i + 1; j < m; ++j) cl.push_back({-x(u, i), -x(u, j)});
    }
  }
  std::uniform_real_distribution<double> coin(0, 1);
  for (int u = 0; u < n; ++u) {
    for (int v = u + 1; v < n; ++v) {
      if ((u < clique && v < clique) || coin(rng) < p) {
        for (int c = 0; c < m; ++c) cl.push_back({-x(u, c), -x(v, c)});
      }
    }
  }
  return cl;
}

}  // namespace

// Relativized pigeonhole (rphp_p<n>_r<r>): n pigeons rest at r places, a place hosts at most one
// pigeon, the places in use map injectively into h holes. Unsatisfiable iff n > h (with r >= n).
ClauseList relativized_php(int n, int r, int h) {
  auto p = [r](int i, int u) { return i * r + u + 1; };
  auto used = [n, r](int u) { return n * r + u + 1; };
  auto q = [n, r, h](int u, int k) { return n * r + r + u * h + k + 1; };
  ClauseList cl;
  for (int i = 0; i < n; ++i) {
    std::vector<int> c;
    for (int u = 0; u < r; ++u) c.push_back(p(i, u));
    cl.push_back(c);
  }
  for (int u = 0; u < r; ++u) {
    for (int i = 0; i < n; ++i) {
      for (int j = i + 1; j < n; ++j) cl.push_back({-p(i, u), -p(j, u)});
      cl.push_back({-p(i, u), used(u)});
    }
    std::vector<int> c = {-used(u)};
    for (int k = 0; k < h; ++k) c.push_back(q(u, k));
    cl.push_back(c);
  }
  for (int u = 0; u < r; ++u) {
    for (int v = u + 1; v < r; ++v) {
      for (int k = 0; k < h; ++k) cl.push_back({-used(u), -used(v), -q(u, k), -q(v, k)});
    }
  }
  return cl;
}

TEST(counting_relativized_pigeonhole) {
  // As many places as pigeons: pigeon m rests at place m, then the places into the holes; more
  // places: the clique-colouring plan. Plain and scrambled; satisfiable ones are not refuted.
  std::mt19937_64 rng(17);
  for (const auto& [n, r, h] : std::vector<std::tuple<int, int, int>>{{5, 5, 4}, {6, 6, 5}, {4, 6, 3}, {5, 6, 4}}) {
    for (int scrambled = 0; scrambled < 2; ++scrambled) {
      Options o;
      o.counting = 1;
      const ClauseList f = relativized_php(n, r, h);
      const CountingRun res = run_counting(scrambled ? scramble(f, rng) : f, o);
      CHECK_EQ(res.result, kUnsat);
      CHECK_EQ(res.stats.counting_found, 1u);
      CHECK_EQ(res.stats.counting_failed, 0u);
      CHECK_EQ(res.stats.conflicts, 0u);
      CHECK(res.check.ok && res.check.has_empty);
      if (!res.check.ok || !res.check.has_empty) std::fprintf(stderr, "  rphp %d %d %d: %s\n", n, r, h, res.check.error.c_str());
    }
  }
  for (const auto& [n, r, h] : std::vector<std::tuple<int, int, int>>{{4, 4, 4}, {4, 6, 4}}) {
    Options o;
    o.counting = 1;
    const ClauseList f = scramble(relativized_php(n, r, h), rng);
    Outcome res = run(max_var_of(f), f, o);
    CHECK_EQ(res.result, kSat);
    CHECK(res.model_ok);
  }
  Options o;  // a wrong witness: refused, search finishes, the proof checks
  o.counting = 1;
  o.countingfault = 4;
  const CountingRun res = run_counting(relativized_php(5, 5, 4), o);
  CHECK_EQ(res.result, kUnsat);
  CHECK_EQ(res.stats.counting_failed, 1u);
  CHECK_EQ(res.stats.counting_pr, 3u);
  CHECK(res.check.ok && res.check.has_empty);
}

TEST(counting_clique_colouring) {
  // Refuted before search with 4-literal PR clauses (positions swap) and RUP lemmas; plain and
  // scrambled; the satisfiable ones (k <= m) are not recognised. (Colour clauses of 3 or more
  // literals: binary ones are not looked at.)
  std::mt19937_64 rng(15);
  for (const auto& [n, k, m] : std::vector<std::tuple<int, int, int>>{{6, 4, 3}, {7, 4, 3}, {6, 5, 3}, {5, 4, 3}}) {
    for (int scrambled = 0; scrambled < 2; ++scrambled) {
      Options o;
      o.counting = 1;
      const ClauseList f = clique_colouring(n, k, m);
      const CountingRun r = run_counting(scrambled ? scramble(f, rng) : f, o);
      CHECK_EQ(r.result, kUnsat);
      CHECK_EQ(r.stats.counting_found, 1u);
      CHECK_EQ(r.stats.counting_failed, 0u);
      CHECK_EQ(r.stats.conflicts, 0u);
      CHECK(r.stats.counting_pr > 0);
      CHECK(r.check.ok && r.check.has_empty);
      if (!r.check.ok || !r.check.has_empty) std::fprintf(stderr, "  clqcl %d %d %d: %s\n", n, k, m, r.check.error.c_str());
    }
  }
  for (const auto& [n, k, m] : std::vector<std::tuple<int, int, int>>{{6, 3, 3}, {6, 4, 4}}) {
    Options o;
    o.counting = 1;
    const ClauseList f = scramble(clique_colouring(n, k, m), rng);
    Outcome r = run(max_var_of(f), f, o);
    CHECK_EQ(r.result, kSat);
    CHECK(r.model_ok);
  }
  // A wrong witness: the check refuses it, search finishes, the proof checks.
  Options o;
  o.counting = 1;
  o.countingfault = 7;
  const CountingRun r = run_counting(clique_colouring(6, 4, 3), o);
  CHECK_EQ(r.result, kUnsat);
  CHECK_EQ(r.stats.counting_failed, 1u);
  CHECK_EQ(r.stats.counting_pr, 6u);
  CHECK(r.check.ok && r.check.has_empty);
}

TEST(counting_embedded_pigeonhole) {
  // A pigeonhole system inside a larger formula (PHP with other clauses on its variables, graph
  // colouring with a clique larger than the number of colours): refuted on its own, the proof
  // deletes the other clauses on its variables first.
  std::mt19937_64 rng(16);
  std::vector<ClauseList> formulas;
  ClauseList php_extra = pigeonhole(5);
  php_extra.push_back({1, 2, -3});
  php_extra.push_back({-7, 31, 32});
  php_extra.push_back({-31, -32});
  formulas.push_back(php_extra);
  for (int amo = 0; amo < 2; ++amo) {
    formulas.push_back(graph_colouring(12, 4, 5, 0.3, amo, rng));
    formulas.push_back(graph_colouring(16, 5, 6, 0.4, amo, rng));
  }
  for (const ClauseList& base : formulas) {
    for (int scrambled = 0; scrambled < 2; ++scrambled) {
      Options o;
      o.counting = 1;
      const CountingRun r = run_counting(scrambled ? scramble(base, rng) : base, o);
      CHECK_EQ(r.result, kUnsat);
      CHECK_EQ(r.stats.counting_found, 1u);
      CHECK_EQ(r.stats.counting_failed, 0u);
      CHECK_EQ(r.stats.conflicts, 0u);
      CHECK(r.check.ok && r.check.has_empty);
      CHECK(r.check.deletions > 0);
      if (!r.check.ok || !r.check.has_empty) std::fprintf(stderr, "  embedded: %s\n", r.check.error.c_str());
    }
  }
  // A wrong witness in the isolated refutation: nothing of it is written, search refutes the
  // formula, the proof checks.
  for (const ClauseList& base : formulas) {
    Options o;
    o.counting = 1;
    o.countingfault = 2;
    const CountingRun r = run_counting(base, o);
    CHECK_EQ(r.result, kUnsat);
    CHECK_EQ(r.stats.counting_failed, 1u);
    CHECK_EQ(r.stats.counting_pr, 0u);
    CHECK(r.check.ok && r.check.has_empty);
  }
  // Colourings whose cliques are not larger than the number of colours: not recognised, the
  // search is the same.
  for (int it = 0; it < 4; ++it) {
    const ClauseList f = graph_colouring(14, 4, 4, 0.15, it % 2, rng);
    Stats ref;
    for (int counting = 0; counting <= 1; ++counting) {
      Options o;
      o.counting = counting;
      Solver s(o);
      s.reserve(max_var_of(f));
      for (const auto& c : f) s.add_clause(c.data(), c.size());
      s.solve();
      CHECK_EQ(s.stats().counting_found, 0u);
      if (!counting) {
        ref = s.stats();
      } else {
        CHECK_EQ(s.stats().conflicts, ref.conflicts);
        CHECK_EQ(s.stats().propagations, ref.propagations);
      }
    }
  }
}

namespace {

// The clauses of x1 + ... + xk = parity (DIMACS variables): one clause per assignment of the
// wrong parity, excluding it.
void add_xor(ClauseList& cl, const std::vector<int>& vars, int parity) {
  const int k = static_cast<int>(vars.size());
  for (int a = 0; a < (1 << k); ++a) {
    int ones = 0;
    for (int i = 0; i < k; ++i) ones += (a >> i) & 1;
    if ((ones & 1) == parity) continue;
    std::vector<int> c;
    for (int i = 0; i < k; ++i) {
      const int v = vars[static_cast<size_t>(i)];
      c.push_back(((a >> i) & 1) ? -v : v);
    }
    cl.push_back(c);
  }
}

// Random XOR-heavy formula over n variables: `xors` random XORs over 2..5 distinct variables, some
// of them chunked through an auxiliary variable (n grows), plus `extra` random clauses.
ClauseList random_xor_formula(std::mt19937_64& rng, int& n, int xors, int extra) {
  ClauseList cl;
  std::uniform_int_distribution<int> var(1, n), len(2, 5), coin(0, 1);
  const int base = n;
  for (int i = 0; i < xors; ++i) {
    std::vector<int> vs;
    const int k = std::min(len(rng), base);
    while (static_cast<int>(vs.size()) < k) {
      const int v = var(rng);
      if (std::find(vs.begin(), vs.end(), v) == vs.end()) vs.push_back(v);
    }
    const int parity = coin(rng);
    if (k >= 4 && coin(rng)) {  // chunked: t = v0 + v1, t + v2 + ... = parity
      const int t = ++n;
      add_xor(cl, {vs[0], vs[1], t}, 0);
      std::vector<int> rest(vs.begin() + 2, vs.end());
      rest.push_back(t);
      add_xor(cl, rest, parity);
    } else {
      add_xor(cl, vs, parity);
    }
  }
  std::uniform_int_distribution<int> any(1, base), clen(2, 4);
  for (int i = 0; i < extra; ++i) {
    std::vector<int> c;
    const int k = clen(rng);
    for (int j = 0; j < k; ++j) c.push_back(coin(rng) ? any(rng) : -any(rng));
    cl.push_back(c);
  }
  return cl;
}

std::vector<Options> gauss_variants() {
  std::vector<Options> v;
  Options g;
  g.gauss = 1;
  g.gaussmin = 0;
  g.gaussxors = 1;
  v.push_back(g);
  Options r = g;  // tiny budgets: the detached solver runs in many short rounds during the search
  r.gaussproof = 0;  // (inconsistent XORs reach the detached solver too)
  r.gaussinit = 0;
  r.gaussint = 1;
  r.gausseffort = 100;
  r.lucky = 0;
  r.reduceint = 10;
  r.rephaseint = 10;
  r.modeinit = 10;
  v.push_back(r);
  r.gaussdecide = 0;  // the same with the detached solver's plain decision order
  r.stable = 2;
  v.push_back(r);
  for (Options o : option_variants()) {  // the main solver's stress variants with Gauss-Jordan on
    o.gauss = 1;
    o.gaussmin = 0;
    o.gaussxors = 1;
    o.gaussproof = static_cast<int64_t>(v.size() % 2);
    o.lucky = 0;
    v.push_back(o);
  }
  return v;
}

Outcome run_with_stats(int n, const ClauseList& clauses, const Options& opts, GaussStats& gs) {
  Outcome out;
  std::string proof_text;
  ProofWriter proof([&](const char* d, size_t k) { proof_text.append(d, k); }, false);
  Solver s(opts);
  s.set_proof(&proof);
  s.reserve(n);
  for (const auto& c : clauses) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  out.result = s.solve();
  proof.flush();
  gs = s.gauss_stats();
  if (out.result == kSat) {
    out.model_ok = true;
    for (const auto& c : clauses) {
      bool sat = false;
      for (int l : c) sat = sat || s.val(l) == l;
      if (!sat) out.model_ok = false;
    }
  }
  if (out.result == kUnsat) {
    psat_test::RupChecker checker(n);
    for (const auto& c : clauses) checker.add_original(c);
    const auto r = checker.check_text_proof(proof_text);
    out.proof_ok = r.ok && r.has_empty;
    out.proof_error = r.ok ? (r.has_empty ? "" : "no empty clause") : r.error;
  }
  return out;
}

void print_formula(int n, const ClauseList& cl) {
  std::fprintf(stderr, "  p cnf %d %zu\n", n, cl.size());
  for (const auto& c : cl) {
    std::fprintf(stderr, "   ");
    for (int l : c) std::fprintf(stderr, " %d", l);
    std::fprintf(stderr, " 0\n");
  }
}

}  // namespace

TEST(gauss_random_xor_formulas_vs_brute_force) {
  // XOR-heavy formulas, SAT and UNSAT, against the brute-force oracle. The detached solver must
  // be sound on its own as well: a model from it is checked like any other, and when it reports
  // UNSAT (ignored by the main solver, which proves it) the formula must be unsatisfiable.
  std::mt19937_64 rng(2027);
  const auto variants = gauss_variants();
  int sat = 0, unsat = 0, models = 0, sub_unsat = 0, started = 0;
  for (int it = 0; it < 1200; ++it) {
    int n = 4 + static_cast<int>(rng() % 11);
    const int base = n;
    const int xors = 2 + static_cast<int>(rng() % static_cast<uint64_t>(base + 2));
    const int extra = static_cast<int>(rng() % static_cast<uint64_t>(base));
    const ClauseList cl = random_xor_formula(rng, n, xors, extra);
    const bool expected = psat_test::brute_force_sat(n, cl);
    const size_t vi = static_cast<size_t>(it) % variants.size();
    GaussStats gs;
    const Outcome r = run_with_stats(n, cl, variants[vi], gs);
    CHECK_EQ(r.result, expected ? kSat : kUnsat);
    if (gs.started) ++started;
    if (gs.model) ++models;
    if (gs.sub_result == kUnsat) ++sub_unsat;
    const bool sub_wrong = (gs.sub_result == kUnsat && expected) || (gs.model && !expected);
    CHECK(!sub_wrong);
    if (r.result != (expected ? kSat : kUnsat) || (r.result == kSat && !r.model_ok) || sub_wrong ||
        (r.result == kUnsat && !r.proof_ok)) {
      std::fprintf(stderr, "  formula %d, variant %zu, detached solver result %d: %s\n", it, vi, gs.sub_result,
                   r.proof_error.c_str());
      print_formula(n, cl);
    }
    if (r.result == kSat) {
      ++sat;
      CHECK(r.model_ok);
    } else if (r.result == kUnsat) {
      ++unsat;
      CHECK(r.proof_ok);
    }
  }
  CHECK(sat > 200);
  CHECK(unsat > 200);
  CHECK(started > 600);
  CHECK(models > 100);
  CHECK(sub_unsat > 100);
}

namespace {

// Lights Out on a w x w grid: pressing a cell toggles it and its neighbours; random target
// pattern. A pure GF(2) system (XORs of 3..5 variables), satisfiable or not depending on w.
ClauseList lights_out(int w, std::mt19937_64& rng) {
  ClauseList cl;
  auto x = [w](int r, int c) { return r * w + c + 1; };
  for (int r = 0; r < w; ++r) {
    for (int c = 0; c < w; ++c) {
      std::vector<int> vs{x(r, c)};
      if (r > 0) vs.push_back(x(r - 1, c));
      if (r + 1 < w) vs.push_back(x(r + 1, c));
      if (c > 0) vs.push_back(x(r, c - 1));
      if (c + 1 < w) vs.push_back(x(r, c + 1));
      add_xor(cl, vs, static_cast<int>(rng() & 1));
    }
  }
  return cl;
}

// Noisy parity in the style of par32: samples (3 hidden bits) with given parities, each with an
// error variable that flips it; errors at most one per pair of samples (a side constraint the
// XORs do not cover).
std::pair<int, ClauseList> noisy_parity(int bits, int samples, std::mt19937_64& rng) {
  ClauseList cl;
  int n = bits;
  std::vector<int> hidden(static_cast<size_t>(bits));
  for (int& h : hidden) h = static_cast<int>(rng() & 1);
  std::vector<int> err;
  for (int s = 0; s < samples; ++s) {
    std::vector<int> vs;
    while (vs.size() < 3) {
      const int v = 1 + static_cast<int>(rng() % static_cast<uint64_t>(bits));
      if (std::find(vs.begin(), vs.end(), v) == vs.end()) vs.push_back(v);
    }
    int p = 0;
    for (int v : vs) p ^= hidden[static_cast<size_t>(v - 1)];
    const bool noisy = rng() % 3 == 0;
    const int e = ++n;
    err.push_back(e);
    vs.push_back(e);
    add_xor(cl, vs, noisy ? p ^ 1 : p);
  }
  for (size_t i = 0; i + 1 < err.size(); i += 2) cl.push_back({-err[i], -err[i + 1]});
  return {n, cl};
}

}  // namespace

TEST(gauss_structured_xor_families) {
  // Lights Out (pure linear: the detached solver finds models without a Gauss-Jordan conflict)
  // and noisy parity (linear plus a side constraint): answers against the solver without
  // Gauss-Jordan, models checked, UNSAT proofs checked.
  std::mt19937_64 rng(11);
  const auto variants = gauss_variants();
  int lo_models = 0;
  for (int it = 0; it < 24; ++it) {
    const int w = 3 + it % 6;
    const ClauseList cl = lights_out(w, rng);
    const Outcome ref = run(w * w, cl, Options());
    REQUIRE(ref.result == kSat || ref.result == kUnsat);
    for (size_t vi = 0; vi < variants.size(); ++vi) {
      GaussStats gs;
      const Outcome r = run_with_stats(w * w, cl, variants[vi], gs);
      CHECK_EQ(r.result, ref.result);
      if (r.result == kSat) CHECK(r.model_ok);
      if (r.result == kUnsat) CHECK(r.proof_ok);
      CHECK(!(gs.sub_result == kUnsat && ref.result == kSat));
      if (gs.model) {
        ++lo_models;
        CHECK_EQ(gs.conflicts, 0u);
      }
    }
  }
  CHECK(lo_models > 50);
  for (int it = 0; it < 12; ++it) {
    const auto f = noisy_parity(24 + it, 40 + 2 * it, rng);
    const Outcome ref = run(f.first, f.second, Options());
    REQUIRE(ref.result == kSat || ref.result == kUnsat);
    for (size_t vi = 0; vi < variants.size(); vi += 3) {
      GaussStats gs;
      const Outcome r = run_with_stats(f.first, f.second, variants[vi], gs);
      CHECK_EQ(r.result, ref.result);
      if (r.result == kSat) CHECK(r.model_ok);
      if (r.result == kUnsat) CHECK(r.proof_ok);
      CHECK(!(gs.sub_result == kUnsat && ref.result == kSat));
    }
  }
}

TEST(gauss_gated_out_keeps_the_search) {
  // With --gauss=1 on a formula the gate rejects, the search is that of --gauss=0 (the default).
  std::mt19937_64 rng(5);
  for (int it = 0; it < 12; ++it) {
    int n = 40;
    const ClauseList f = it % 2 ? random_formula(rng, 60, 255, 2, 4) : random_xor_formula(rng, n, 30, 60);
    if (it % 2) n = 60;
    Stats ref;
    int ref_result = 0;
    for (int g = 0; g < 2; ++g) {
      Options o;
      o.gauss = g;
      o.gaussmin = 1000;  // gated out unless every clause is part of an XOR
      Solver s(o);
      s.reserve(n);
      for (const auto& c : f) {
        for (int l : c) s.add(l);
        s.add(0);
      }
      const int r = s.solve();
      if (g == 0) {
        ref = s.stats();
        ref_result = r;
        continue;
      }
      CHECK(!s.gauss_stats().started);
      CHECK_EQ(r, ref_result);
      if (s.gauss_stats().refutations) continue;  // (inconsistent XORs: answered before search)
      CHECK_EQ(s.stats().conflicts, ref.conflicts);
      CHECK_EQ(s.stats().decisions, ref.decisions);
      CHECK_EQ(s.stats().propagations, ref.propagations);
      CHECK_EQ(s.stats().ticks, ref.ticks);
    }
  }
}

TEST(gauss_refutation_proofs) {
  // Inconsistent XOR systems are refuted before search, with a DRAT proof that uses extension
  // variables (RAT definitions): Lights Out on singular grids, and random overdetermined systems
  // (some XORs chunked, some reduced by unit clauses, with unrelated extra clauses). Every proof
  // goes through the checker; on the smaller formulas, with --gaussproofsize=0 the refutation is
  // skipped and the search proves the same formulas, and the answers agree with --gauss=0.
  std::mt19937_64 rng(99);
  int refuted = 0, unsat = 0;
  auto check = [&](int n, const ClauseList& cl) {
    for (int size : {20000, 0}) {
      if (!size && n > 30) continue;  // (CDCL proofs of larger XOR systems: slow to check here)
      Options o;
      o.gauss = 1;
      o.gaussproofsize = size;
      o.lucky = 0;
      GaussStats gs;
      const Outcome r = run_with_stats(n, cl, o, gs);
      if (n <= 30) CHECK_EQ(r.result, run(n, cl, Options()).result);
      if (r.result == kSat) CHECK(r.model_ok);
      if (r.result == kUnsat) {
        CHECK(r.proof_ok);
        if (!r.proof_ok) {
          std::fprintf(stderr, "  refutation proof: %s\n", r.proof_error.c_str());
          print_formula(n, cl);
        }
        if (size) ++unsat;
      }
      if (size && gs.refutations) {
        ++refuted;
        CHECK_EQ(r.result, kUnsat);
        CHECK(gs.proof_lines > 0);
      }
      if (!size) CHECK_EQ(gs.proof_lines, 0u);
    }
  };
  for (int it = 0; it < 24; ++it) {
    const int w = std::vector<int>{4, 5, 9, 11}[static_cast<size_t>(it) % 4];
    check(w * w, lights_out(w, rng));
  }
  for (int it = 0; it < 150; ++it) {
    int n = 6 + static_cast<int>(rng() % 20);
    const int base = n;
    ClauseList cl = random_xor_formula(rng, n, base + 1 + static_cast<int>(rng() % 4), static_cast<int>(rng() % 3));
    for (int u = static_cast<int>(rng() % 3); u > 0; --u) {
      const int v = 1 + static_cast<int>(rng() % static_cast<uint64_t>(base));
      cl.push_back({rng() % 2 ? v : -v});
    }
    check(n, cl);
  }
  CHECK(refuted > 60);
  CHECK(unsat >= refuted);
}

TEST(gauss_xors_with_subsumed_clauses) {
  // XOR encodings in which some clauses are replaced by a binary clause over two of their
  // literals (a stronger formula, as in binary-tree-parity): the XOR is still extracted. Answers
  // against the brute-force oracle, models checked, proofs (refutations included) checked.
  std::mt19937_64 rng(31);
  uint64_t subsumed = 0;
  int sat = 0, unsat = 0;
  for (int it = 0; it < 300; ++it) {
    const int n = 5 + static_cast<int>(rng() % 9);
    ClauseList cl;
    const int m = n - 2 + static_cast<int>(rng() % 5);
    for (int x = 0; x < m; ++x) {
      std::vector<int> vs;
      while (vs.size() < 3) {
        const int v = 1 + static_cast<int>(rng() % static_cast<uint64_t>(n));
        if (std::find(vs.begin(), vs.end(), v) == vs.end()) vs.push_back(v);
      }
      ClauseList enc;
      add_xor(enc, vs, static_cast<int>(rng() & 1));
      for (auto& c : enc) {
        if (rng() % 4 == 0) c.erase(c.begin() + static_cast<std::ptrdiff_t>(rng() % 3));  // subsuming binary
        cl.push_back(c);
      }
    }
    const bool expected = psat_test::brute_force_sat(n, cl);
    Options o;
    o.gauss = 1;
    o.gaussmin = 0;
    o.gaussxors = 1;
    o.lucky = 0;
    o.gaussproof = it % 2;
    GaussStats gs;
    const Outcome r = run_with_stats(n, cl, o, gs);
    CHECK_EQ(r.result, expected ? kSat : kUnsat);
    CHECK(!(gs.sub_result == kUnsat && expected));
    subsumed += gs.subsumed;
    if (r.result == kSat) {
      ++sat;
      CHECK(r.model_ok);
    } else if (r.result == kUnsat) {
      ++unsat;
      CHECK(r.proof_ok);
      if (!r.proof_ok) {
        std::fprintf(stderr, "  formula %d: %s\n", it, r.proof_error.c_str());
        print_formula(n, cl);
      }
    }
  }
  CHECK(subsumed > 100);
  CHECK(sat > 30);
  CHECK(unsat > 30);
}

TEST(gauss_detached_solver_leaves_the_search) {
  // The detached solver runs besides the main search without changing it: on formulas it cannot
  // answer (UNSAT, no refutation), the main search with --gauss=1 (adaptive or fixed share, with
  // rounds after every interval) is that of --gauss=0, and its proof checks.
  std::mt19937_64 rng(77);
  int compared = 0;
  for (int it = 0; it < 60; ++it) {
    int n = 20 + static_cast<int>(rng() % 20);
    const ClauseList cl = random_xor_formula(rng, n, n / 2, 3 * n);
    Stats ref;
    int ref_result = 0;
    for (int g = 0; g < 3; ++g) {
      Options o;
      o.gauss = g > 0;
      o.gaussmin = 0;
      o.gaussxors = 1;
      o.gaussproof = 0;
      o.gaussint = 1;
      o.gaussinit = 1;
      o.gaussadapt = g == 1;
      std::string proof_text;
      ProofWriter proof([&](const char* d, size_t k) { proof_text.append(d, k); }, false);
      Solver s(o);
      s.set_proof(&proof);
      s.reserve(n);
      for (const auto& c : cl) {
        for (int l : c) s.add(l);
        s.add(0);
      }
      const int r = s.solve();
      proof.flush();
      if (g == 0) {
        ref = s.stats();
        ref_result = r;
        continue;
      }
      CHECK_EQ(r, ref_result);
      if (r != kUnsat || s.gauss_stats().model) continue;
      ++compared;
      CHECK_EQ(s.stats().conflicts, ref.conflicts);
      CHECK_EQ(s.stats().decisions, ref.decisions);
      CHECK_EQ(s.stats().propagations, ref.propagations);
      psat_test::RupChecker checker(n);
      for (const auto& c : cl) checker.add_original(c);
      const auto pr = checker.check_text_proof(proof_text);
      CHECK(pr.ok && pr.has_empty);
    }
  }
  CHECK(compared > 20);
}

TEST(gauss_adaptive_share) {
  // The share mechanics: with every round judged useless (--gaussshrink=1000) the detached solver
  // is stopped; with every round judged useful (--gaussgrow=0) the share reaches --gausseffort.
  // Answers and models checked either way.
  // Formulas: random 3-SAT near the threshold (search that takes rounds) and a chain of XORs.
  std::mt19937_64 rng(5150);
  int stopped = 0, maxed = 0;
  for (int it = 0; it < 30; ++it) {
    const int n = 110 + it % 30;
    std::pair<int, ClauseList> f{n, random_formula(rng, n, static_cast<int>(n * 4.26), 3, 3)};
    for (int k = 1; k + 2 <= 16; k += 2) add_xor(f.second, {k, k + 1, k + 2}, static_cast<int>(rng() & 1));
    for (int mode = 0; mode < 2; ++mode) {
      Options o;
      o.gauss = 1;
      o.gaussmin = 0;
      o.gaussxors = 1;
      o.gaussinit = 1;
      o.gaussint = mode == 0 ? 1 : 10;
      o.gausseffort = mode == 0 ? 512 : 8000;  // (growth needs 64 detached conflicts per evaluation)
      if (mode == 0) o.gaussshrink = 1000;
      if (mode == 1) o.gaussgrow = 0;
      o.lucky = 0;
      GaussStats gs;
      const Outcome r = run_with_stats(f.first, f.second, o, gs);
      REQUIRE(r.result == kSat || r.result == kUnsat);
      if (r.result == kSat) CHECK(r.model_ok);
      if (r.result == kUnsat) CHECK(r.proof_ok);
      if (mode == 0 && gs.stopped) {
        ++stopped;
        CHECK(!gs.model);
        CHECK(gs.max_share == 64u);  // (512 / 8, never grown)
      }
      if (mode == 1 && gs.max_share == 8000u) ++maxed;
    }
  }
  CHECK(stopped > 10);
  CHECK(maxed > 10);
}
