// CDCL solver: answers against a brute-force oracle, models against the formula, and every
// UNSAT answer's DRAT proof through the test-only RUP checker. Options that change schedules are
// pushed to extremes (tiny reduce / rephase / mode intervals) so that small formulas exercise
// reduction, garbage collection, mode switching and rephasing.

#include <cstdint>
#include <random>
#include <stdexcept>
#include <string>
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
  Solver s;
  for (const auto& c : pigeonhole(8)) {
    for (int l : c) s.add(l);
    s.add(0);
  }
  s.set_conflict_limit(100);
  CHECK_EQ(s.solve(), kUnknown);
  CHECK(std::string(s.unknown_reason()) == "conflict limit");
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
