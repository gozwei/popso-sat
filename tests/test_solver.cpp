// CDCL solver: answers against a brute-force oracle, models against the formula, and every
// UNSAT answer's DRAT proof through the test-only RUP checker. Options that change schedules are
// pushed to extremes (tiny reduce / rephase / mode intervals) so that small formulas exercise
// reduction, garbage collection, mode switching and rephasing.

#include <cstdint>
#include <random>
#include <string>
#include <vector>

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
  Options c;
  c.stable = 2;
  c.target = 2;
  c.reluctantint = 2;
  c.reduceint = 10;
  c.tier1 = 1;
  c.tier2 = 1;
  v.push_back(c);
  Options d;
  d.seed = 12345;
  d.phase = 0;
  d.modeinit = 10;
  d.modegrowth = 100;
  d.restartmargin = 0;
  d.minimizedepth = 1;
  v.push_back(d);
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

TEST(solver_incremental_add_after_solve) {
  Solver s;
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
