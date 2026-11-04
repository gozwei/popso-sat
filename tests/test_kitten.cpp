// Kitten (the sub-solver for sweeping) against brute force: random small formulas, several solves
// per instance under random assumptions. Models are checked; unsatisfiable results are checked
// as proofs: the learned clauses in order, then the final clause (or the empty clause), must all
// be RUP. Unsat cores (after an inconsistency) must be unsatisfiable on their own.

#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "psat/solver/kitten.hpp"
#include "rup_checker.hpp"
#include "test_framework.hpp"

using psat::Kitten;

namespace {

int to_int(Kitten::KLit l) { return static_cast<int>((l >> 1) + 1) * ((l & 1u) ? -1 : 1); }

bool brute_sat(int n, const std::vector<std::vector<int>>& cls) {
  for (uint32_t m = 0; m < (1u << n); ++m) {
    bool all = true;
    for (const auto& c : cls) {
      bool sat = false;
      for (const int l : c) {
        const bool v = (m >> (std::abs(l) - 1)) & 1u;
        sat = sat || (l > 0 ? v : !v);
      }
      if (!sat) {
        all = false;
        break;
      }
    }
    if (all) return true;
  }
  return false;
}

}  // namespace

TEST(kitten_random_with_assumptions) {
  std::mt19937_64 rng(4242);
  Kitten k;
  int sat = 0, unsat = 0, unknown = 0, cores = 0;
  size_t core_clauses = 0, all_clauses = 0;
  for (int round = 0; round < 600; ++round) {
    const int n = 3 + static_cast<int>(rng() % 10);
    const int m = static_cast<int>(n * (2 + rng() % 4));
    std::vector<std::vector<int>> cls;
    k.clear();
    k.resize(static_cast<uint32_t>(n));
    for (int i = 0; i < m; ++i) {
      std::vector<int> c;
      std::vector<Kitten::KLit> kc;
      const int len = 1 + static_cast<int>(rng() % 4);
      for (int j = 0; j < len; ++j) {
        const int v = static_cast<int>(rng() % n);
        const bool negv = rng() & 1u;
        c.push_back((v + 1) * (negv ? -1 : 1));
        kc.push_back(static_cast<Kitten::KLit>(2 * v + (negv ? 1 : 0)));
      }
      k.add_clause(kc.data(), static_cast<uint32_t>(kc.size()), static_cast<uint32_t>(cls.size()));
      cls.push_back(c);
    }
    // Several solves on the same instance (learned clauses carry over).
    for (int s = 0; s < 4; ++s) {
      std::vector<int> assumed;
      const int na = static_cast<int>(rng() % 4);
      for (int a = 0; a < na; ++a) {
        const int v = static_cast<int>(rng() % n);
        const bool negv = rng() & 1u;
        assumed.push_back((v + 1) * (negv ? -1 : 1));
        k.assume(static_cast<Kitten::KLit>(2 * v + (negv ? 1 : 0)));
      }
      std::vector<std::vector<int>> with = cls;
      for (const int a : assumed) with.push_back({a});
      const bool expect = brute_sat(n, with);
      const int r = k.solve(1'000'000);
      if (r == Kitten::kUnknown) {
        ++unknown;
        continue;
      }
      CHECK_EQ(r == Kitten::kSat, expect);
      if (r == Kitten::kSat) {
        ++sat;
        for (const auto& c : with) {
          bool ok = false;
          for (const int l : c) {
            const Kitten::KLit kl = static_cast<Kitten::KLit>(2 * (std::abs(l) - 1) + (l < 0 ? 1 : 0));
            ok = ok || k.value(kl) > 0;
          }
          CHECK(ok);
        }
        continue;
      }
      ++unsat;
      // Proof: learned clauses, then the final clause (empty if inconsistent).
      std::string proof;
      for (size_t i = 0; i < k.num_learned(); ++i) {
        for (uint32_t j = 0; j < k.learned_size(i); ++j) proof += std::to_string(to_int(k.learned_lits(i)[j])) + " ";
        proof += "0\n";
      }
      for (const Kitten::KLit l : k.final_clause()) proof += std::to_string(to_int(l)) + " ";
      proof += "0\n";
      // Final clause: only negated assumptions.
      for (const Kitten::KLit l : k.final_clause()) {
        bool found = false;
        for (const int a : assumed) found = found || to_int(l) == -a;
        CHECK(found);
      }
      if (k.inconsistent()) CHECK(k.final_clause().empty());
      psat_test::RupChecker checker(n);
      for (const auto& c : cls) checker.add_original(c);
      const auto res = checker.check_text_proof(proof);
      CHECK(res.ok);
      if (!res.ok) std::fprintf(stderr, "  kitten proof (round %d, solve %d): %s\n", round, s, res.error.c_str());
      if (k.final_clause().empty()) CHECK(res.has_empty);
      if (k.inconsistent()) {
        // The core (original clauses by id) is unsatisfiable on its own.
        std::vector<uint32_t> ids;
        k.compute_core(ids);
        std::vector<std::vector<int>> core;
        for (const uint32_t id : ids) core.push_back(cls[id]);
        CHECK(!ids.empty());
        CHECK(!brute_sat(n, core));
        ++cores;
        core_clauses += ids.size();
        all_clauses += cls.size();
      }
    }
  }
  CHECK(sat > 100);
  CHECK(unsat > 100);
  CHECK_EQ(unknown, 0);
  CHECK(cores > 50);
  CHECK(core_clauses < all_clauses);  // cores are proper subsets on average
}
