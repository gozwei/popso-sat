// LitStack (the trail's container) against std::vector: pushes through growth, truncation,
// zero-filled extension, iteration.

#include <cstdint>
#include <random>
#include <vector>

#include "psat/core/lit_stack.hpp"
#include "test_framework.hpp"

TEST(lit_stack_model) {
  std::mt19937_64 rng(7);
  psat::LitStack s;
  std::vector<psat::Lit> model;
  for (int step = 0; step < 20000; ++step) {
    const int op = static_cast<int>(rng() % 100);
    if (op < 80) {
      const auto l = static_cast<psat::Lit>(rng() % 100000);
      s.push_back(l);
      model.push_back(l);
    } else if (op < 95) {
      const size_t n = model.empty() ? 0 : rng() % (model.size() + 1);
      s.resize(n);
      model.resize(n);
    } else {
      const size_t n = model.size() + rng() % 50;
      s.resize(n);
      model.resize(n);
    }
    REQUIRE(s.size() == model.size());
    REQUIRE(s.capacity() >= s.size());
    if (!model.empty()) CHECK_EQ(s.back(), model.back());
  }
  size_t k = 0;
  for (const psat::Lit l : s) CHECK_EQ(l, model[k++]);
  CHECK_EQ(k, model.size());
  s.clear();
  CHECK(s.empty());
  s.reserve(1000);
  CHECK(s.capacity() >= 1000);
  CHECK(s.empty());
}
