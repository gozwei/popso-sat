// radix_sort_keys against std::sort: random keys of several widths and lengths, and keys whose
// low bits are left unordered (distinct high parts).

#include <algorithm>
#include <cstdint>
#include <random>
#include <vector>

#include "psat/core/radix_sort.hpp"
#include "test_framework.hpp"

TEST(radix_sort_keys_full) {
  std::mt19937_64 rng(11);
  std::vector<uint64_t> keys, tmp;
  for (int round = 0; round < 200; ++round) {
    const size_t n = rng() % 3000;
    const unsigned bits = 1 + static_cast<unsigned>(rng() % 64);
    keys.clear();
    for (size_t i = 0; i < n; ++i) {
      uint64_t k = rng();
      if (bits < 64) k &= (uint64_t{1} << bits) - 1;
      keys.push_back(k ^ (rng() % 4 == 0 ? uint64_t{0xFF00} << 40 : 0));
    }
    std::vector<uint64_t> expect = keys;
    std::sort(expect.begin(), expect.end());
    psat::radix_sort_keys(keys, tmp);
    REQUIRE(keys == expect);
  }
}

TEST(radix_sort_keys_high_part) {
  std::mt19937_64 rng(12);
  std::vector<uint64_t> keys, tmp;
  for (int round = 0; round < 200; ++round) {
    const size_t n = rng() % 2000;
    std::vector<uint64_t> high;
    for (size_t i = 0; i < n; ++i) high.push_back(i * (1 + rng() % 5) + rng() % 3 * 100000);
    std::sort(high.begin(), high.end());
    high.erase(std::unique(high.begin(), high.end()), high.end());
    std::shuffle(high.begin(), high.end(), rng);
    keys.clear();
    for (const uint64_t h : high) keys.push_back((h << 32) | (rng() & 0xFFFFFFFFu));
    std::vector<uint64_t> expect = keys;
    std::sort(expect.begin(), expect.end());
    psat::radix_sort_keys(keys, tmp, 32);
    REQUIRE(keys == expect);
  }
}
