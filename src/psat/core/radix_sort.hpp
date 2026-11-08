#pragma once
// Sorting 64-bit keys (ascending): least-significant-digit radix sort by bytes, skipping the bytes
// that are the same in every key and those below `low_bits` (bits the caller does not need
// ordered: with distinct keys above them, the order is the same as a full sort). Short arrays go to
// std::sort.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

namespace psat {

inline void radix_sort_keys(std::vector<uint64_t>& keys, std::vector<uint64_t>& tmp, unsigned low_bits = 0) {
  const size_t n = keys.size();
  if (n < 48) {
    std::sort(keys.begin(), keys.end());
    return;
  }
  uint64_t all = ~uint64_t{0}, any = 0;
  for (const uint64_t k : keys) {
    all &= k;
    any |= k;
  }
  const uint64_t varying = all ^ any;
  tmp.resize(n);
  uint64_t* src = keys.data();
  uint64_t* dst = tmp.data();
  for (unsigned shift = low_bits & ~7u; shift < 64; shift += 8) {
    if (!((varying >> shift) & 255)) continue;
    size_t pos[256] = {};
    for (size_t i = 0; i < n; ++i) ++pos[(src[i] >> shift) & 255];
    size_t sum = 0;
    for (size_t& p : pos) {
      const size_t c = p;
      p = sum;
      sum += c;
    }
    for (size_t i = 0; i < n; ++i) dst[pos[(src[i] >> shift) & 255]++] = src[i];
    std::swap(src, dst);
  }
  if (src != keys.data()) std::memcpy(keys.data(), src, n * sizeof(uint64_t));
}

}  // namespace psat
