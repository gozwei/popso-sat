#pragma once
// Insertion sort for tiny fixed-size arrays (gate inputs, short clauses). Faster than std::sort
// at these sizes, and it avoids a gcc 13 false positive (-Warray-bounds) that std::sort's
// unrolled insertion step triggers on local arrays of fewer than 16 elements.

#include <cstdint>

namespace psat {

template <typename T>
inline void small_sort(T* a, uint32_t n) {
  for (uint32_t k = 1; k < n; ++k) {
    const T x = a[k];
    uint32_t j = k;
    for (; j > 0 && x < a[j - 1]; --j) a[j] = a[j - 1];
    a[j] = x;
  }
}

}  // namespace psat
