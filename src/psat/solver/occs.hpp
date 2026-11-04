#pragma once
// Occurrence lists for elimination rounds: one list of clause references per literal, all in one
// pool (a WordArena) instead of one std::vector per literal. On formulas with millions of
// variables the per-literal vectors cost a 24-byte header plus a separate heap block each and
// fragmented the heap; here a list is three words, sized exactly when the round builds the lists.
// A full list moves to the end of the pool with twice the capacity (the old space is abandoned
// until clear()). Pointers from begin() / end() are invalidated by push().

#include <algorithm>
#include <cstdint>
#include <new>
#include <vector>

#include "psat/core/word_arena.hpp"

namespace psat {

class OccLists {
 public:
  // Lists with capacity counts[l] each (all empty).
  void init(const std::vector<uint32_t>& counts) {
    heads_.assign(counts.size(), Head{});
    size_t total = 0;
    for (size_t l = 0; l < counts.size(); ++l) {
      heads_[l].begin = static_cast<uint32_t>(total);
      heads_[l].cap = counts[l];
      total += counts[l];
    }
    if (total > kMaxPool) throw std::bad_alloc();
    pool_.clear();
    pool_.reserve(total + total / 8 + 1024);
    pool_.resize(total);
  }
  void grow(size_t lists) {
    if (lists > heads_.size()) heads_.resize(lists, Head{});
  }
  void clear() {
    std::vector<Head>().swap(heads_);
    pool_.clear();
    pool_.shrink_to_fit();
  }
  size_t lists() const { return heads_.size(); }
  uint32_t size(size_t l) const { return heads_[l].size; }
  uint32_t* begin(size_t l) { return pool_.data() + heads_[l].begin; }
  uint32_t* end(size_t l) { return begin(l) + heads_[l].size; }
  void push(size_t l, uint32_t x) {
    Head& h = heads_[l];
    if (h.size == h.cap) relocate(h);
    pool_[size_t{h.begin} + h.size++] = x;
  }
  void truncate(size_t l, uint32_t n) {
    if (n < heads_[l].size) heads_[l].size = n;
  }
  void erase_value(size_t l, uint32_t x) {
    uint32_t* b = begin(l);
    uint32_t* e = std::remove(b, end(l), x);
    heads_[l].size = static_cast<uint32_t>(e - b);
  }

 private:
  static constexpr size_t kMaxPool = 0xFFFFFFF0u;
  struct Head {
    uint32_t begin = 0, size = 0, cap = 0;
  };
  void relocate(Head& h) {
    const uint32_t cap = std::max<uint32_t>(4, 2 * h.cap);
    const size_t at = pool_.size();
    if (at + cap > kMaxPool) throw std::bad_alloc();
    if (at + cap > pool_.capacity()) pool_.reserve(at + cap + pool_.capacity() / 4);
    pool_.resize(at + cap);
    std::copy(pool_.data() + h.begin, pool_.data() + h.begin + h.size, pool_.data() + at);
    h.begin = static_cast<uint32_t>(at);
    h.cap = cap;
  }

  std::vector<Head> heads_;
  WordArena pool_;
};

}  // namespace psat
