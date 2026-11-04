#pragma once
// Binary max-heap of variables ordered by an external score array (EVSIDS decisions).

#include <cstdint>
#include <vector>

#include "psat/core/types.hpp"

namespace psat {

class ScoreHeap {
 public:
  static constexpr uint32_t kAbsent = UINT32_MAX;

  explicit ScoreHeap(const std::vector<double>& score) : score_(score) {}

  void resize(size_t vars) { pos_.resize(vars, kAbsent); }
  bool contains(Var v) const { return pos_[v] != kAbsent; }
  bool empty() const { return heap_.empty(); }
  size_t size() const { return heap_.size(); }
  Var top() const { return heap_[0]; }
  void clear() {
    for (Var v : heap_) pos_[v] = kAbsent;
    heap_.clear();
  }

  void push(Var v) {
    if (contains(v)) return;
    pos_[v] = static_cast<uint32_t>(heap_.size());
    heap_.push_back(v);
    up(pos_[v]);
  }

  Var pop() {
    const Var v = heap_[0];
    const Var last = heap_.back();
    heap_.pop_back();
    pos_[v] = kAbsent;
    if (!heap_.empty()) {
      heap_[0] = last;
      pos_[last] = 0;
      down(0);
    }
    return v;
  }

  // Call after score[v] increased.
  void increased(Var v) {
    if (contains(v)) up(pos_[v]);
  }

 private:
  bool less(Var a, Var b) const { return score_[a] < score_[b]; }

  void up(uint32_t i) {
    const Var v = heap_[i];
    while (i > 0) {
      const uint32_t p = (i - 1) / 2;
      const Var pv = heap_[p];
      if (!less(pv, v)) break;
      heap_[i] = pv;
      pos_[pv] = i;
      i = p;
    }
    heap_[i] = v;
    pos_[v] = i;
  }

  void down(uint32_t i) {
    const Var v = heap_[i];
    const uint32_t n = static_cast<uint32_t>(heap_.size());
    for (;;) {
      uint32_t c = 2 * i + 1;
      if (c >= n) break;
      if (c + 1 < n && less(heap_[c], heap_[c + 1])) ++c;
      if (!less(v, heap_[c])) break;
      heap_[i] = heap_[c];
      pos_[heap_[c]] = i;
      i = c;
    }
    heap_[i] = v;
    pos_[v] = i;
  }

  const std::vector<double>& score_;
  std::vector<Var> heap_;
  std::vector<uint32_t> pos_;
};

}  // namespace psat
