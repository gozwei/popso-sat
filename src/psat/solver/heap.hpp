#pragma once
// Binary max-heap of variables ordered by an external score array (EVSIDS decisions).
//
// Each entry keeps a copy of its variable's score, so that sifting compares siblings in one
// cache line instead of loading two scores from the (large, randomly accessed) score array. The
// copies are kept equal to the array: push() and increased() read it, rescale() applies the
// same multiplication the caller applied to the array. The heap layout, hence the decision
// order, is the same as comparing through the array.

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
  Var top() const { return heap_[0].var; }
  void clear() {
    for (const Entry& e : heap_) pos_[e.var] = kAbsent;
    heap_.clear();
  }

  void push(Var v) {
    if (contains(v)) return;
    pos_[v] = static_cast<uint32_t>(heap_.size());
    heap_.push_back(Entry{score_[v], v});
    up(pos_[v]);
  }

  Var pop() {
    const Var v = heap_[0].var;
    const Entry last = heap_.back();
    heap_.pop_back();
    pos_[v] = kAbsent;
    if (!heap_.empty()) {
      heap_[0] = last;
      pos_[last.var] = 0;
      down(0);
    }
    return v;
  }

  // Call after score[v] increased.
  void increased(Var v) {
    if (!contains(v)) return;
    heap_[pos_[v]].score = score_[v];
    up(pos_[v]);
  }

  // Call after every score was multiplied by factor (the same operation on the copies).
  void rescale(double factor) {
    for (Entry& e : heap_) e.score *= factor;
  }

 private:
  struct Entry {
    double score;
    Var var;
  };

  void up(uint32_t i) {
    const Entry e = heap_[i];
    while (i > 0) {
      const uint32_t p = (i - 1) / 2;
      if (!(heap_[p].score < e.score)) break;
      heap_[i] = heap_[p];
      pos_[heap_[i].var] = i;
      i = p;
    }
    heap_[i] = e;
    pos_[e.var] = i;
  }

  void down(uint32_t i) {
    const Entry e = heap_[i];
    const uint32_t n = static_cast<uint32_t>(heap_.size());
    for (;;) {
      uint32_t c = 2 * i + 1;
      if (c >= n) break;
      if (c + 1 < n && heap_[c].score < heap_[c + 1].score) ++c;
      if (!(e.score < heap_[c].score)) break;
      heap_[i] = heap_[c];
      pos_[heap_[i].var] = i;
      i = c;
    }
    heap_[i] = e;
    pos_[e.var] = i;
  }

  const std::vector<double>& score_;
  std::vector<Entry> heap_;
  std::vector<uint32_t> pos_;
};

}  // namespace psat
