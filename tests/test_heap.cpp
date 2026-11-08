// ScoreHeap: the decision order (including ties) is the textbook binary heap's.
#include <cstdint>
#include <vector>

#include "psat/solver/heap.hpp"
#include "test_framework.hpp"

using namespace psat;

namespace {

// The textbook max-heap on an external score array (sift down: larger child, the left one on
// ties, stop when no child is larger), the reference for ScoreHeap's layout.
struct ReferenceHeap {
  const std::vector<double>& score;
  std::vector<Var> heap;
  std::vector<uint32_t> pos;
  explicit ReferenceHeap(const std::vector<double>& s) : score(s), pos(s.size(), UINT32_MAX) {}
  bool contains(Var v) const { return pos[v] != UINT32_MAX; }
  void up(uint32_t i) {
    const Var v = heap[i];
    while (i > 0) {
      const uint32_t p = (i - 1) / 2;
      if (!(score[heap[p]] < score[v])) break;
      heap[i] = heap[p];
      pos[heap[i]] = i;
      i = p;
    }
    heap[i] = v;
    pos[v] = i;
  }
  void down(uint32_t i) {
    const Var v = heap[i];
    const uint32_t n = static_cast<uint32_t>(heap.size());
    for (;;) {
      uint32_t c = 2 * i + 1;
      if (c >= n) break;
      if (c + 1 < n && score[heap[c]] < score[heap[c + 1]]) ++c;
      if (!(score[v] < score[heap[c]])) break;
      heap[i] = heap[c];
      pos[heap[i]] = i;
      i = c;
    }
    heap[i] = v;
    pos[v] = i;
  }
  void push(Var v) {
    if (contains(v)) return;
    pos[v] = static_cast<uint32_t>(heap.size());
    heap.push_back(v);
    up(pos[v]);
  }
  Var pop() {
    const Var v = heap[0];
    const Var last = heap.back();
    heap.pop_back();
    pos[v] = UINT32_MAX;
    if (!heap.empty()) {
      heap[0] = last;
      pos[last] = 0;
      down(0);
    }
    return v;
  }
  void increased(Var v) {
    if (contains(v)) up(pos[v]);
  }
};

}  // namespace

TEST(score_heap_matches_textbook_order) {
  uint64_t rng = 88172645463325252ull;
  auto next = [&]() {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
  };
  for (const uint32_t n : {1u, 2u, 3u, 7u, 64u, 1000u}) {
    std::vector<double> score(n, 0.0);
    ScoreHeap heap(score);
    heap.resize(n);
    ReferenceHeap ref(score);
    for (Var v = 0; v < n; ++v) {
      heap.push(v);
      ref.push(v);
    }
    for (int step = 0; step < 20000; ++step) {
      const uint64_t r = next();
      const Var v = static_cast<Var>(r % n);
      switch ((r >> 32) % 4) {
        case 0:  // few distinct scores: many ties
          score[v] += static_cast<double>((r >> 40) % 3);
          heap.increased(v);
          ref.increased(v);
          break;
        case 1:
          if (!ref.heap.empty()) {
            REQUIRE(!heap.empty());
            CHECK_EQ(heap.top(), ref.heap[0]);
            CHECK_EQ(heap.pop(), ref.pop());
          }
          break;
        default:
          heap.push(v);
          ref.push(v);
          break;
      }
      CHECK_EQ(heap.size(), ref.heap.size());
    }
    while (!ref.heap.empty()) CHECK_EQ(heap.pop(), ref.pop());
    CHECK(heap.empty());
  }
}
