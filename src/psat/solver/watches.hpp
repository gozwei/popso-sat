#pragma once
// Watch lists of all literals in one pool.
//
// Each list is a slice of the pool given by a 12-byte head (begin, size, capacity) instead of a
// std::vector per literal (24-byte header plus one heap block per list, reallocated as the list
// grows: on formulas with millions of variables the headers, the unused capacity and the
// allocation churn of elimination rounds cost hundreds of MB).
//
// Every slice starts with a header entry (the list's index and the slice's capacity), so that the
// pool can be walked slice by slice. A list that outgrows its slice moves to the end of the pool
// with 1.5 times the capacity (or grows in place if it is the last slice); its old slice becomes
// garbage (its header no longer matches the list's head). The pool grows by realloc. compact()
// moves the live lists down in place, without gaps (no second pool: freeing whole pools showed
// up as resident memory on macOS); callers run it at points where no list is being iterated
// (maybe_compact(): when garbage and unused capacity exceed a quarter of the live entries; and
// at restarts once the pool's used part is twice the live entries of the last compaction, see
// compact_due()). Compaction leaves each list room for a quarter of its long-clause watches
// (plus 2): with exactly its size, nearly every list with long-clause watches moved to the end
// at its first new watch in the search that followed (as-p147: the used part went from 107 to
// 327 MB within 0.2 s and to 511 MB before the next collection, for 134 MB of live watches;
// with the room, half the list moves and half the compactions of exact sizes at 100k
// conflicts). Binary watches do not move, so lists of binary watches only get no room.
//
// Pointer validity: a WatchList view and its pointers stay valid while no list is relocated.
// push_back() or reserve() on one list can move that list and grow the pool, which moves every
// list; the begin index of the other lists stays the same until compact(). Code that iterates a
// list while pushing to another (propagation) re-derives its pointers from the begin index after
// the push (see pool()/begin_index()). In stress mode (debugging, --watchstress) every relocation
// copies the pool to a new block, so that any stale pointer is a use after free (AddressSanitizer)
// instead of an occasional one.

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>
#include <vector>

#include "psat/core/types.hpp"

namespace psat {

constexpr uint32_t kBinaryTag = 0x80000000u;
// Bits of a binary watch's ref besides the tag and the redundant flag (bit 0), read only by the
// code that sets them (binaries.cpp): --binstats marks a watch used in a propagation or conflict
// since learned and since the last census, and keeps the census count when it was learned (bits
// 4-30); --binreduce marks the watch of a learned binary clause it checked and kept.
constexpr uint32_t kBinaryUsed = 2u, kBinaryRecent = 4u, kBinaryChecked = 8u;
constexpr uint32_t kBinaryEpochShift = 4, kBinaryEpochMask = 0x07FFFFFFu;

struct Watch {
  Lit blit;      // blocking literal (the other literal for binary clauses)
  uint32_t ref;  // clause reference, or kBinaryTag | redundant-flag (| the bits above) for binary clauses

  bool binary() const { return (ref & kBinaryTag) != 0; }
  bool redundant_binary() const { return (ref & 1u) != 0; }
};

class WatchLists;

// A view of one literal's list (valid until a list is relocated, see above).
class WatchList {
 public:
  WatchList(WatchLists& lists, size_t l) : lists_(&lists), l_(static_cast<uint32_t>(l)) {}
  size_t size() const;
  bool empty() const { return size() == 0; }
  Watch* data() const;
  Watch* begin() const { return data(); }
  Watch* end() const { return data() + size(); }
  Watch& operator[](size_t i) const { return data()[i]; }
  Watch& back() const { return data()[size() - 1]; }
  // (const: a view, like a span; these change the list, not the view)
  void push_back(Watch w) const;
  void pop_back() const;
  void resize(size_t n) const;  // n <= size(): truncates
  void clear() const { resize(0); }
  void reserve(size_t n) const;
  void shrink_to_fit() const;  // gives the unused capacity back (as garbage until compaction)
  size_t capacity() const;

 private:
  WatchLists* lists_;
  uint32_t l_;
};

class ConstWatchList {
 public:
  ConstWatchList(const WatchLists& lists, size_t l) : lists_(&lists), l_(static_cast<uint32_t>(l)) {}
  size_t size() const;
  bool empty() const { return size() == 0; }
  const Watch* data() const;
  const Watch* begin() const { return data(); }
  const Watch* end() const { return data() + size(); }
  const Watch& operator[](size_t i) const { return data()[i]; }
  size_t capacity() const;

 private:
  const WatchLists* lists_;
  uint32_t l_;
};

class WatchLists {
 public:
  WatchLists() = default;
  WatchLists(const WatchLists&) = delete;
  WatchLists& operator=(const WatchLists&) = delete;
  ~WatchLists() { std::free(pool_); }

  // Number of lists (two per variable); resize() adds empty lists (never removes).
  size_t size() const { return heads_.size(); }
  void resize(size_t n) {
    if (n > heads_.size()) heads_.resize(n, Head{0, 0, 0});
  }
  void reserve_lists(size_t n) { heads_.reserve(n); }
  WatchList operator[](size_t l) { return WatchList(*this, l); }
  ConstWatchList operator[](size_t l) const { return ConstWatchList(*this, l); }

  Watch* pool() { return pool_; }
  uint32_t begin_index(size_t l) const { return heads_[l].begin; }

  void push_back(size_t l, Watch w) {
    Head& h = heads_[l];
    if (h.size == h.cap) grow(l, h.size + 1);
    pool_[heads_[l].begin + heads_[l].size++] = w;
  }
  void reserve(size_t l, size_t n) {
    if (n > heads_[l].cap) grow(l, n);
  }
  // An empty list gives its slice up (garbage until compaction); otherwise nothing changes until
  // compaction (which gives every slice exactly its size).
  void shrink_to_fit(size_t l) {
    Head& h = heads_[l];
    if (h.size || !h.cap) return;
    if (h.begin + h.cap == used_) used_ = h.begin - 1;  // the last slice: back to the pool
    h = Head{0, 0, 0};
  }

  // Moves the live lists down in pool order, each slice with capacity = size (empty lists lose
  // their slice), then gives the lists with long-clause watches their room (moving the slices up
  // again, last first), and shrinks the pool to the used part plus a tail of an eighth if more
  // than half of it would be unused. Invalidates every pointer and begin index.
  void compact() {
    size_t at = 0, pos = 0;
    std::vector<uint32_t> order;  // the live lists in pool order
    while (pos < used_) {
      const uint32_t id = pool_[pos].blit, cap = pool_[pos].ref;
      const size_t first = pos + 1;
      pos = first + cap;
      Head& h = heads_[id];
      if (h.begin != first || h.cap != cap) continue;  // garbage slice
      if (!h.size) {
        h = Head{0, 0, 0};
        continue;
      }
      pool_[at] = Watch{id, h.size};
      if (at + 1 != first) std::memmove(pool_ + at + 1, pool_ + first, h.size * sizeof(Watch));
      h.begin = static_cast<uint32_t>(at + 1);
      h.cap = h.size;
      at += 1 + h.size;
      order.push_back(id);
    }
    used_ = at;
    compacted_ = at;
    auto room = [&](const Head& h) {
      uint32_t longs = 0;
      for (uint32_t k = 0; k < h.size; ++k) longs += (pool_[h.begin + k].ref & kBinaryTag) == 0;
      return longs ? longs / 4 + 2 : 0u;
    };
    size_t extra = 0;
    for (const uint32_t id : order) extra += room(heads_[id]);
    if (extra) {
      // Slice i moves up by the room of the slices before it: from the last one down, every
      // destination lies above the slices not moved yet.
      ensure_pool(used_ + extra);
      size_t off = extra;
      for (size_t i = order.size(); i-- > 0;) {
        Head& h = heads_[order[i]];
        const uint32_t r = room(h);
        off -= r;
        if (off) std::memmove(pool_ + h.begin - 1 + off, pool_ + h.begin - 1, (size_t{h.size} + 1) * sizeof(Watch));
        h.begin = static_cast<uint32_t>(h.begin + off);
        h.cap += r;
        pool_[h.begin - 1].ref = h.cap;
      }
      used_ += extra;
    }
    granted_ = extra;
    // The tail goes back only if more than half of the pool would stay unused: lists grow again
    // after a compaction, and a pool shrunk to its used part is regrown soon (a copy and a freed
    // block on allocators without in-place growth).
    const size_t want = used_ + used_ / 8 + 1024;
    if (!stress_ && 2 * want < cap_) {
      void* p = std::realloc(pool_, want * sizeof(Watch));
      if (p) {
        pool_ = static_cast<Watch*>(p);
        cap_ = want;
      }
    }
    ++compactions_;
  }
  // The used part of the pool is twice the live entries of the last compaction (plus 8 MB):
  // garbage slices and unused capacity are as large as the lists. Cheap (no walk over the lists).
  bool compact_due() const { return !stress_ && used_ > 2 * compacted_ + (size_t{1} << 20); }
  // Compacts when garbage and unused capacity (beyond the room given at the last compaction)
  // exceed a quarter of the entries in use, or when compaction would give back more than half
  // of the pool (with the room as last given: the same test as compact()'s, so that a
  // compaction that keeps the pool does not repeat at every collection; always in stress mode).
  void maybe_compact() {
    size_t live = 0;
    for (const Head& h : heads_) live += h.size + (h.cap ? 1 : 0);
    const size_t after = live + granted_;
    if (stress_ || used_ - live > live / 4 + granted_ + 4096 || cap_ > 2 * (after + after / 8 + 1024)) compact();
  }
  void set_stress(bool on) { stress_ = on; }

  // Statistics: bytes allocated (heads and pool), live entries, unused capacity inside the
  // slices, garbage slices.
  size_t bytes() const { return heads_.capacity() * sizeof(Head) + cap_ * sizeof(Watch); }
  size_t head_bytes() const { return heads_.capacity() * sizeof(Head); }
  size_t pool_bytes() const { return cap_ * sizeof(Watch); }
  size_t live() const {
    size_t n = 0;
    for (const Head& h : heads_) n += h.size;
    return n;
  }
  size_t slack() const {
    size_t n = 0;
    for (const Head& h : heads_) n += h.cap - h.size;
    return n;
  }
  size_t garbage() const { return used_ - live() - slack() - nonempty(); }
  size_t nonempty() const {
    size_t n = 0;
    for (const Head& h : heads_) n += h.cap ? 1 : 0;
    return n;
  }
  size_t used() const { return used_; }
  uint64_t relocations() const { return relocations_; }
  uint64_t compactions() const { return compactions_; }

 private:
  friend class WatchList;
  friend class ConstWatchList;
  struct Head {
    uint32_t begin, size, cap;
  };

  static Watch* allocate(size_t n) {
    void* p = std::malloc(n * sizeof(Watch));
    if (!p) throw std::bad_alloc();
    return static_cast<Watch*>(p);
  }
  // Pool capacity for at least n entries (by realloc, or a fresh copy in stress mode).
  void ensure_pool(size_t n) {
    if (n <= cap_ && !stress_) return;
    // (Stress mode copies even when the pool has room, at the same capacity then: growing it on
    // every copy compounded to 1.7G entries in the unit test, which Linux refuses to allocate.)
    size_t want = n <= cap_ ? cap_ : cap_ + cap_ / 4 + 1024;
    if (want < n) want = n;
    if (want > kMaxEntries) want = kMaxEntries;
    if (want < n) throw std::bad_alloc();  // (begin indices are 32-bit)
    if (stress_) {
      Watch* fresh = allocate(want);
      if (used_) std::memcpy(fresh, pool_, used_ * sizeof(Watch));
      std::free(pool_);
      pool_ = fresh;
    } else {
      void* p = std::realloc(pool_, want * sizeof(Watch));
      if (!p) throw std::bad_alloc();
      pool_ = static_cast<Watch*>(p);
    }
    cap_ = want;
  }
  // Gives list l capacity for at least n entries: in place if it is the last slice, else a new
  // slice (header + 1.5 times the capacity) at the end of the pool.
  void grow(size_t l, size_t n) {
    ++relocations_;
    Head h = heads_[l];
    size_t cap = h.cap ? size_t{h.cap} + size_t{h.cap} / 2 + 1 : 2;
    if (cap < n) cap = n;
    if (h.cap && h.begin + h.cap == used_ && !stress_) {
      ensure_pool(h.begin + cap);
      used_ = h.begin + cap;
      heads_[l].cap = static_cast<uint32_t>(cap);
      pool_[h.begin - 1].ref = static_cast<uint32_t>(cap);
      return;
    }
    ensure_pool(used_ + 1 + cap);
    const size_t at = used_ + 1;
    pool_[used_] = Watch{static_cast<uint32_t>(l), static_cast<uint32_t>(cap)};
    if (h.size) std::memcpy(pool_ + at, pool_ + h.begin, h.size * sizeof(Watch));
    used_ = at + cap;
    heads_[l].begin = static_cast<uint32_t>(at);
    heads_[l].cap = static_cast<uint32_t>(cap);
  }

  static constexpr size_t kMaxEntries = 0xFFFFFFF0u;
  std::vector<Head> heads_;
  Watch* pool_ = nullptr;
  size_t cap_ = 0, used_ = 0;
  size_t compacted_ = 0;  // live entries (with slice headers) after the last compaction
  size_t granted_ = 0;    // room given to the lists by the last compaction
  uint64_t relocations_ = 0, compactions_ = 0;
  bool stress_ = false;
};

inline size_t WatchList::size() const { return lists_->heads_[l_].size; }
inline Watch* WatchList::data() const { return lists_->pool_ + lists_->heads_[l_].begin; }
inline void WatchList::push_back(Watch w) const { lists_->push_back(l_, w); }
inline void WatchList::pop_back() const { --lists_->heads_[l_].size; }
inline void WatchList::resize(size_t n) const { lists_->heads_[l_].size = static_cast<uint32_t>(n); }
inline void WatchList::reserve(size_t n) const { lists_->reserve(l_, n); }
inline void WatchList::shrink_to_fit() const { lists_->shrink_to_fit(l_); }
inline size_t WatchList::capacity() const { return lists_->heads_[l_].cap; }
inline size_t ConstWatchList::size() const { return lists_->heads_[l_].size; }
inline const Watch* ConstWatchList::data() const { return lists_->pool_ + lists_->heads_[l_].begin; }
inline size_t ConstWatchList::capacity() const { return lists_->heads_[l_].cap; }

}  // namespace psat
