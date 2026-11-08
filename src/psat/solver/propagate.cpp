// Boolean constraint propagation with two watched literals.
//
// Watch lists are indexed by the watched literal and visited when it becomes false. Long-clause
// watches carry a blocking literal: when it is true the clause is skipped without touching the
// arena. The two watched literals of a long clause are lits[0] and lits[1]; the replacement
// search resumes where the last one ended (Gent, JAIR 2013), which matters for long clauses.

#include <algorithm>
#include <cstddef>

#include "psat/solver/solver.hpp"

namespace psat {

// Prefetching the clause of the watch kPrefetchDistance ahead, in watch lists of at least
// kPrefetchList watches, pays where the arena does not fit the caches (M4: constraints_17, 21 MB
// of long clauses, -10% time; scc_9630, -6 to -11%); with smaller arenas it cost up to 3%
// (station-repacking, 6 MB), and without the list length gate 17-40% on ncc and 8% on
// linked_list (millions of variables, short lists, most blockers true). It changes nothing else.
// On the i7-7700K with 4 jobs sharing memory bandwidth (sc2026, 12 instances, two rounds) it cost
// ~20% (+15% against the build before it, where everything else gained ~5%); prefetching only
// where the blocking literal is not true halved that and won on constraints_16/17 but lost on
// post-cbmc and ntil. Hence --prefetch=0 by default.
constexpr std::ptrdiff_t kPrefetchDistance = 4;
constexpr size_t kPrefetchList = 16;
constexpr size_t kPrefetchArenaWords = size_t{1} << 21;  // 8 MB

bool Solver::propagate() {
  if (gauss_on_) return propagate_with_gauss();  // (the detached Gauss-Jordan solver only)
  return propagate_search();
}

bool Solver::propagate_search() {
  return opts_.prefetch && arena_.size() >= kPrefetchArenaWords ? propagate_impl<false, true>(kNoReason)
                                                                : propagate_impl<false, false>(kNoReason);
}

// Vivification propagates without the clause being vivified, and books its ticks separately from
// search. Both skip garbage clauses (deleted in the proof already) and drop their watches.
//
// With chronological backtracking (search only), an implied literal gets the highest level of the
// other literals of its reason. That is the current level whenever the propagated literal is on
// the current level, so the reason is scanned only while propagating a lower-level literal (kept
// on the trail by a chronological backtrack, or implied out of order).
bool Solver::propagate_vivify(uint32_t ignore) {
  return opts_.prefetch && arena_.size() >= kPrefetchArenaWords ? propagate_impl<true, true>(ignore)
                                                                : propagate_impl<true, false>(ignore);
}

template <bool kVivify, bool kPrefetch>
bool Solver::propagate_impl(uint32_t ignore) {
  has_conflict_ = false;
  const size_t start = propagated_;
  uint64_t ticks = 0;
  // Local copies of the arrays' base pointers: the int8_t stores of an assignment may alias any
  // object for the compiler, which would otherwise reload every member pointer after each one.
  // None of these arrays is reallocated during propagation (the trail has room for every
  // variable, see grow_vars()); only the watch pool can move (below).
  int8_t* const vals = vals_.data();
  VarData* const vdata = vdata_.data();
  int8_t* const saved = saved_.data();
  uint32_t* const arena = arena_.data();
  const uint32_t current = level();
  [[maybe_unused]] const bool prefetch_open_only = opts_.prefetch == 2;  // (kPrefetch only)
  size_t propagated = propagated_;
  bool conflict = false;
  // The assignment of assign_at(), inlined.
  const auto imply = [&](Lit l, uint32_t reason, uint32_t lvl) {
    const Var v = var_of(l);
    vals[l] = 1;
    vals[negate(l)] = -1;
    VarData& d = vdata[v];
    d.level = lvl;
    d.reason = lvl ? reason : kNoReason;
    d.trail = static_cast<uint32_t>(trail_.size());
    saved[v] = is_negative(l) ? -1 : 1;
    trail_.push_back(l);
    if (!lvl) on_root_fixed(l);
  };
  while (propagated < trail_.size()) {
    const Lit lit = trail_[propagated++];
    const Lit not_lit = negate(lit);
    uint32_t lit_level = current;
    bool lower = false;  // lit is below the current level: implied levels need a scan
    if constexpr (!kVivify) {
      if (opts_.chrono) {
        lit_level = vdata[var_of(lit)].level;
        lower = lit_level < current;
      }
    }
    // The list is a slice of the watch pool: moving a watch to another list can relocate that
    // list and grow (move) the pool, so the pointers are re-derived from the slice's begin index
    // (which only compaction changes) after every such push.
    const size_t list_size = watches_[not_lit].size();
    const uint32_t list_begin = watches_.begin_index(not_lit);
    Watch* begin = watches_.pool() + list_begin;
    Watch* end = begin + list_size;
    Watch* i = begin;
    Watch* j = begin;
    ticks += 1 + (list_size >> 3);
    [[maybe_unused]] const bool long_list = list_size >= kPrefetchList;  // (kPrefetch only)
    while (i != end) {
      if constexpr (kPrefetch) {
        if (long_list && end - i > kPrefetchDistance) {
          const Watch p = i[kPrefetchDistance];
          if (!p.binary() && (!prefetch_open_only || vals[p.blit] <= 0)) PSAT_PREFETCH(arena + p.ref);
        }
      }
      const Watch w = *j++ = *i++;
      const int8_t bv = vals[w.blit];
      if (bv > 0) continue;
      if (w.binary()) {
        if (bv < 0) {
          conflict_bin_[0] = not_lit;
          conflict_bin_[1] = w.blit;
          conflict_ref_ = kNoReason;
          conflict = true;
          break;
        }
        imply(w.blit, kBinaryTag | not_lit, lit_level);
        continue;
      }
      ++ticks;
      Clause& c = *reinterpret_cast<Clause*>(arena + w.ref);
      if (c.garbage) {  // deleted clause (collections are deferred): drop its watch
        --j;
        continue;
      }
      if constexpr (kVivify) {
        if (w.ref == ignore) continue;
      }
      Lit* lits = c.lits();
      const Lit other = lits[0] ^ lits[1] ^ not_lit;
      const int8_t ov = vals[other];
      if (ov > 0) {
        j[-1].blit = other;
        continue;
      }
      lits[0] = other;
      lits[1] = not_lit;
      const uint32_t size = c.size;
      uint32_t pos = c.pos;
      if (pos < 2 || pos >= size) pos = 2;
      uint32_t k = pos;
      int8_t rv = -1;
      for (; k < size; ++k) {
        rv = vals[lits[k]];
        if (rv >= 0) break;
      }
      if (rv < 0) {
        for (k = 2; k < pos; ++k) {
          rv = vals[lits[k]];
          if (rv >= 0) break;
        }
      }
      if (rv >= 0) {
        c.pos = k;
        const Lit r = lits[k];
        if (rv > 0) {
          // Satisfied by a non-watched literal: keep the watch, remember r as blocker.
          j[-1].blit = r;
          continue;
        }
        lits[1] = r;
        lits[k] = not_lit;
        --j;
        const size_t oi = static_cast<size_t>(i - begin), oj = static_cast<size_t>(j - begin);
        watches_.push_back(r, Watch{other, w.ref});
        Watch* const moved = watches_.pool() + list_begin;
        if (moved != begin) {
          begin = moved;
          i = begin + oi;
          j = begin + oj;
          end = begin + list_size;
        }
        continue;
      }
      if (ov < 0) {
        conflict_ref_ = w.ref;
        conflict = true;
        break;
      }
      if (lower) {
        uint32_t lvl = lit_level;
        for (uint32_t m = 2; m < size; ++m) lvl = std::max(lvl, vdata[var_of(lits[m])].level);
        ticks += size / 8;
        imply(other, w.ref, lvl);
      } else {
        imply(other, w.ref, current);
      }
    }
    if (conflict) {
      while (i != end) *j++ = *i++;
    }
    watches_[not_lit].resize(static_cast<size_t>(j - begin));
    if (conflict) break;
  }
  propagated_ = propagated;
  has_conflict_ = conflict;
  stats_.propagations += propagated - start;
  if constexpr (kVivify) {
    stats_.vivify_ticks += ticks;
  } else {
    stats_.ticks += ticks;
  }
  return !conflict;
}

}  // namespace psat
