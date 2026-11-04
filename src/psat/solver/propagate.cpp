// Boolean constraint propagation with two watched literals.
//
// Watch lists are indexed by the watched literal and visited when it becomes false. Long-clause
// watches carry a blocking literal: when it is true the clause is skipped without touching the
// arena. The two watched literals of a long clause are lits[0] and lits[1]; the replacement
// search resumes where the last one ended (Gent, JAIR 2013), which matters for long clauses.

#include "psat/solver/solver.hpp"

namespace psat {

bool Solver::propagate() { return propagate_impl<false>(kNoReason); }

// Vivification propagates without the clause being vivified, and books its ticks separately from
// search. Both skip garbage clauses (deleted in the proof already) and drop their watches.
bool Solver::propagate_vivify(uint32_t ignore) { return propagate_impl<true>(ignore); }

template <bool kVivify>
bool Solver::propagate_impl(uint32_t ignore) {
  has_conflict_ = false;
  const size_t start = propagated_;
  uint64_t ticks = 0;
  while (propagated_ < trail_.size()) {
    const Lit lit = trail_[propagated_++];
    const Lit not_lit = negate(lit);
    std::vector<Watch>& ws = watches_[not_lit];
    Watch* const begin = ws.data();
    Watch* const end = begin + ws.size();
    Watch* i = begin;
    Watch* j = begin;
    ticks += 1 + (ws.size() >> 3);
    while (i != end) {
      const Watch w = *j++ = *i++;
      const int8_t bv = vals_[w.blit];
      if (bv > 0) continue;
      if (w.binary()) {
        if (bv < 0) {
          conflict_bin_[0] = not_lit;
          conflict_bin_[1] = w.blit;
          conflict_ref_ = kNoReason;
          has_conflict_ = true;
          break;
        }
        assign(w.blit, kBinaryTag | not_lit);
        continue;
      }
      ++ticks;
      Clause& c = clause(w.ref);
      if (c.garbage) {  // deleted clause (collections are deferred): drop its watch
        --j;
        continue;
      }
      if constexpr (kVivify) {
        if (w.ref == ignore) continue;
      }
      Lit* lits = c.lits();
      const Lit other = lits[0] ^ lits[1] ^ not_lit;
      const int8_t ov = vals_[other];
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
        rv = vals_[lits[k]];
        if (rv >= 0) break;
      }
      if (rv < 0) {
        for (k = 2; k < pos; ++k) {
          rv = vals_[lits[k]];
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
        watches_[r].push_back(Watch{other, w.ref});
        --j;
        continue;
      }
      if (ov < 0) {
        conflict_ref_ = w.ref;
        has_conflict_ = true;
        break;
      }
      assign(other, w.ref);
    }
    if (has_conflict_) {
      while (i != end) *j++ = *i++;
    }
    ws.resize(static_cast<size_t>(j - begin));
    if (has_conflict_) break;
  }
  stats_.propagations += propagated_ - start;
  if constexpr (kVivify) {
    stats_.vivify_ticks += ticks;
  } else {
    stats_.ticks += ticks;
  }
  return !has_conflict_;
}

}  // namespace psat
