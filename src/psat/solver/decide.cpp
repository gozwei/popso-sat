// Decision heuristics: VMTF queue in focused mode, EVSIDS scores on a binary heap in stable mode
// (the Kissat combination), with saved / target phases.

#include <algorithm>
#include <cstdint>

#include "psat/core/radix_sort.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

// --- VMTF queue ------------------------------------------------------------------------------

void Solver::queue_enqueue_last(Var v) {
  Link& l = links_[v];
  l.prev = queue_last_;
  l.next = UINT32_MAX;
  if (queue_last_ != UINT32_MAX) {
    links_[queue_last_].next = v;
  } else {
    queue_first_ = v;
  }
  queue_last_ = v;
  bumped_[v] = ++queue_stamp_;
  if (vals_[make_lit(v, false)] == 0) queue_search_ = v;
}

void Solver::queue_dequeue(Var v) {
  Link& l = links_[v];
  if (l.prev != UINT32_MAX) {
    links_[l.prev].next = l.next;
  } else {
    queue_first_ = l.next;
  }
  if (l.next != UINT32_MAX) {
    links_[l.next].prev = l.prev;
  } else {
    queue_last_ = l.prev;
  }
  l.prev = l.next = UINT32_MAX;
}

void Solver::queue_bump(Var v) {
  if (links_[v].next == UINT32_MAX) return;  // already last
  queue_dequeue(v);
  queue_enqueue_last(v);
}

Var Solver::next_focused() {
  Var v = queue_search_;
  while (vals_[make_lit(v, false)] != 0) v = links_[v].prev;
  queue_search_ = v;
  return v;
}

// --- EVSIDS ----------------------------------------------------------------------------------

void Solver::heap_bump(Var v) {
  double s = score_[v] + score_inc_;
  if (s > 1e150) {
    for (double& x : score_) x *= 1e-150;
    heap_.rescale(1e-150);
    score_inc_ *= 1e-150;
    s = score_[v] + score_inc_;
  }
  score_[v] = s;
  heap_.increased(v);
}

// Eliminated (and substituted) variables leave the decision queue for good.
void Solver::drop_inactive_decisions() {
  for (Var v = 0; v < num_vars_; ++v) {
    if (eliminated_[v] && (links_[v].prev != UINT32_MAX || links_[v].next != UINT32_MAX || queue_first_ == v)) {
      queue_dequeue(v);
    }
  }
  queue_search_ = queue_last_;
  if (stable_) rebuild_heap();
}

void Solver::rebuild_heap() {
  heap_.clear();
  for (Var k = 0; k < num_vars_; ++k) {
    const Var v = internal_var(k);  // (in input order: ties fall the same after a renumbering)
    if (vals_[make_lit(v, false)] == 0 && !eliminated_[v]) heap_.push(v);
  }
}

Var Solver::next_stable() {
  for (;;) {
    const Var v = heap_.top();
    if (vals_[make_lit(v, false)] == 0) return v;
    heap_.pop();
  }
}

void Solver::bump_variables() {
  if (stable_) {
    for (Var v : analyzed_) heap_bump(v);
    score_inc_ *= 1000.0 / (1000.0 - static_cast<double>(opts_.decay));
    return;
  }
  // Move to the front in the order of the previous enqueue times, keeping their relative order.
  // The times are distinct, so the order does not depend on the sort. They are sorted as 64-bit
  // keys (time - earliest) << 32 | variable (radix sort on the time bytes), read once per
  // variable, instead of reading two times per comparison; if the times span 2^32 or more, by the
  // times directly.
  uint64_t lo = UINT64_MAX, hi = 0;
  for (const Var v : analyzed_) {
    const uint64_t t = bumped_[v];
    lo = std::min(lo, t);
    hi = std::max(hi, t);
  }
  if (analyzed_.empty() || hi - lo > UINT32_MAX) {
    std::sort(analyzed_.begin(), analyzed_.end(), [this](Var a, Var b) { return bumped_[a] < bumped_[b]; });
  } else {
    sort_keys_.clear();
    for (const Var v : analyzed_) sort_keys_.push_back(((bumped_[v] - lo) << 32) | v);
    radix_sort_keys(sort_keys_, sort_tmp_, 32);
    for (size_t k = 0; k < sort_keys_.size(); ++k) analyzed_[k] = static_cast<Var>(sort_keys_[k]);
  }
  for (Var v : analyzed_) queue_bump(v);
}

// --- decisions -------------------------------------------------------------------------------

bool Solver::decide() {
  Var v;
  if (randec_left_) {
    v = random_decision();
    ++stats_.random_decisions;
  } else if (stable_) {
    v = next_stable();
  } else {
    v = next_focused();
    // The next decision's search starts at v (assigned by then) and goes to its predecessor in
    // the queue: its link and value are prefetched (millions of variables: both are misses).
    const Var p = links_[v].prev;
    if (p != UINT32_MAX) {
      PSAT_PREFETCH(links_.data() + p);
      PSAT_PREFETCH(vals_.data() + 2 * size_t{p});
    }
  }
  if (gauss_on_ && v < gauss_mat_.size() && gauss_mat_[v] != UINT32_MAX && opts_.gaussdecide) v = gauss_decision(v);
  int8_t phase = saved_[v];
  if (opts_.target == 2 || (opts_.target == 1 && stable_)) {
    if (target_[v]) phase = target_[v];
  }
  ++stats_.decisions;
  control_.push_back(static_cast<uint32_t>(trail_.size()));
  assign(make_lit(v, phase < 0), kNoReason);
  return true;
}

}  // namespace psat
