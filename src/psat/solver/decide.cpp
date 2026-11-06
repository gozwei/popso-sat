// Decision heuristics: VMTF queue in focused mode, EVSIDS scores on a binary heap in stable mode
// (the Kissat combination), with saved / target phases.

#include <algorithm>

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
  for (Var v = 0; v < num_vars_; ++v) {
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
  std::sort(analyzed_.begin(), analyzed_.end(), [this](Var a, Var b) { return bumped_[a] < bumped_[b]; });
  for (Var v : analyzed_) queue_bump(v);
}

// --- decisions -------------------------------------------------------------------------------

bool Solver::decide() {
  Var v = stable_ ? next_stable() : next_focused();
  if (gauss_on_ && gauss_mat_[v] != UINT32_MAX && opts_.gaussdecide) v = gauss_decision(v);
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
