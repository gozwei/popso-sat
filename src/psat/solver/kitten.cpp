#include "psat/solver/kitten.hpp"

#include <algorithm>

namespace psat {

void Kitten::clear() {
  const uint32_t n = nvars_;
  for (uint32_t l = 0; l < 2 * n; ++l) watches_[l].clear();
  arena_.clear();
  learned_refs_.clear();
  ante_.clear();
  ante_begin_.assign(1, 0);
  core_conflict_ = kNone;
  track_cores_ = false;
  needed_.clear();
  final_reasons_.clear();
  trail_.clear();
  control_.clear();
  heap_.clear();
  queue_ = false;
  queue_first_ = queue_last_ = queue_search_ = kNone;
  queue_stamps_ = 0;
  assumptions_.clear();
  final_.clear();
  propagated_ = 0;
  conflict_ = kNone;
  status_ = kUnknown;
  inconsistent_ = false;
  inc_ = 1.0;
  nvars_ = 0;
}

size_t Kitten::bytes() const {
  size_t b = (arena_.capacity() + learned_refs_.capacity() + ante_.capacity() + ante_begin_.capacity() +
              stamp_.capacity() + final_reasons_.capacity()) * 4 + needed_.capacity();
  b += watches_.capacity() * sizeof(std::vector<uint32_t>);
  for (const auto& w : watches_) b += w.capacity() * 4;
  b += vals_.capacity() + phase_.capacity() + seen_.capacity() + score_.capacity() * 8;
  b += (levels_.capacity() + reasons_.capacity() + heap_.capacity() + heap_pos_.capacity() + trail_.capacity() +
        control_.capacity() + queue_prev_.capacity() + queue_next_.capacity()) * 4 + queue_stamp_.capacity() * 8;
  return b;
}

void Kitten::resize(uint32_t n) {
  if (n <= nvars_) return;
  const uint32_t old = nvars_;
  nvars_ = n;
  if (watches_.size() < 2 * size_t{n}) watches_.resize(2 * size_t{n});
  vals_.resize(2 * size_t{n});
  phase_.resize(n);
  levels_.resize(n);
  reasons_.resize(n);
  seen_.resize(n);
  score_.resize(n);
  heap_pos_.resize(n);
  if (queue_) {
    queue_prev_.resize(n);
    queue_next_.resize(n);
    queue_stamp_.resize(n);
  }
  for (uint32_t v = old; v < n; ++v) {
    vals_[2 * v] = vals_[2 * v + 1] = 0;
    phase_[v] = -1;
    levels_[v] = 0;
    reasons_[v] = kNone;
    seen_[v] = 0;
    score_[v] = 0;
    heap_pos_[v] = kNone;
    if (!queue_) heap_push(v);
  }
  if (queue_) {
    // New variables go before the old ones, the lowest index last (decided first, as the heap
    // does with equal scores): the queue is rebuilt with fresh stamps.
    std::vector<uint32_t> order;
    order.reserve(n);
    for (uint32_t v = n; v-- > old;) order.push_back(v);
    for (uint32_t v = queue_first_; v != kNone; v = queue_next_[v]) order.push_back(v);
    queue_first_ = queue_last_ = queue_search_ = kNone;
    queue_stamps_ = 0;
    for (const uint32_t v : order) queue_enqueue(v);
    for (uint32_t v = queue_last_; v != kNone; v = queue_prev_[v]) {
      if (!vals_[2 * v]) {
        queue_search_ = v;
        break;
      }
    }
  }
}

void Kitten::queue_enqueue(uint32_t v) {
  queue_prev_[v] = queue_last_;
  queue_next_[v] = kNone;
  if (queue_last_ != kNone) {
    queue_next_[queue_last_] = v;
  } else {
    queue_first_ = v;
  }
  queue_last_ = v;
  queue_stamp_[v] = ++queue_stamps_;
}

void Kitten::queue_dequeue(uint32_t v) {
  const uint32_t p = queue_prev_[v], q = queue_next_[v];
  if (p != kNone) {
    queue_next_[p] = q;
  } else {
    queue_first_ = q;
  }
  if (q != kNone) {
    queue_prev_[q] = p;
  } else {
    queue_last_ = p;
  }
}

uint32_t Kitten::new_clause(const KLit* lits, uint32_t size, uint32_t aux, bool watch) {
  const uint32_t ref = static_cast<uint32_t>(arena_.size());
  arena_.push_back(size);
  arena_.push_back(aux);
  arena_.insert(arena_.end(), lits, lits + size);
  if (watch && size >= 2) {
    watches_[lits[0]].push_back(ref);
    watches_[lits[1]].push_back(ref);
  }
  return ref;
}

void Kitten::add_clause(const KLit* lits, uint32_t size, uint32_t id) {
  status_ = kUnknown;
  backtrack(0);
  if (inconsistent_) return;
  learned_.clear();
  bool skip = false;  // satisfied at the root or a tautology
  for (uint32_t i = 0; i < size && !skip; ++i) {
    const KLit l = lits[i];
    if (vals_[l] > 0 && levels_[var(l)] == 0) {
      skip = true;
      continue;
    }
    if (seen_[var(l)]) {
      skip = std::find(learned_.begin(), learned_.end(), l) == learned_.end();  // else a duplicate
      continue;
    }
    seen_[var(l)] = 1;
    learned_.push_back(l);
  }
  for (const KLit x : learned_) seen_[var(x)] = 0;  // the marks are cleared on every path
  if (skip) return;
  // Literals false at the root are kept (cores follow their reasons) but moved to the end.
  const auto mid = std::stable_partition(learned_.begin(), learned_.end(), [&](KLit l) { return vals_[l] == 0; });
  const auto open = static_cast<uint32_t>(mid - learned_.begin());
  const uint32_t ref = new_clause(learned_.data(), static_cast<uint32_t>(learned_.size()), id, open >= 2);
  if (open == 0) {
    inconsistent_ = true;
    core_conflict_ = ref;
  } else if (open == 1) {
    assign(learned_[0], ref);  // at the root, with the clause as its reason
  }
}

void Kitten::assign(KLit lit, uint32_t reason) {
  vals_[lit] = 1;
  vals_[neg(lit)] = -1;
  const uint32_t v = var(lit);
  levels_[v] = level();
  reasons_[v] = reason;
  trail_.push_back(lit);
}

bool Kitten::propagate() {
  // The array bases, the list being visited and the tick counter live in locals: the int8_t
  // stores of an assignment may alias any member for the compiler, which otherwise reloads them
  // for every watch. Nothing here reallocates the arena or the values; a replacement watch goes
  // to another literal's list (a non-false literal, never the false one being visited).
  int8_t* const vals = vals_.data();
  uint32_t* const arena = arena_.data();
  uint64_t ticks = ticks_;
  bool ok = true;
  while (ok && propagated_ < trail_.size()) {
    const KLit nl = neg(trail_[propagated_++]);  // false now
    std::vector<uint32_t>& wl = watches_[nl];
    uint32_t* const ws = wl.data();
    const size_t n = wl.size();
    size_t i = 0, j = 0;
    while (i < n) {
      const uint32_t ref = ws[i++];
      ++ticks;
      const uint32_t size = arena[ref];
      KLit* const c = arena + ref + 2;
      // c[1] becomes the false watch: nl is one of the two watches, so the other one is
      // c[0] ^ c[1] ^ nl (stored without a branch on which one it was).
      const KLit other = c[0] ^ c[1] ^ nl;
      c[0] = other;
      c[1] = nl;
      const int8_t ov = vals[other];
      if (ov > 0) {
        ws[j++] = ref;
        continue;
      }
      uint32_t k = 2;
      while (k < size && vals[c[k]] < 0) ++k;
      if (k < size) {
        const KLit r = c[k];
        c[k] = c[1];
        c[1] = r;
        watches_[r].push_back(ref);
        continue;
      }
      ws[j++] = ref;
      if (ov < 0) {
        conflict_ = ref;
        while (i < n) ws[j++] = ws[i++];
        ok = false;
        break;
      }
      assign(other, ref);
    }
    wl.resize(j);
  }
  ticks_ = ticks;
  return ok;
}

void Kitten::backtrack(uint32_t lvl) {
  if (level() <= lvl) return;
  const uint32_t start = control_[lvl];
  for (size_t t = trail_.size(); t-- > start;) {
    const KLit l = trail_[t];
    const uint32_t v = var(l);
    phase_[v] = vals_[2 * v] > 0 ? 1 : -1;  // (the value: flip() can change it after a model)
    vals_[l] = vals_[neg(l)] = 0;
    if (queue_) {
      if (queue_search_ == kNone || queue_stamp_[v] > queue_stamp_[queue_search_]) queue_search_ = v;
    } else if (heap_pos_[v] == kNone) {
      heap_push(v);
    }
  }
  trail_.resize(start);
  control_.resize(lvl);
  if (propagated_ > start) propagated_ = start;
}

bool Kitten::flip(KLit lit) {
  if (status_ != kSat || vals_[lit] <= 0 || levels_[var(lit)] == 0) return false;
  // (local bases as in propagate(); a replacement is a true literal, never lit itself)
  const int8_t* const vals = vals_.data();
  uint32_t* const arena = arena_.data();
  std::vector<uint32_t>& wl = watches_[lit];
  uint32_t* const ws = wl.data();
  const size_t n = wl.size();
  uint64_t ticks = ticks_;
  size_t i = 0, j = 0;
  bool ok = true;
  while (i < n) {
    const uint32_t ref = ws[i++];
    ++ticks;
    const uint32_t size = arena[ref];
    KLit* const c = arena + ref + 2;
    c[0] ^= c[1] ^ lit;  // c[1] is lit (see propagate())
    c[1] = lit;
    if (vals[c[0]] > 0) {
      ws[j++] = ref;
      continue;
    }
    uint32_t k = 2;
    while (k < size && vals[c[k]] <= 0) ++k;
    if (k < size) {
      const KLit r = c[k];
      c[k] = c[1];
      c[1] = r;
      watches_[r].push_back(ref);
      continue;
    }
    ws[j++] = ref;  // only lit satisfies the clause: no flip (watches moved so far are true)
    ok = false;
    break;
  }
  while (i < n) ws[j++] = ws[i++];
  wl.resize(j);
  ticks_ = ticks;
  if (!ok) return false;
  vals_[lit] = -1;
  vals_[neg(lit)] = 1;
  return true;
}

void Kitten::randomize_phases(uint64_t& state) {
  backtrack(0);  // (solve() would otherwise save the current values as phases first)
  status_ = kUnknown;
  for (uint32_t v = 0; v < nvars_; ++v) {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    phase_[v] = (state >> 32) & 1 ? 1 : -1;
  }
}

void Kitten::bump(uint32_t v) {
  if (queue_) {  // to the end of the queue (the search pointer: if unassigned)
    if (queue_last_ == v) return;
    if (queue_search_ == v) queue_search_ = queue_prev_[v];
    queue_dequeue(v);
    queue_enqueue(v);
    if (!vals_[2 * v]) queue_search_ = v;
    return;
  }
  score_[v] += inc_;
  if (score_[v] > 1e100) {
    for (uint32_t u = 0; u < nvars_; ++u) score_[u] *= 1e-100;
    inc_ *= 1e-100;
  }
  if (heap_pos_[v] != kNone) heap_up(heap_pos_[v]);
}

void Kitten::analyze() {
  const uint32_t cl = level();
  learned_.clear();
  learned_.push_back(0);
  std::vector<uint32_t>& analyzed = final_;  // scratch (final_ is rebuilt before it is read)
  analyzed.clear();
  uint32_t open = 0;
  uint32_t ref = conflict_;
  KLit uip = kNone;
  size_t t = trail_.size();
  for (;;) {
    ante_.push_back(ref);
    const uint32_t size = arena_[ref];
    const KLit* c = &arena_[ref + 2];
    for (uint32_t k = 0; k < size; ++k) {
      const KLit q = c[k];
      if (q == uip) continue;
      const uint32_t v = var(q);
      if (seen_[v] || levels_[v] == 0) continue;
      seen_[v] = 1;
      analyzed.push_back(v);
      bump(v);
      if (levels_[v] == cl) {
        ++open;
      } else {
        learned_.push_back(q);
      }
    }
    do {
      uip = trail_[--t];
    } while (!seen_[var(uip)]);
    if (--open == 0) break;
    ref = reasons_[var(uip)];
  }
  learned_[0] = neg(uip);
  for (const uint32_t v : analyzed) seen_[v] = 0;
  inc_ /= 0.95;
  uint32_t jump = 0;
  for (size_t k = 1; k < learned_.size(); ++k) {
    const uint32_t lv = levels_[var(learned_[k])];
    if (lv > jump) {
      jump = lv;
      std::swap(learned_[1], learned_[k]);
    }
  }
  backtrack(jump);
  const uint32_t size = static_cast<uint32_t>(learned_.size());
  const uint32_t index = static_cast<uint32_t>(learned_refs_.size());
  const uint32_t lref = new_clause(learned_.data(), size, kLearnedBit | index, true);
  learned_refs_.push_back(lref);
  ante_begin_.push_back(static_cast<uint32_t>(ante_.size()));
  assign(learned_[0], lref);  // units too: at the root the clause is the reason (for cores)
}

void Kitten::compute_core(std::vector<uint32_t>& ids) {
  ids.clear();
  if (!inconsistent_ || core_conflict_ == kNone) return;
  std::vector<uint8_t> visited(arena_.size(), 0);
  std::vector<uint32_t> work{core_conflict_};
  while (!work.empty()) {
    const uint32_t ref = work.back();
    work.pop_back();
    if (visited[ref]) continue;
    visited[ref] = 1;
    const uint32_t size = arena_[ref], aux = arena_[ref + 1];
    if (aux & kLearnedBit) {
      const uint32_t i = aux & ~kLearnedBit;
      for (uint32_t a = ante_begin_[i]; a < ante_begin_[i + 1]; ++a) work.push_back(ante_[a]);
    } else {
      ids.push_back(aux);
    }
    // Literals false at the root were removed by the clauses that falsified them.
    for (uint32_t k = 0; k < size; ++k) {
      const KLit l = arena_[ref + 2 + k];
      const uint32_t v = var(l);
      if (vals_[l] < 0 && levels_[v] == 0 && reasons_[v] != kNone) work.push_back(reasons_[v]);
    }
  }
}

void Kitten::mark_core() {
  std::vector<uint32_t> work;
  if (inconsistent_) {
    if (core_conflict_ != kNone) work.push_back(core_conflict_);
  } else {
    work = final_reasons_;
  }
  mark_from(work);
}

void Kitten::mark_learned(size_t i) {
  std::vector<uint32_t> work{learned_refs_[i]};
  mark_from(work);
}

// Marks the learned clauses among the clauses in work and their antecedents, following the
// reasons of literals false at the root (those were skipped by the derivations). A clause marked
// before keeps its antecedents marked, but its root literals are followed again (they may have
// become false since).
void Kitten::mark_from(std::vector<uint32_t>& work) {
  if (needed_.size() < learned_refs_.size()) needed_.resize(learned_refs_.size(), 0);
  if (stamp_.size() < arena_.size()) stamp_.resize(arena_.size(), 0);
  if (++epoch_ == 0) {
    std::fill(stamp_.begin(), stamp_.end(), 0);
    epoch_ = 1;
  }
  while (!work.empty()) {
    const uint32_t ref = work.back();
    work.pop_back();
    if (stamp_[ref] == epoch_) continue;
    stamp_[ref] = epoch_;
    const uint32_t size = arena_[ref], aux = arena_[ref + 1];
    if (aux & kLearnedBit) {
      const uint32_t i = aux & ~kLearnedBit;
      if (!needed_[i]) {
        needed_[i] = 1;
        for (uint32_t a = ante_begin_[i]; a < ante_begin_[i + 1]; ++a) work.push_back(ante_[a]);
      }
    }
    for (uint32_t k = 0; k < size; ++k) {
      const KLit l = arena_[ref + 2 + k];
      const uint32_t v = var(l);
      if (vals_[l] < 0 && levels_[v] == 0 && reasons_[v] != kNone) work.push_back(reasons_[v]);
    }
  }
}

void Kitten::analyze_final(KLit failed) {
  // final_ = negations of the assumptions that imply -failed (plus -failed itself).
  final_.clear();
  final_.push_back(neg(failed));
  final_reasons_.clear();
  const uint32_t fv = var(failed);
  if (levels_[fv] == 0) {
    if (reasons_[fv] != kNone) final_reasons_.push_back(reasons_[fv]);
    return;
  }
  seen_[fv] = 1;
  std::vector<uint32_t> marked{fv};
  for (size_t t = trail_.size(); t-- > (control_.empty() ? trail_.size() : control_[0]);) {
    const KLit l = trail_[t];
    const uint32_t v = var(l);
    if (!seen_[v]) continue;
    const uint32_t r = reasons_[v];
    if (r == kNone) {  // an assumption (if it is -failed itself, the clause is a tautology)
      final_.push_back(neg(l));
      continue;
    }
    final_reasons_.push_back(r);
    const uint32_t size = arena_[r];
    const KLit* c = &arena_[r + 2];
    for (uint32_t k = 0; k < size; ++k) {
      const uint32_t u = var(c[k]);
      if (u == v || seen_[u] || levels_[u] == 0) continue;
      seen_[u] = 1;
      marked.push_back(u);
    }
  }
  for (const uint32_t v : marked) seen_[v] = 0;
}

bool Kitten::decide() {
  if (queue_) {
    uint32_t v = queue_search_;
    while (v != kNone && vals_[2 * v] != 0) v = queue_prev_[v];
    queue_search_ = v;
    if (v == kNone) return false;
    control_.push_back(static_cast<uint32_t>(trail_.size()));
    assign(2 * v + (phase_[v] > 0 ? 0u : 1u), kNone);
    return true;
  }
  while (!heap_.empty()) {
    const uint32_t v = heap_pop();
    if (vals_[2 * v] != 0) continue;
    control_.push_back(static_cast<uint32_t>(trail_.size()));
    assign(2 * v + (phase_[v] > 0 ? 0u : 1u), kNone);
    return true;
  }
  return false;
}

int Kitten::solve(uint64_t ticks_limit) {
  final_.clear();
  backtrack(0);
  const uint64_t limit = ticks_ + ticks_limit;
  int result = kUnknown;
  for (;;) {
    if (inconsistent_) {
      result = kUnsat;
      break;
    }
    if (!propagate()) {
      if (level() == 0) {
        inconsistent_ = true;  // the empty clause is RUP after the learned clauses
        core_conflict_ = conflict_;
        continue;
      }
      analyze();
      continue;
    }
    if (ticks_ > limit) break;
    if (level() < assumptions_.size()) {
      const KLit a = assumptions_[level()];
      if (vals_[a] > 0) {
        control_.push_back(static_cast<uint32_t>(trail_.size()));  // already true: empty level
        continue;
      }
      if (vals_[a] < 0) {
        analyze_final(a);
        result = kUnsat;
        break;
      }
      control_.push_back(static_cast<uint32_t>(trail_.size()));
      assign(a, kNone);
      continue;
    }
    if (!decide()) {
      result = kSat;
      break;
    }
  }
  if (result == kUnsat && inconsistent_) final_.clear();
  if (result == kUnsat && track_cores_) mark_core();
  assumptions_.clear();
  status_ = result;
  return result;
}

// Max-heap of variables by score.
void Kitten::heap_up(uint32_t i) {
  const uint32_t v = heap_[i];
  while (i > 0) {
    const uint32_t p = (i - 1) / 2;
    if (score_[heap_[p]] >= score_[v]) break;
    heap_[i] = heap_[p];
    heap_pos_[heap_[i]] = i;
    i = p;
  }
  heap_[i] = v;
  heap_pos_[v] = i;
}

void Kitten::heap_down(uint32_t i) {
  const uint32_t v = heap_[i];
  const uint32_t n = static_cast<uint32_t>(heap_.size());
  for (;;) {
    uint32_t c = 2 * i + 1;
    if (c >= n) break;
    if (c + 1 < n && score_[heap_[c + 1]] > score_[heap_[c]]) ++c;
    if (score_[heap_[c]] <= score_[v]) break;
    heap_[i] = heap_[c];
    heap_pos_[heap_[i]] = i;
    i = c;
  }
  heap_[i] = v;
  heap_pos_[v] = i;
}

void Kitten::heap_push(uint32_t v) {
  heap_pos_[v] = static_cast<uint32_t>(heap_.size());
  heap_.push_back(v);
  heap_up(heap_pos_[v]);
}

uint32_t Kitten::heap_pop() {
  const uint32_t v = heap_[0];
  heap_pos_[v] = kNone;
  const uint32_t last = heap_.back();
  heap_.pop_back();
  if (!heap_.empty()) {
    heap_[0] = last;
    heap_pos_[last] = 0;
    heap_down(0);
  }
  return v;
}

}  // namespace psat
