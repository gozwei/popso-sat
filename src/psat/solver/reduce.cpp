// Clause database maintenance: learned clause reduction (three tiers by glue, CaDiCaL's "used"
// aging), root-level simplification (satisfied clauses, falsified literals) and the compacting
// garbage collector of the clause arena.

#include <algorithm>
#include <cmath>
#include <cstring>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

void Solver::delete_clause_proof(const Clause& c) {
  if (proof_) proof_->del(c.lits(), c.size);
}

void Solver::mark_reasons(bool on) {
  for (const Lit l : trail_) {
    const VarData& d = vdata_[var_of(l)];
    if (!d.level || d.reason == kNoReason || (d.reason & kBinaryTag)) continue;
    clause(d.reason).reason = on;
  }
}

void Solver::update_tier_limits() {
  uint64_t total = 0;
  for (uint64_t c : used_glue_) total += c;
  if (total < 1000) return;  // too few samples: keep the current limits
  const uint64_t q1 = total * static_cast<uint64_t>(opts_.tier1quantile) / 100;
  const uint64_t q2 = total * static_cast<uint64_t>(opts_.tier2quantile) / 100;
  uint64_t cum = 0;
  uint32_t t1 = 0, t2 = 0;
  for (uint32_t g = 0; g < kGlueBuckets; ++g) {
    cum += used_glue_[g];
    if (!t1 && cum >= q1) t1 = g;
    if (!t2 && cum >= q2) t2 = g;
  }
  if (!t1) t1 = kGlueBuckets - 1;
  if (!t2) t2 = kGlueBuckets - 1;
  tier1_ = std::max<uint32_t>(t1, 1);
  tier2_ = std::max(tier1_ + 1, t2);
  for (uint64_t& c : used_glue_) c /= 2;  // older samples fade
}

void Solver::reduce() {
  ++stats_.reductions;
  if (opts_.dynamictiers) update_tier_limits();
  mark_reasons(true);
  // Candidates: unprotected learned clauses not used since the last reduction (tier2 clauses
  // survive two rounds unused, tier1 clauses are kept).
  std::vector<std::pair<uint64_t, uint32_t>> order;
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (!c.redundant || c.garbage || c.reason) continue;
    const bool used = c.used != 0;
    if (used) --c.used;
    if (used || c.keep || c.glue <= tier1_) continue;
    // Least useful first: high glue, then long.
    order.emplace_back((uint64_t{c.glue} << 32) | c.size, ref);
  }
  std::sort(order.begin(), order.end(), [](const auto& a, const auto& b) { return a.first > b.first; });
  const size_t n = order.size();
  const size_t target = n * static_cast<size_t>(opts_.reducefraction) / 100;
  for (size_t i = 0; i < target; ++i) {
    Clause& c = clause(order[i].second);
    delete_clause_proof(c);
    c.garbage = 1;
    note_garbage(c);
    garbage_words_ += kHeaderWords + c.size;
    --redundant_;
    ++stats_.reduced_clauses;
  }
  mark_reasons(false);
  maybe_collect_garbage();
  const double delta = static_cast<double>(opts_.reduceint) * std::sqrt(static_cast<double>(stats_.reductions + 1));
  reduce_limit_ = stats_.conflicts + static_cast<uint64_t>(delta);
}

// Removes binary clauses satisfied at the root (level 0 only, after complete propagation: then
// every binary clause with an assigned literal is satisfied).
void Solver::flush_root_binaries() {
  for (Lit l = 0; l < 2 * num_vars_; ++l) {
    std::vector<Watch>& ws = watches_[l];
    const bool l_assigned = vals_[l] != 0;
    size_t j = 0;
    for (size_t i = 0; i < ws.size(); ++i) {
      const Watch w = ws[i];
      if (w.binary() && (l_assigned || vals_[w.blit] != 0)) {
        if (l < w.blit) {
          if (proof_) {
            const Lit bin[2] = {l, w.blit};
            proof_->del(bin, 2);
          }
          if (w.redundant_binary()) {
            --binaries_redundant_;
          } else {
            --binaries_irredundant_;
          }
        }
        continue;
      }
      ws[j++] = w;
    }
    ws.resize(j);
  }
}

void Solver::simplify_root() {
  // Precondition: level 0, everything propagated, no conflict.
  last_simplify_fixed_ = fixed_;
  ++stats_.simplified_root;
  flush_root_binaries();
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (c.garbage) continue;
    Lit* lits = c.lits();
    bool satisfied = false, falsified = false;
    for (uint32_t k = 0; k < c.size; ++k) {
      const int8_t v = vals_[lits[k]];
      if (v > 0) {
        satisfied = true;
        break;
      }
      if (v < 0) falsified = true;
    }
    if (!satisfied && !falsified) continue;
    if (satisfied) {
      delete_clause_proof(c);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      continue;
    }
    // Remove the root-falsified literals. The watched literals lits[0], lits[1] are not false
    // (the clause would otherwise have propagated or be satisfied), so they stay in place.
    clause_buf_.clear();
    for (uint32_t k = 0; k < c.size; ++k) {
      if (vals_[lits[k]] == 0) clause_buf_.push_back(lits[k]);
    }
    if (proof_) {
      proof_->add(clause_buf_.data(), clause_buf_.size());
      proof_->del(lits, c.size);
    }
    if (clause_buf_.size() == 2) {
      add_binary(clause_buf_[0], clause_buf_[1], c.redundant);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      continue;
    }
    garbage_words_ += c.size - static_cast<uint32_t>(clause_buf_.size());
    shrunk_words_ += c.size - static_cast<uint32_t>(clause_buf_.size());
    std::copy(clause_buf_.begin(), clause_buf_.end(), lits);
    c.size = static_cast<uint32_t>(clause_buf_.size());
    c.pos = 2;
    if (c.glue > c.size - 1) c.glue = c.size - 1;
  }
  maybe_collect_garbage();
  // Amortize: the next simplification waits for search effort proportional to its cost.
  simplify_ticks_limit_ = stats_.ticks + arena_.size() / 4 + 2 * size_t{num_vars_};
}

// Compacts the arena from the first garbage clause on (as Kissat's sparse collection): clauses
// before it keep their place, and their watches are not even looked up. Learned clauses live at
// the end of the arena, so collections after a reduction move only the learned tail instead of
// the whole (mostly irredundant) formula. Words left dead by clauses shortened in place are
// reclaimed by a full compaction once they exceed an eighth of the arena.
void Solver::collect_garbage() {
  if (garbage_words_ == 0) return;
  ++stats_.collections;
  const bool full = shrunk_words_ * 8 > arena_.size();
  // clauses_ is in arena order: find the first garbage clause.
  size_t first = 0;
  if (!full) {
    if (first_garbage_ == UINT32_MAX) {  // only shrunk clauses: their few dead words stay for now
      garbage_words_ = 0;
      return;
    }
    first = static_cast<size_t>(std::lower_bound(clauses_.begin(), clauses_.end(), first_garbage_) - clauses_.begin());
  }
  const uint32_t start = full ? 0 : clauses_[first];
  if (full) ++stats_.collections_full;
  stats_.collected_words += arena_.size() - start;
  // Pass 1: forwarding addresses (in the header's pos field) for the surviving clauses.
  uint32_t dst = start;
  for (size_t i = first; i < clauses_.size(); ++i) {
    Clause& c = clause(clauses_[i]);
    if (c.garbage) continue;
    c.pos = dst;
    dst += kHeaderWords + c.size;
  }
  // Pass 2: watches and reasons (only references at or after the start can change).
  for (std::vector<Watch>& ws : watches_) {
    size_t j = 0;
    for (size_t i = 0; i < ws.size(); ++i) {
      Watch w = ws[i];
      if (!w.binary() && w.ref >= start) {
        const Clause& c = clause(w.ref);
        if (c.garbage) continue;
        w.ref = c.pos;
      }
      ws[j++] = w;
    }
    ws.resize(j);
  }
  for (const Lit l : trail_) {
    VarData& d = vdata_[var_of(l)];
    if (d.reason == kNoReason || (d.reason & kBinaryTag) || d.reason < start) continue;
    d.reason = clause(d.reason).pos;
  }
  // Pass 3: move (destinations never overlap later clauses).
  size_t live = first;
  for (size_t i = first; i < clauses_.size(); ++i) {
    const uint32_t ref = clauses_[i];
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    const uint32_t to = c.pos;
    const uint32_t words = kHeaderWords + c.size;
    if (to != ref) std::memmove(arena_.data() + to, arena_.data() + ref, size_t{words} * sizeof(uint32_t));
    clause(to).pos = 2;
    clauses_[live++] = to;
  }
  clauses_.resize(live);
  watched_clauses_ = live;
  arena_.resize(dst);
  if (arena_.capacity() > 2 * arena_.size() + 1024) arena_.shrink_to_fit();
  garbage_words_ = 0;
  first_garbage_ = UINT32_MAX;
  recent_learned_.clear();
  if (full) shrunk_words_ = 0;
}

// Propagation drops watches of garbage clauses when it meets them, so a collection can wait until
// it pays: when at least half of what it would move is garbage (typically the learned tail after
// a reduction), or when garbage is an eighth of the arena (memory).
void Solver::maybe_collect_garbage() {
  if (garbage_words_ == 0) return;
  const uint64_t tail = first_garbage_ == UINT32_MAX ? 0 : arena_.size() - first_garbage_;
  if (2 * garbage_words_ >= tail || 8 * garbage_words_ >= arena_.size() || shrunk_words_ * 8 > arena_.size()) {
    collect_garbage();
  }
}

}  // namespace psat
