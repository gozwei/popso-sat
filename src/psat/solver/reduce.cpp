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

void Solver::reduce() {
  ++stats_.reductions;
  mark_reasons(true);
  // Candidates: unprotected learned clauses not used since the last reduction (tier2 clauses
  // survive two rounds unused, tier1 clauses are kept).
  std::vector<std::pair<uint64_t, uint32_t>> order;
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (!c.redundant || c.garbage || c.reason) continue;
    const bool used = c.used != 0;
    if (used) --c.used;
    if (used || c.keep) continue;
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
    garbage_words_ += kHeaderWords + c.size;
    --redundant_;
    ++stats_.reduced_clauses;
  }
  mark_reasons(false);
  collect_garbage();
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
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      continue;
    }
    garbage_words_ += c.size - static_cast<uint32_t>(clause_buf_.size());
    std::copy(clause_buf_.begin(), clause_buf_.end(), lits);
    c.size = static_cast<uint32_t>(clause_buf_.size());
    c.pos = 2;
    if (c.glue > c.size - 1) c.glue = c.size - 1;
  }
  collect_garbage();
  // Amortize: the next simplification waits for search effort proportional to its cost.
  simplify_ticks_limit_ = stats_.ticks + arena_.size() / 4 + 2 * size_t{num_vars_};
}

void Solver::collect_garbage() {
  if (garbage_words_ == 0) return;
  ++stats_.collections;
  // Pass 1: forwarding addresses (in the header's pos field) for the surviving clauses.
  uint32_t dst = 0;
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (c.garbage) continue;
    c.pos = dst;
    dst += kHeaderWords + c.size;
  }
  // Pass 2: watches and reasons.
  for (std::vector<Watch>& ws : watches_) {
    size_t j = 0;
    for (size_t i = 0; i < ws.size(); ++i) {
      Watch w = ws[i];
      if (!w.binary()) {
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
    if (d.reason == kNoReason || (d.reason & kBinaryTag)) continue;
    d.reason = clause(d.reason).pos;
  }
  // Pass 3: move (destinations never overlap later clauses).
  size_t live = 0;
  for (const uint32_t ref : clauses_) {
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
}

}  // namespace psat
