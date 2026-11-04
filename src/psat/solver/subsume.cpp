// Forward subsumption and self-subsuming strengthening of irredundant clauses, run at the start
// of an elimination round (long watches detached, occurrence lists built).
//
// Clauses are processed by increasing size. Each one is checked against the irredundant binary
// clauses of its literals (from the watch lists) and against the smaller long clauses processed
// before it, which are kept in one-watch lists (each connected to its literal with the shortest
// list, as in CaDiCaL's subsume). A clause D subsumes C if D's literals are all in C; it
// strengthens C if all but one are, and that one occurs negated in C (C minus that literal is
// the resolvent of C and D).

#include <algorithm>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

void Solver::subsume_round(uint64_t& budget) {
  const uint64_t limit = budget + (eliminate_rounds_ <= 1 ? std::max<uint64_t>(1'000'000, arena_.size() / 4)
                                                         : std::max<uint64_t>(100'000, arena_.size() / 32)) *
                                      static_cast<uint64_t>(opts_.subsumeeffort) / 100;
  std::vector<std::pair<uint32_t, uint32_t>> order;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant) order.emplace_back(c.size, ref);
  }
  std::sort(order.begin(), order.end());
  std::vector<std::vector<uint32_t>> conn(2 * size_t{num_vars_});

  for (const auto& item : order) {
    if (budget > limit) break;
    const uint32_t ref = item.second;
    Clause& c = clause(ref);
    if (c.garbage) continue;
    Lit* lits = c.lits();
    for (uint32_t k = 0; k < c.size; ++k) marks_[lits[k]] = 1;
    bool subsumed = false;
    Lit remove = kNoLit;
    // Check one candidate D against the marked clause C.
    auto check = [&](uint32_t dref) {
      const Clause& d = clause(dref);
      if (d.garbage || dref == ref) return;
      budget += d.size / 4 + 1;
      Lit neg = kNoLit;
      const Lit* dl = d.lits();
      for (uint32_t k = 0; k < d.size; ++k) {
        const Lit l = dl[k];
        if (marks_[l]) continue;
        if (neg == kNoLit && marks_[negate(l)]) {
          neg = l;
          continue;
        }
        return;
      }
      if (neg == kNoLit) {
        subsumed = true;
      } else if (remove == kNoLit) {
        remove = negate(neg);
      }
    };
    for (uint32_t k = 0; k < c.size && !subsumed && budget <= limit; ++k) {
      const Lit l = lits[k];
      for (const Watch& w : watches_[l]) {
        if (w.binary() && !w.redundant_binary() && marks_[w.blit]) {
          subsumed = true;
          break;
        }
      }
      if (subsumed) break;
      if (remove == kNoLit) {
        for (const Watch& w : watches_[negate(l)]) {
          if (w.binary() && !w.redundant_binary() && marks_[w.blit]) {
            remove = l;
            break;
          }
        }
      }
      budget += (watches_[l].size() + watches_[negate(l)].size()) / 8 + 1;
      for (const uint32_t d : conn[l]) {
        check(d);
        if (subsumed) break;
      }
      if (subsumed) break;
      for (const uint32_t d : conn[negate(l)]) check(d);
    }
    for (uint32_t k = 0; k < c.size; ++k) marks_[lits[k]] = 0;

    if (subsumed) {
      ++stats_.subsumed;
      delete_irredundant(ref);
      continue;
    }
    if (remove != kNoLit) {
      ++stats_.strengthened;
      clause_buf_.clear();
      for (uint32_t k = 0; k < c.size; ++k) {
        if (lits[k] != remove) clause_buf_.push_back(lits[k]);
      }
      if (proof_) {
        proof_->add(clause_buf_.data(), clause_buf_.size());
        proof_->del(lits, c.size);
      }
      touch_clause(lits, c.size);
      std::vector<uint32_t>& os = occs_[remove];
      os.erase(std::remove(os.begin(), os.end(), ref), os.end());
      if (clause_buf_.size() == 2) {
        add_binary(clause_buf_[0], clause_buf_[1], false);
        c.garbage = 1;
        note_garbage(c);
        garbage_words_ += kHeaderWords + c.size;
        --irredundant_;
        continue;
      }
      std::copy(clause_buf_.begin(), clause_buf_.end(), lits);
      garbage_words_ += 1;
      shrunk_words_ += 1;
      c.size -= 1;
    }
    // Connect C to its literal with the shortest one-watch list.
    Lit best = lits[0];
    for (uint32_t k = 1; k < c.size; ++k) {
      if (conn[lits[k]].size() < conn[best].size()) best = lits[k];
    }
    conn[best].push_back(ref);
  }
}

}  // namespace psat
