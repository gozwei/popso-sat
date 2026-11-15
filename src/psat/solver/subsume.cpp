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
#include <cstdio>
#include <unordered_map>
#include <vector>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

// Removes `remove` from the irredundant long clause `ref` (occurrence lists built, long watches
// detached). The shorter clause is RUP; it is added to the proof before the old one is deleted.
// Returns true when the result is binary: the clause becomes garbage and a binary clause is added.
bool Solver::strengthen_irredundant(uint32_t ref, Lit remove) {
  Clause& c = clause(ref);
  Lit* lits = c.lits();
  clause_buf_.clear();
  for (uint32_t k = 0; k < c.size; ++k) {
    if (lits[k] != remove) clause_buf_.push_back(lits[k]);
  }
  if (proof_) {
    proof_->add(clause_buf_.data(), clause_buf_.size());
    proof_->del(lits, c.size);
  }
  touch_clause(lits, c.size);
  occs_.erase_value(remove, ref);
  if (clause_buf_.size() == 2) {
    add_binary(clause_buf_[0], clause_buf_[1], false);
    c.garbage = 1;
    note_garbage(c);
    garbage_words_ += kHeaderWords + c.size;
    --irredundant_;
    return true;
  }
  std::copy(clause_buf_.begin(), clause_buf_.end(), lits);
  garbage_words_ += 1;
  shrunk_words_ += 1;
  c.size -= 1;
  return false;
}

// --mergepairs: two irredundant clauses over the same variables whose signs differ in exactly one
// place, (A x) and (A -x), are replaced by their resolvent A, which subsumes both: one is
// strengthened in place, the other deleted. The formula stays equivalent (no extension stack).
// Forward subsumption finds such pairs only one level per round, and at a quadratic cost where
// many clauses share their variables: a function encoded by its forbidden assignments (random
// circuits: each 7-input / 7-output gate as 16,256 clauses of 14 literals, which merge down to
// 7 clauses per input row; Kissat gets there by strengthening over its whole run).
//
// Clauses are grouped by size, largest first, and within a size by their variable set (a sum of
// hashed variables, checked exactly); in a group a clause is a sign mask over its sorted variables
// and a partner is the mask with one bit flipped. Pairs are taken one variable position at a time
// (the resolvents of a group then mostly share their variables again) and the resolvents join the
// next size down. Linear in the literals (plus the sorts); clauses of more than 64 literals are
// left alone.
void Solver::merge_pairs() {
  constexpr uint32_t kMaxSize = 64;
  std::vector<std::vector<uint32_t>> bucket(kMaxSize + 1);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant && c.size >= 3 && c.size <= kMaxSize) bucket[c.size].push_back(ref);
  }
  const auto mix = [](uint64_t x) {
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
  };
  const auto by_var = [](Lit a, Lit b) { return var_of(a) < var_of(b); };
  std::vector<std::pair<uint64_t, uint32_t>> keyed;
  std::vector<uint32_t> members;
  std::vector<Lit> sorted;  // the members' literals by variable, s per member
  std::vector<uint64_t> masks;
  std::vector<uint8_t> matched;
  std::unordered_map<uint64_t, uint32_t> index;
  const uint64_t merged_before = stats_.merged;
  uint64_t work = 0;
  for (uint32_t s = kMaxSize; s >= 3 && !inconsistent_; --s) {
    if (stop_requested()) break;
    keyed.clear();
    for (const uint32_t ref : bucket[s]) {
      const Clause& c = clause(ref);
      if (c.garbage || c.size != s) continue;
      uint64_t h = 0;
      for (uint32_t k = 0; k < s; ++k) h += mix(uint64_t{var_of(c.lits()[k])} + 1);
      keyed.emplace_back(h, ref);
    }
    work += uint64_t{s} * keyed.size();
    std::vector<uint32_t>().swap(bucket[s]);
    if (keyed.size() < 2) continue;
    std::sort(keyed.begin(), keyed.end());
    for (size_t a = 0; a < keyed.size();) {
      size_t b = a + 1;
      while (b < keyed.size() && keyed[b].first == keyed[a].first) ++b;
      if (b - a < 2) {
        a = b;
        continue;
      }
      members.clear();
      sorted.clear();
      masks.clear();
      for (size_t m = a; m < b; ++m) {
        const Clause& c = clause(keyed[m].second);
        const size_t at = sorted.size();
        sorted.insert(sorted.end(), c.lits(), c.lits() + s);
        std::sort(sorted.begin() + static_cast<std::ptrdiff_t>(at), sorted.end(), by_var);
        bool same = true;
        uint64_t mask = 0;
        for (uint32_t k = 0; k < s; ++k) {
          const Lit l = sorted[at + k];
          if (at && var_of(l) != var_of(sorted[k])) same = false;
          if (is_negative(l)) mask |= uint64_t{1} << k;
        }
        if (!same) {  // a hash collision: a different variable set
          sorted.resize(at);
          continue;
        }
        members.push_back(keyed[m].second);
        masks.push_back(mask);
      }
      a = b;
      const uint32_t n = static_cast<uint32_t>(members.size());
      if (n < 2) continue;
      work += uint64_t{n} * s * 2;
      index.clear();
      for (uint32_t m = 0; m < n; ++m) index.emplace(masks[m], m);  // duplicates: the first
      matched.assign(n, 0);
      for (uint32_t k = 0; k < s; ++k) {
        for (uint32_t m = 0; m < n; ++m) {
          if (matched[m]) continue;
          const auto it = index.find(masks[m] ^ (uint64_t{1} << k));
          if (it == index.end()) continue;
          const uint32_t p = it->second;
          if (p == m || matched[p]) continue;
          matched[m] = matched[p] = 1;
          ++stats_.merged;
          ++stats_.strengthened;
          ++stats_.subsumed;
          // The resolvent (members[m] without its literal on the k-th variable) is added before
          // either parent is deleted.
          const bool binary = strengthen_irredundant(members[m], sorted[size_t{m} * s + k]);
          delete_irredundant(members[p]);
          if (!binary && s - 1 >= 3) bucket[s - 1].push_back(members[m]);
        }
      }
    }
  }
  merge_productive_ = stats_.merged != merged_before;
  if (opts_.verbose >= 3) {
    std::printf("c   merge pairs: %llu merged, work %llu\n",
                static_cast<unsigned long long>(stats_.merged - merged_before), static_cast<unsigned long long>(work));
  }
}

void Solver::subsume_round(uint64_t& budget) {
  const PassTimer pass_timer(*this, kPassSubsume);
  uint64_t effort = (eliminate_rounds_ <= 1 ? std::max<uint64_t>(1'000'000, arena_.size() / 4)
                                            : std::max<uint64_t>(100'000, arena_.size() / 32)) *
                    static_cast<uint64_t>(opts_.subsumeeffort) / 100;
  // --subsumerel: later rounds also get a share of the search since the last round. The fixed
  // effort (a 32nd of the arena) covers the smallest clauses of the formula, the same ones every
  // round (schooltt-5-3-8: about 11k of 21-30k long irredundant clauses), and not the larger
  // resolvents of the previous rounds.
  if (eliminate_rounds_ > 1 && opts_.subsumerel) {
    const uint64_t search_ticks = stats_.ticks - eliminate_last_ticks_;
    effort = std::max<uint64_t>(
        effort, static_cast<uint64_t>(static_cast<double>(search_ticks) * static_cast<double>(opts_.subsumerel) / 1000.0));
  }
  const uint64_t limit = budget + effort;
  // Later rounds only while the last call merged (elimination rarely makes such pairs; on ncc,
  // 12M clauses and none to merge, a call costs 0.6 s).
  if (opts_.mergepairs && (eliminate_rounds_ <= 1 || merge_productive_)) merge_pairs();
  std::vector<std::pair<uint32_t, uint32_t>> order;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant) order.emplace_back(c.size, ref);
  }
  std::sort(order.begin(), order.end());
  std::vector<std::vector<uint32_t>> conn(2 * size_t{num_vars_});

  size_t checked = 0;
  const uint64_t subsumed_before = stats_.subsumed, strengthened_before = stats_.strengthened;
  for (const auto& item : order) {
    if (budget > limit || stop_requested()) break;
    ++checked;
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
      if (strengthen_irredundant(ref, remove)) continue;
    }
    // Connect C to its literal with the shortest one-watch list.
    Lit best = lits[0];
    for (uint32_t k = 1; k < c.size; ++k) {
      if (conn[lits[k]].size() < conn[best].size()) best = lits[k];
    }
    conn[best].push_back(ref);
  }
  if (opts_.verbose >= 3) {
    std::printf("c   subsume: checked %zu of %zu clauses, subsumed %llu, strengthened %llu, effort %llu\n", checked,
                order.size(), static_cast<unsigned long long>(stats_.subsumed - subsumed_before),
                static_cast<unsigned long long>(stats_.strengthened - strengthened_before),
                static_cast<unsigned long long>(effort));
  }
}

}  // namespace psat
