// Clause vivification (Piette, Hamadi & Sais 2008; Li et al. 2020; as in Kissat and CaDiCaL).
//
// For a clause C = (l1 ... lk), assign the negations of its literals one by one and propagate
// without C. If a literal li is already false it is dropped (implied by the earlier ones); if it
// is already true, C can be replaced by the decided literals plus li; if propagation conflicts, C
// can be replaced by the decided literals alone. Any such clause is RUP and a subset of C. When
// the clause that conflicted (or implied li) has only decided literals besides, it is itself a
// subset of C: with --vivifysubsume C is deleted instead of being replaced by a copy of it.
//
// Rounds run at the root after the root formula has been cleaned. Learned clauses of tier1 and
// tier2 (best glue first) get two thirds of the effort, irredundant clauses the rest. Phases
// are saved and restored around a round so that vivification decisions do not leak into search.

#include <algorithm>
#include <cmath>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

void Solver::vivify() {
  const PassTimer pass_timer(*this, kPassVivify);
  ++stats_.vivifications;
  ++vivify_rounds_;
  if (!backtrack_to_root()) return;
  if (fixed_ > last_simplify_fixed_) simplify_root();
  maybe_collect_garbage();
  const std::vector<int8_t> saved = saved_;
  const uint64_t search = stats_.ticks - vivify_last_ticks_;
  const uint64_t effort =
      std::max<uint64_t>(static_cast<uint64_t>(static_cast<double>(search) * opts_.vivifyeffort / 1000.0), 20000);
  if (opts_.unhide) {
    unhide(std::max<uint64_t>(static_cast<uint64_t>(static_cast<double>(search) * opts_.unhideeffort / 1000.0), 100000));
    if (inconsistent_) return;
  }
  const uint64_t start = stats_.vivify_ticks;
  if (opts_.probe) probe_failed_literals(start + effort / 5);
  if (inconsistent_) return;
  if (opts_.sweep) {
    const uint64_t equivalences = stats_.sweep_equivalences;
    sweep();
    if (inconsistent_) return;
    if (opts_.sweepsubst && stats_.sweep_equivalences != equivalences) {
      substitute_now();
      if (inconsistent_) return;
    }
  }
  vivify_clauses(true, stats_.vivify_ticks + (opts_.vivifyirred ? 2 * effort / 3 : effort));
  if (opts_.vivifyirred && !inconsistent_) vivify_clauses(false, start + effort);
  backtrack(0);
  saved_ = saved;
  maybe_collect_garbage();
  vivify_last_ticks_ = stats_.ticks;
  vivify_limit_ = stats_.conflicts + static_cast<uint64_t>(static_cast<double>(opts_.vivifyint) *
                                                           std::sqrt(static_cast<double>(vivify_rounds_ + 1)));
}

void Solver::vivify_clauses(bool redundant, uint64_t ticks_limit) {
  // Candidates packed as (glue 20 bits, size 12 bits, ref 32 bits) in one word, reserved up front:
  // on formulas with millions of clauses a growing vector of pairs cost hundreds of MB.
  std::vector<uint64_t>& cands = viv_cands_;
  cands.clear();
  cands.reserve(redundant ? redundant_ : irredundant_);
  size_t done = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant != redundant) continue;
    if (redundant && c.glue > tier2_ && !opts_.vivifytier3) continue;
    if (c.vivified) {
      ++done;
      continue;
    }
    const uint64_t key = (uint64_t{std::min<uint32_t>(c.glue, (1u << 20) - 1)} << 12) | std::min<uint32_t>(c.size, 4095);
    cands.push_back((key << 32) | ref);
  }
  // Every clause had its turn: start the next pass.
  if (cands.empty() && done) {
    for (const uint32_t ref : clauses_) {
      Clause& c = clause(ref);
      if (!c.garbage && c.redundant == redundant) c.vivified = 0;
    }
    return;
  }
  // Learned clauses: lowest glue (most useful) first; irredundant: shortest first. Only the
  // clauses this round can afford (estimated from the ticks per clause of earlier rounds, with a
  // margin) are selected and ordered: on large formulas sorting every irredundant clause each
  // round cost more than vivifying. The others keep their turn for later rounds. Taken in chunks
  // in that order; within a chunk the literals of each clause are sorted by their number of
  // occurrences among the selected candidates (--vivifysort: in all clauses) and the clauses
  // lexicographically, so that consecutive clauses share decision prefixes, which are kept
  // instead of being propagated again.
  constexpr size_t kChunk = 1000;
  {
    const uint64_t budget = ticks_limit > stats_.vivify_ticks ? ticks_limit - stats_.vivify_ticks : 0;
    const uint64_t afford = 2 * budget / std::max<uint64_t>(vivify_ticks_per_clause_, 1);
    const size_t take = std::min(cands.size(), std::max<size_t>(kChunk, static_cast<size_t>(afford)));
    if (take < cands.size()) {
      std::nth_element(cands.begin(), cands.begin() + static_cast<std::ptrdiff_t>(take), cands.end());
      cands.resize(take);
    }
  }
  std::sort(cands.begin(), cands.end());
  std::vector<uint32_t>& count = viv_count_;
  count.assign(2 * size_t{num_vars_}, 0);
  if (opts_.vivifysort == 2 || (opts_.vivifysort == 1 && !redundant)) {
    // Occurrences in all clauses (binary ones included): deciding the negation of a literal that
    // occurs often propagates the most, so conflicts come after fewer decisions. (Irredundant
    // clauses on schooltt-5-3-8: 7.2% of the checks shorten one instead of 2.0%.)
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage) continue;
      for (uint32_t k = 0; k < c.size; ++k) ++count[c.lits()[k]];
    }
    for (Lit l = 0; l < 2 * num_vars_; ++l) {
      for (const Watch& w : watches_[l]) count[l] += w.binary() ? 1u : 0u;
    }
    stats_.vivify_ticks += arena_.size() / 8 + num_vars_;
  } else {
    for (const uint64_t cand : cands) {
      const Clause& c = clause(static_cast<uint32_t>(cand));
      for (uint32_t k = 0; k < c.size; ++k) ++count[c.lits()[k]];
    }
  }
  auto before = [&](Lit a, Lit b) { return count[a] != count[b] ? count[a] > count[b] : a < b; };
  std::vector<Lit> flat;
  std::vector<std::pair<uint32_t, uint32_t>> spans;  // offset into flat, size
  std::vector<uint32_t> order;
  backtrack(0);
  const uint64_t ticks_before = stats_.vivify_ticks;
  uint64_t processed = 0;
  for (size_t first = 0; first < cands.size(); first += kChunk) {
    if (inconsistent_ || stats_.vivify_ticks > ticks_limit || stop_requested()) break;
    const size_t last = std::min(cands.size(), first + kChunk);
    flat.clear();
    spans.clear();
    for (size_t i = first; i < last; ++i) {
      const Clause& c = clause(static_cast<uint32_t>(cands[i]));
      const uint32_t off = static_cast<uint32_t>(flat.size());
      flat.insert(flat.end(), c.lits(), c.lits() + c.size);
      std::sort(flat.begin() + off, flat.end(), before);
      spans.emplace_back(off, c.size);
    }
    order.resize(last - first);
    for (uint32_t i = 0; i < order.size(); ++i) order[i] = i;
    // (equal literal sequences by candidate order: std::sort leaves ties in a library-specific order)
    std::sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) {
      const auto fa = flat.begin() + spans[a].first, fb = flat.begin() + spans[b].first;
      if (std::lexicographical_compare(fa, fa + spans[a].second, fb, fb + spans[b].second, before)) return true;
      if (std::lexicographical_compare(fb, fb + spans[b].second, fa, fa + spans[a].second, before)) return false;
      return a < b;
    });
    for (const uint32_t i : order) {
      if (inconsistent_ || stats_.vivify_ticks > ticks_limit || stop_requested()) break;
      vivify_clause(static_cast<uint32_t>(cands[first + i]), flat.data() + spans[i].first, spans[i].second);
      ++processed;
    }
  }
  backtrack(0);
  if (processed >= 100) {
    const uint64_t per = (stats_.vivify_ticks - ticks_before) / processed + 1;
    vivify_ticks_per_clause_ = (vivify_ticks_per_clause_ + per) / 2;
  }
}

// Failed literal probing on the roots of the binary implication graph (literals that occur in no
// binary clause, so nothing implies them through binaries, but that imply others): a root whose
// propagation conflicts is false, giving the unit -root (RUP). Probes run at level 1 and book
// their ticks with vivification.
void Solver::probe_failed_literals(uint64_t ticks_limit) {
  const PassTimer pass_timer(*this, kPassProbe);
  std::vector<Lit> roots;
  for (Lit l = 0; l < 2 * num_vars_; ++l) {
    if (vals_[l] != 0 || eliminated_[var_of(l)]) continue;
    // (each scan stops at the first binary watch)
    bool implied = false;
    for (const Watch& w : watches_[l]) {
      if (w.binary()) {
        implied = true;
        break;
      }
    }
    if (implied) continue;
    bool implies = false;
    for (const Watch& w : watches_[negate(l)]) {
      if (w.binary()) {
        implies = true;
        break;
      }
    }
    if (implies) roots.push_back(l);
  }
  for (const Lit r : roots) {
    // With --probeuip a failed probe learns the negation of the conflict's first unique
    // implication point, which the probe implies; while the probe stays unassigned after that
    // unit, it is probed again (each round fixes a new variable).
    while (!inconsistent_ && stats_.vivify_ticks <= ticks_limit && vals_[r] == 0 && !stop_requested()) {
      ++stats_.probes;
      control_.push_back(static_cast<uint32_t>(trail_.size()));
      assign(r, kNoReason);
      const bool ok = propagate_vivify(kNoReason);
      const Lit uip = ok || !opts_.probeuip ? r : probe_uip();
      backtrack(0);
      if (ok) break;
      ++stats_.failed_literals;
      if (uip != r) ++stats_.probe_uips;
      const Lit unit = negate(uip);
      if (proof_) proof_->add_unit(unit);
      assign_unit_in_proof(unit);
      if (!propagate_vivify(kNoReason)) {
        inconsistent_ = true;
        if (proof_) proof_->add_empty();
      }
    }
    if (inconsistent_ || stats_.vivify_ticks > ticks_limit || stop_requested()) break;
  }
}

// The first unique implication point of the conflict of a failed probe (all of its implications
// are on level 1). Every path from the probe to the conflict passes through it, so its negation
// is a unit (RUP: assigning it propagates to the same conflict), implied by the negated probe.
Lit Solver::probe_uip() {
  probe_marked_.clear();
  uint32_t open = 0;
  size_t i = trail_.size();
  Lit uip = kNoLit;
  Lit tmp[2];
  const Lit* lits;
  uint32_t n;
  if (conflict_ref_ == kNoReason) {
    tmp[0] = conflict_bin_[0];
    tmp[1] = conflict_bin_[1];
    lits = tmp;
    n = 2;
  } else {
    const Clause& c = clause(conflict_ref_);
    lits = c.lits();
    n = c.size;
  }
  for (;;) {
    for (uint32_t k = 0; k < n; ++k) {
      const Var v = var_of(lits[k]);
      if (flags_[v] || vdata_[v].level == 0) continue;
      flags_[v] = kSeen;
      probe_marked_.push_back(v);
      ++open;
    }
    do {
      uip = trail_[--i];
    } while (!(flags_[var_of(uip)] & kSeen));
    if (--open == 0) break;
    const uint32_t r = vdata_[var_of(uip)].reason;
    if (r & kBinaryTag) {
      tmp[0] = r & ~kBinaryTag;
      lits = tmp;
      n = 1;
    } else {
      const Clause& c = clause(r);
      lits = c.lits();
      n = c.size;
    }
  }
  for (const Var v : probe_marked_) flags_[v] = 0;
  return uip;
}

bool Solver::vivify_clause(uint32_t ref, const Lit* lits, uint32_t n) {
  {
    Clause& c = clause(ref);
    if (c.garbage) return false;
    c.vivified = 1;
    if (c.redundant) ++stats_.vivify_checked_learned;
  }
  ++stats_.vivify_checked;
  // Satisfied at the root: just remove it.
  for (uint32_t i = 0; i < n; ++i) {
    const Lit l = lits[i];
    if (vals_[l] > 0 && vdata_[var_of(l)].level == 0) {
      Clause& c = clause(ref);
      delete_clause_proof(c);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      return false;
    }
  }
  // Keep the decisions of the previous clause that are negations of this clause's first
  // literals (skipping literals already false below them).
  uint32_t keep = 0;
  for (uint32_t i = 0; i < n; ++i) {
    const Lit x = lits[i];
    if (keep < level() && trail_[control_[keep]] == negate(x)) {
      ++keep;
      continue;
    }
    if (vals_[x] < 0 && vdata_[var_of(x)].level <= keep) continue;
    break;
  }
  backtrack(keep);
  // Implications through this very clause must not be kept (it is ignored while vivifying it).
  if (level() > 0) {
    for (size_t t = control_[0]; t < trail_.size(); ++t) {
      const VarData& d = vdata_[var_of(trail_[t])];
      if (d.reason == ref) {
        backtrack(d.level - 1);
        break;
      }
    }
  }
  viv_decided_.clear();
  Lit implied = kNoLit;
  bool conflict = false;
  for (uint32_t i = 0; i < n; ++i) {
    const Lit x = lits[i];
    const int8_t v = vals_[x];
    if (v < 0) {
      // False: either one of the decisions (the negation of a literal of this clause, kept from
      // the previous clause), or implied false by the earlier literals and dropped.
      const VarData& d = vdata_[var_of(x)];
      if (d.level > 0 && d.reason == kNoReason) viv_decided_.push_back(x);
      continue;
    }
    if (v > 0) {
      implied = x;
      break;
    }
    control_.push_back(static_cast<uint32_t>(trail_.size()));
    assign(negate(x), kNoReason);
    viv_decided_.push_back(x);
    if (!propagate_vivify(ref)) {
      conflict = true;
      break;
    }
  }
  // Subsumed: the clause that conflicted (or implied the true literal) has only decided literals
  // besides (negations of literals of C), so it is a subset of C. C goes, unless C is
  // irredundant and the subsuming clause learned (then C is replaced by a copy below as usual).
  if (opts_.vivifysubsume && (conflict || implied != kNoLit) && vivify_subsumed(implied, clause(ref).redundant)) {
    if (conflict) backtrack(level() - 1);
    Clause& c = clause(ref);
    if (c.redundant) {
      delete_clause_proof(c);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      --redundant_;
    } else {
      delete_irredundant(ref);
    }
    ++stats_.vivify_subsumed;
    return true;
  }
  // Keep only the decisions the conflict (or the implication of the true literal) depends on.
  const bool track = opts_.vivifyasym && !clause(ref).redundant;
  if (conflict || implied != kNoLit) vivify_analyze(conflict ? kNoLit : implied, track);
  if (conflict) backtrack(level() - 1);  // back to a consistent state
  const uint32_t old_size = n;
  // Instantiation (Kissat): every literal false without a conflict. Flip the last decision: if
  // its literal x true (with the others false) conflicts too, x can go, since C without x is RUP
  // (falsifying it makes C unit on x, which propagates to that conflict).
  if (!conflict && implied == kNoLit && opts_.vivifyinst && n >= 3 && viv_decided_.size() == n && level() > 0) {
    const Lit x = viv_decided_.back();
    if (trail_[control_[level() - 1]] == negate(x)) {
      backtrack(level() - 1);
      control_.push_back(static_cast<uint32_t>(trail_.size()));
      assign(x, kNoReason);
      const bool inst_conflict = !propagate_vivify(ref);
      backtrack(level() - 1);
      if (inst_conflict) {
        viv_decided_.pop_back();
        ++stats_.vivify_instantiated;
      }
    }
  }
  if (viv_decided_.size() >= old_size) {
    // Implied by other clauses (a literal true under the negation of the others) and not
    // shorter: a learned clause adds nothing, delete it.
    if (implied != kNoLit && opts_.vivifyimplied && clause(ref).redundant) {
      backtrack(0);
      Clause& c = clause(ref);
      delete_clause_proof(c);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      --redundant_;
      ++stats_.vivify_implied_deleted;
      return true;
    }
    // An irredundant clause implied by the other irredundant clauses alone (an asymmetric
    // tautology): the formula without it is equivalent, so it goes. Its variables lose an
    // occurrence, which can make them eliminable.
    if (track && (conflict || implied != kNoLit) && !viv_used_redundant_) {
      backtrack(0);
      delete_irredundant(ref);
      ++stats_.vivify_asym;
      return true;
    }
    return false;
  }
  backtrack(0);  // the replacement is added at the root
  viv_lits_.assign(lits, lits + n);

  // Replace C by the shorter clause.
  ++stats_.vivified;
  stats_.vivified_literals += old_size - viv_decided_.size();
  const bool red = clause(ref).redundant;
  if (red) ++stats_.vivified_learned;
  const uint32_t glue = clause(ref).glue;
  if (proof_) proof_->add(viv_decided_.data(), viv_decided_.size());
  {
    Clause& c = clause(ref);
    delete_clause_proof(c);
    c.garbage = 1;
    note_garbage(c);
    garbage_words_ += kHeaderWords + c.size;
    if (red) {
      --redundant_;
    } else {
      --irredundant_;
    }
  }
  if (!red) touch_clause(viv_lits_.data(), old_size);
  if (viv_decided_.empty()) {  // cannot happen at a consistent root, but stay safe
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return true;
  }
  if (viv_decided_.size() == 1) {
    assign_unit_in_proof(viv_decided_[0]);  // added above
    // Garbage clauses are still watched until the round ends: skip them (they are deleted in the
    // proof, so they must not justify the root units found here).
    if (!propagate_vivify(kNoReason)) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
    }
    return true;
  }
  if (viv_decided_.size() == 2) {
    add_binary(viv_decided_[0], viv_decided_[1], red);
    return true;
  }
  const uint32_t size = static_cast<uint32_t>(viv_decided_.size());
  const uint32_t nref = new_clause(viv_decided_.data(), size, red, std::min(glue, size - 1));
  clause(nref).vivified = 1;
  return true;
}

// Conflict analysis for vivification: walks the implication graph from the conflict (or from the
// implied true literal) back to the decisions, which are negations of literals of the clause
// being vivified. viv_decided_ becomes the clause literals of the involved decisions (plus the
// implied literal): assigning their negations propagates to the same conflict, so the clause is
// RUP, and it is often much shorter than all decisions taken (as in CaDiCaL and Kissat).
// With track_redundant, viv_used_redundant_ tells whether a learned clause took part.
void Solver::vivify_analyze(Lit implied, bool track_redundant) {
  viv_decided_.clear();
  viv_used_redundant_ = false;
  auto mark = [&](Lit l) {
    const Var v = var_of(l);
    if ((flags_[v] & kSeen) || vdata_[v].level == 0) return;
    flags_[v] |= kSeen;
    viv_marked_.push_back(v);
  };
  if (implied != kNoLit) {
    mark(implied);
  } else if (conflict_ref_ == kNoReason) {
    mark(conflict_bin_[0]);
    mark(conflict_bin_[1]);
    if (track_redundant && !irredundant_binary(conflict_bin_[0], conflict_bin_[1])) viv_used_redundant_ = true;
  } else {
    const Clause& c = clause(conflict_ref_);
    viv_used_redundant_ = viv_used_redundant_ || c.redundant;
    for (uint32_t k = 0; k < c.size; ++k) mark(c.lits()[k]);
  }
  size_t open = viv_marked_.size();
  for (size_t t = trail_.size(); open > 0 && t-- > 0;) {
    const Lit l = trail_[t];
    const Var v = var_of(l);
    if (!(flags_[v] & kSeen)) continue;
    --open;
    const uint32_t r = vdata_[v].reason;
    if (r == kNoReason) {  // a decision: the negation of a literal of the clause
      viv_decided_.push_back(negate(l));
      continue;
    }
    const size_t before = viv_marked_.size();
    if (r & kBinaryTag) {
      const Lit o = static_cast<Lit>(r & ~kBinaryTag);  // the reason is the binary (l o)
      if (track_redundant && !viv_used_redundant_ && !irredundant_binary(o, l)) viv_used_redundant_ = true;
      mark(o);
    } else {
      const Clause& c = clause(r);
      viv_used_redundant_ = viv_used_redundant_ || c.redundant;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (c.lits()[k] != l) mark(c.lits()[k]);
      }
    }
    open += viv_marked_.size() - before;
  }
  for (const Var v : viv_marked_) flags_[v] &= static_cast<uint8_t>(~kSeen);
  viv_marked_.clear();
  if (implied != kNoLit) viv_decided_.push_back(implied);
}

// Whether the conflict clause (implied == kNoLit) or the reason of the implied true literal has
// only decisions besides (the negations of literals of the clause being vivified): then it is a
// subset of that clause. For an irredundant clause the subsuming clause has to be irredundant.
bool Solver::vivify_subsumed(Lit implied, bool redundant) {
  auto decided = [&](Lit l) {
    const VarData& d = vdata_[var_of(l)];
    return vals_[l] < 0 && d.level > 0 && d.reason == kNoReason;
  };
  if (implied == kNoLit && conflict_ref_ == kNoReason) {
    return decided(conflict_bin_[0]) && decided(conflict_bin_[1]) &&
           (redundant || irredundant_binary(conflict_bin_[0], conflict_bin_[1]));
  }
  uint32_t r = conflict_ref_;
  if (implied != kNoLit) {
    r = vdata_[var_of(implied)].reason;
    if (r == kNoReason) return false;
    if (r & kBinaryTag) {
      const Lit o = static_cast<Lit>(r & ~kBinaryTag);
      return decided(o) && (redundant || irredundant_binary(implied, o));
    }
  }
  const Clause& d = clause(r);
  if (!redundant && d.redundant) return false;
  stats_.vivify_ticks += 1 + d.size / 8;
  for (uint32_t k = 0; k < d.size; ++k) {
    const Lit l = d.lits()[k];
    if (l != implied && !decided(l)) return false;
  }
  return true;
}

// Whether an irredundant copy of the binary clause (a b) exists; it is watched in watches_[a]
// with blocking literal b. The scan is charged to vivification.
bool Solver::irredundant_binary(Lit a, Lit b) {
  const auto ws = watches_[a];
  stats_.vivify_ticks += 1 + (ws.size() >> 3);
  for (const Watch& w : ws) {
    if (w.binary() && w.blit == b && !w.redundant_binary()) return true;
  }
  return false;
}

}  // namespace psat
