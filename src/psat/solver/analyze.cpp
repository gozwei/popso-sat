// Conflict analysis: first-UIP learning, recursive minimization (MiniSat / Van Gelder, with the
// level checks of CaDiCaL), glue (LBD) computation and updates of used learned clauses, variable
// bumping, backjumping.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "psat/core/radix_sort.hpp"
#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

uint32_t Solver::recompute_glue(const Clause& c) {
  const uint64_t stamp = ++glue_stamp_;
  uint32_t glue = 0;
  const Lit* lits = c.lits();
  for (uint32_t i = 0; i < c.size; ++i) {
    const uint32_t lvl = vdata_[var_of(lits[i])].level;
    if (level_stamp_[lvl] != stamp) {
      level_stamp_[lvl] = stamp;
      if (++glue >= c.glue) break;  // no improvement possible
    }
  }
  return glue;
}

void Solver::bump_reason_clause(uint32_t ref) {
  Clause& c = clause(ref);
  if (!stable_) ++used_glue_[std::min<uint32_t>(c.glue, kGlueBuckets - 1)];
  if (!c.keep) {
    const uint32_t glue = recompute_glue(c);
    if (glue < c.glue) {
      c.glue = glue;
      if (glue <= tier1_) c.keep = 1;
    }
  }
  c.used = c.glue <= tier2_ ? 2 : 1;
}

void Solver::remove_long_watch(Lit l, uint32_t ref) {
  const WatchList ws = watches_[l];
  for (size_t k = 0; k < ws.size(); ++k) {
    if (!ws[k].binary() && ws[k].ref == ref) {
      ws[k] = ws.back();
      ws.pop_back();
      return;
    }
  }
}

// Chronological backtracking (Nadel & Ryvchin 2018; Moehle & Biere 2019, as in CaDiCaL): the
// conflict can be below the current level. Returns the highest level among the conflict's
// literals, how many are on it and (if one) which. A long conflict clause gets its two
// highest-level literals as watches, so that it is watched correctly after backtracking.
uint32_t Solver::conflict_level(Lit& forced, uint32_t& count) {
  Lit tmp[2];
  Lit* lits;
  uint32_t n;
  if (conflict_ref_ == kNoReason) {
    tmp[0] = conflict_bin_[0];
    tmp[1] = conflict_bin_[1];
    lits = tmp;
    n = 2;
  } else if (conflict_ref_ == kGaussConflict) {
    lits = gauss_conflict_.data();
    n = static_cast<uint32_t>(gauss_conflict_.size());
  } else {
    Clause& c = clause(conflict_ref_);
    lits = c.lits();
    n = c.size;
  }
  uint32_t res = 0;
  count = 0;
  forced = kNoLit;
  for (uint32_t k = 0; k < n; ++k) {
    const uint32_t lvl = vdata_[var_of(lits[k])].level;
    if (lvl > res) {
      res = lvl;
      forced = lits[k];
      count = 1;
    } else if (lvl == res) {
      ++count;
    }
  }
  if (conflict_ref_ != kNoReason && conflict_ref_ != kGaussConflict) {
    for (uint32_t i = 0; i < 2; ++i) {
      const Lit lit = lits[i];
      uint32_t best = i, best_level = vdata_[var_of(lit)].level;
      for (uint32_t k = i + 1; k < n; ++k) {
        const uint32_t lvl = vdata_[var_of(lits[k])].level;
        if (lvl > best_level) {
          best = k;
          best_level = lvl;
          if (lvl == res) break;
        }
      }
      if (best == i) continue;
      const Lit high = lits[best];
      if (best > 1) remove_long_watch(lit, conflict_ref_);
      lits[best] = lit;
      lits[i] = high;
      if (best > 1) watches_[high].push_back(Watch{lits[1 - i], conflict_ref_});
    }
  }
  return res;
}

bool Solver::analyze() {
  ++stats_.conflicts;
  if (stable_) {
    ++stats_.stable_conflicts;
  } else {
    ++stats_.focused_conflicts;
  }
  if (opts_.chrono) {
    Lit forced;
    uint32_t count;
    const uint32_t lvl = conflict_level(forced, count);
    if (lvl == 0) return false;
    if (count == 1) {
      // A missed lower implication: all but one literal were false below its level. Backtrack
      // below that level and assign it, with the conflict clause as reason.
      ++stats_.chrono_missed;
      const Lit other = conflict_ref_ == kNoReason ? (conflict_bin_[0] == forced ? conflict_bin_[1] : conflict_bin_[0])
                                                   : clause(conflict_ref_).lits()[1];  // (forced is lits[0])
      const uint32_t other_level = vdata_[var_of(other)].level;
      uint32_t target = lvl - 1;
      // --chrono=2: the implications of the last chronologically backtracked UIP contradict the
      // levels kept above its backjump level (no decision since). Popping one level per such
      // conflict would re-propagate the UIP's implications each time (on linked_list about ten
      // in a row); backjump as without chronological backtracking instead.
      if (opts_.chrono >= 2 && chrono_jump_ < target && stats_.decisions == chrono_decisions_) {
        ++stats_.chrono_fallbacks;
        target = chrono_jump_;
      }
      chrono_jump_ = UINT32_MAX;
      backtrack(target);
      if (other_level <= target) {  // (else the conflict clause is not unit after the backjump)
        assign_at(forced, conflict_ref_ == kNoReason ? kBinaryTag | other : conflict_ref_, other_level);
      }
      return true;
    }
    if (lvl < level()) {
      ++stats_.chrono_conflict_backtracks;
      backtrack(lvl);
    }
  }
  update_target_and_best(control_.back());

  const uint32_t cur = level();
  learned_.clear();
  learned_.push_back(kNoLit);
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
  } else if (conflict_ref_ == kGaussConflict) {
    lits = gauss_conflict_.data();
    n = static_cast<uint32_t>(gauss_conflict_.size());
  } else {
    Clause& c = clause(conflict_ref_);
    if (c.redundant) bump_reason_clause(conflict_ref_);
    lits = c.lits();
    n = c.size;
  }
  // (local base pointers: the uint8_t flag stores may alias any member for the compiler)
  uint8_t* const flags = flags_.data();
  const VarData* const vdata = vdata_.data();
  LevelInfo* const levels = levels_.data();
  const Lit* const trail = trail_.data();
  for (;;) {
    for (uint32_t k = 0; k < n; ++k) {
      const Lit l = lits[k];
      const Var v = var_of(l);
      if (flags[v]) continue;
      const VarData& d = vdata[v];
      if (d.level == 0) continue;
      flags[v] = kSeen;
      analyzed_.push_back(v);
      if (d.level == cur) {
        ++open;
      } else {
        learned_.push_back(l);
        LevelInfo& li = levels[d.level];
        if (li.seen++ == 0) touched_levels_.push_back(d.level);
        if (d.trail < li.trail) li.trail = d.trail;
      }
    }
    // (With chronological backtracking, seen literals of lower levels can follow on the trail.)
    do {
      uip = trail[--i];
    } while (!(flags[var_of(uip)] & kSeen) || vdata[var_of(uip)].level != cur);
    if (--open == 0) break;
    const uint32_t r = vdata[var_of(uip)].reason;
    if (r >= kGaussTag) {  // (never kNoReason: uip is implied)
      lits = gauss_reason(r, n);
    } else if (r & kBinaryTag) {
      tmp[0] = r & ~kBinaryTag;
      lits = tmp;
      n = 1;
    } else {
      Clause& c = clause(r);
      if (c.redundant) bump_reason_clause(r);
      lits = c.lits();
      n = c.size;
    }
  }
  learned_[0] = negate(uip);
  const size_t before = learned_.size();
  if (opts_.minimize && learned_.size() > 1) minimize_clause();
  if (opts_.shrink && learned_.size() > 2) shrink_clause();
  stats_.minimized_literals += before - learned_.size();

  // Glue, backjump level, and the highest-level literal moved to position 1 (second watch).
  const uint64_t stamp = ++glue_stamp_;
  uint32_t glue = 0, jump = 0;
  for (size_t k = 0; k < learned_.size(); ++k) {
    const uint32_t lvl = vdata_[var_of(learned_[k])].level;
    if (level_stamp_[lvl] != stamp) {
      level_stamp_[lvl] = stamp;
      ++glue;
    }
    if (k > 0 && lvl > jump) {
      jump = lvl;
      std::swap(learned_[1], learned_[k]);
    }
  }

  if (opts_.bumpreasons && learned_.size() <= static_cast<size_t>(opts_.bumpreasonslimit)) bump_reason_literals();
  bump_variables();

  for (Var v : analyzed_) flags_[v] = 0;
  analyzed_.clear();
  for (uint32_t lvl : touched_levels_) levels_[lvl] = LevelInfo{};
  touched_levels_.clear();

  // Chronological backtracking: a backjump over many levels throws away assignments that would
  // mostly be made again; backtrack one level instead and assign the UIP at its own level.
  uint32_t target = jump;
  chrono_jump_ = UINT32_MAX;
  if (opts_.chrono && (learned_.size() > 1 || opts_.chronounits) && cur - jump > static_cast<uint32_t>(opts_.chronolevels)) {
    target = cur - 1;
    ++stats_.chrono_backtracks;
    chrono_jump_ = jump;
    chrono_decisions_ = stats_.decisions;
  }
  stats_.conflict_levels += cur;
  stats_.backjump_levels += cur - target;
  backtrack(target);
  learn_clause(jump, glue);
  update_conflict_statistics(glue);
  return true;
}

void Solver::minimize_clause() {
  size_t j = 1;
  for (size_t k = 1; k < learned_.size(); ++k) {
    const Lit l = learned_[k];
    if (!minimize_literal(negate(l), 0)) learned_[j++] = l;
  }
  learned_.resize(j);
  for (Var v : minimized_) flags_[v] &= kSeen;
  minimized_.clear();
}

// Shrinking (Fleury & Biere, SAT 2021): the literals of one decision level in the learned clause
// are replaced by the level's block UIP when every reason literal met while resolving within the
// level is on that level, at the root, or in (or implied by) the learned clause. The result is
// RUP like the minimized clause.
void Solver::shrink_clause() {
  // Group by level (descending), latest trail position first. Sorted (ascending, radix) as the
  // complements of the 64-bit keys level << 32 | trail position, one read per literal instead of
  // two per comparison; the positions are distinct, so the order does not depend on the sort, and
  // each literal is the negation of the trail literal at its position.
  sort_keys_.clear();
  for (size_t k = 1; k < learned_.size(); ++k) {
    const VarData& d = vdata_[var_of(learned_[k])];
    sort_keys_.push_back(~((uint64_t{d.level} << 32) | d.trail));
  }
  radix_sort_keys(sort_keys_, sort_tmp_);
  for (size_t k = 1; k < learned_.size(); ++k) learned_[k] = negate(trail_[static_cast<uint32_t>(~sort_keys_[k - 1])]);
  size_t out = 1;
  size_t i = 1;
  while (i < learned_.size()) {
    const uint32_t lvl = vdata_[var_of(learned_[i])].level;
    size_t j = i + 1;
    while (j < learned_.size() && vdata_[var_of(learned_[j])].level == lvl) ++j;
    if (j - i < 2) {
      learned_[out++] = learned_[i];
      i = j;
      continue;
    }
    // Resolve backwards along the trail within level lvl until one open literal is left.
    shrunk_.clear();
    for (size_t k = i; k < j; ++k) {
      flags_[var_of(learned_[k])] |= kShrinkable;
      shrunk_.push_back(var_of(learned_[k]));
    }
    uint32_t open = static_cast<uint32_t>(j - i);
    size_t pos = vdata_[var_of(learned_[i])].trail;
    const size_t bottom = control_[lvl - 1];
    Lit uip = kNoLit;
    bool ok = true;
    uint64_t steps = 0;
    for (;;) {
      const Lit t = trail_[pos];
      const Var v = var_of(t);
      if (flags_[v] & kShrinkable) {
        if (--open == 0) {
          uip = t;
          break;
        }
        const uint32_t r = vdata_[v].reason;
        if (r == kNoReason) {
          ok = false;
          break;
        }
        auto visit = [&](Lit o) {
          const Var u = var_of(o);
          const VarData& d = vdata_[u];
          if (d.level == lvl) {
            if (!(flags_[u] & kShrinkable)) {
              flags_[u] |= kShrinkable;
              shrunk_.push_back(u);
              ++open;
            }
          } else if (d.level != 0 && !(flags_[u] & kSeen)) {
            // Not in the clause: with --shrink=2 (Kissat's shrink=3) it may still be implied by
            // the clause's lower-level literals (the minimization check, depth 1).
            if (opts_.shrink < 2 || !minimize_literal(negate(o), 1)) ok = false;
          }
        };
        if (r >= kGaussTag) {
          uint32_t n;
          const Lit* lits = gauss_reason(r, n);
          for (uint32_t k = 0; k < n && ok; ++k) {
            if (var_of(lits[k]) != v) visit(lits[k]);
          }
          steps += n;
        } else if (r & kBinaryTag) {
          visit(r & ~kBinaryTag);
        } else {
          const Clause& c = clause(r);
          for (uint32_t k = 0; k < c.size && ok; ++k) {
            if (var_of(c.lits()[k]) != v) visit(c.lits()[k]);
          }
          steps += c.size;
        }
        if (!ok || steps > 10000) {
          ok = false;
          break;
        }
      }
      if (pos == bottom) {
        ok = false;
        break;
      }
      --pos;
    }
    for (const Var v : shrunk_) flags_[v] &= static_cast<uint8_t>(~kShrinkable);
    if (ok) {
      learned_[out++] = negate(uip);
      stats_.shrunk_literals += (j - i) - 1;
    } else {
      for (size_t k = i; k < j; ++k) learned_[out++] = learned_[k];
    }
    i = j;
  }
  learned_.resize(out);
  for (Var v : minimized_) flags_[v] &= kSeen;  // (marks of the minimization checks)
  minimized_.clear();
}

// lit is true on the trail (its negation is in, or implied by, the learned clause). Returns true
// if lit is implied by the other literals of the learned clause.
bool Solver::minimize_literal(Lit lit, uint32_t depth) {
  const Var v = var_of(lit);
  const uint8_t f = flags_[v];
  const VarData& d = vdata_[v];
  if (d.level == 0 || (f & kRemovable) || (depth && (f & kSeen))) return true;
  if ((f & kPoison) || d.reason == kNoReason) return false;
  const LevelInfo& li = levels_[d.level];
  // A literal can only be implied by clause literals of its own level that precede it.
  if ((!depth && li.seen < 2) || d.trail <= li.trail) return false;
  if (depth > static_cast<uint32_t>(opts_.minimizedepth)) return false;
  bool res = true;
  const uint32_t r = d.reason;
  if ((r & kBinaryTag) && r < kGaussTag) {
    res = minimize_literal(negate(r & ~kBinaryTag), depth + 1);
  } else {
    uint32_t n;
    const Lit* lits;
    if (r >= kGaussTag) {
      lits = gauss_reason(r, n);
    } else {
      const Clause& c = clause(r);
      lits = c.lits();
      n = c.size;
    }
    for (uint32_t k = 0; k < n; ++k) {
      const Lit o = lits[k];
      const Var u = var_of(o);
      if (u == v) continue;
      // The first checks of the recursive call (depth > 0), inline: most reason literals are
      // decided by their flags or root level without a call.
      const uint8_t fu = flags_[u];
      if (fu & (kSeen | kRemovable)) continue;
      if (vdata_[u].level == 0) continue;
      if ((fu & kPoison) || !minimize_literal(negate(o), depth + 1)) {
        res = false;
        break;
      }
    }
  }
  flags_[v] |= res ? kRemovable : kPoison;
  minimized_.push_back(v);
  return res;
}

// Bumps the variables of the reasons of the learned clause's literals as well (Kissat's
// "bumpreasons"): they took part in the conflict one resolution step further away.
void Solver::bump_reason_literals() {
  for (size_t k = 1; k < learned_.size(); ++k) {
    const uint32_t r = vdata_[var_of(learned_[k])].reason;
    if (r == kNoReason) continue;
    if ((r & kBinaryTag) && r < kGaussTag) {
      const Var u = var_of(r & ~kBinaryTag);
      if (!flags_[u] && vdata_[u].level) {
        flags_[u] = kSeen;
        analyzed_.push_back(u);
      }
      continue;
    }
    uint32_t n;
    const Lit* lits;
    if (r >= kGaussTag) {
      lits = gauss_reason(r, n);
    } else {
      const Clause& c = clause(r);
      lits = c.lits();
      n = c.size;
    }
    for (uint32_t m = 0; m < n; ++m) {
      const Var u = var_of(lits[m]);
      if (flags_[u] || !vdata_[u].level) continue;
      flags_[u] = kSeen;
      analyzed_.push_back(u);
    }
  }
}

void Solver::learn_clause(uint32_t jump, uint32_t glue) {
  ++stats_.learned;
  stats_.learned_literals += learned_.size();
  stats_.learned_glue += glue;
  const Lit uip = learned_[0];
  if (learned_.size() == 1) {
    ++stats_.learned_units;
    // Root level (logged to the proof by on_root_fixed); with --chronounits out of order, above
    // the levels kept by the chronological backtrack.
    assign_at(uip, kNoReason, 0);
    return;
  }
  if (proof_) proof_->add(learned_.data(), learned_.size());
  if (opts_.eagersubsume) eager_subsume();
  if (learned_.size() == 2) {
    ++stats_.learned_binary;
    add_binary(learned_[0], learned_[1], true);
    assign_at(uip, kBinaryTag | learned_[1], jump);
    return;
  }
  const uint32_t ref = new_clause(learned_.data(), static_cast<uint32_t>(learned_.size()), true, glue);
  assign_at(uip, ref, jump);
  if (opts_.eagersubsume) {
    if (recent_learned_.size() >= static_cast<size_t>(opts_.eagersubsume)) {
      recent_learned_.erase(recent_learned_.begin());
    }
    recent_learned_.push_back(ref);
  }
}

// Eager subsumption (as in Kissat and CaDiCaL): the new learned clause often subsumes one of the
// last few learned clauses (it was derived from a conflict they were part of), which can then be
// deleted. Clauses that are reasons on the trail are kept.
void Solver::eager_subsume() {
  const ProofScope proof_scope(*this, kProofEager);
  const uint32_t n = static_cast<uint32_t>(learned_.size());
  for (const Lit l : learned_) marks_[l] = 1;
  for (const uint32_t ref : recent_learned_) {
    Clause& c = clause(ref);
    if (c.garbage || c.size <= n) continue;
    const Lit first = c.lits()[0];
    if (vals_[first] > 0 && vdata_[var_of(first)].reason == ref) continue;
    // (stops once the literals left cannot make up the missing ones)
    uint32_t found = 0;
    const Lit* lits = c.lits();
    for (uint32_t k = 0; k < c.size && found < n && c.size - k >= n - found; ++k) found += marks_[lits[k]] ? 1u : 0u;
    if (found < n) continue;
    ++stats_.eager_subsumed;
    delete_clause_proof(c);
    c.garbage = 1;
    note_garbage(c);
    garbage_words_ += kHeaderWords + c.size;
    --redundant_;
  }
  for (const Lit l : learned_) marks_[l] = 0;
}

void Solver::backtrack(uint32_t new_level) {
  if (level() <= new_level) return;
  if (gauss_on_) gauss_backtrack(new_level);
  const uint32_t start = control_[new_level];
  size_t j = start;
  if (opts_.chrono) {
    // With chronological backtracking, literals of levels <= new_level can be above `start`: they
    // stay (moved down, order kept) and are propagated again. The others follow them, in order.
    backtrack_tmp_.clear();
    for (size_t i = start; i < trail_.size(); ++i) {
      const Lit l = trail_[i];
      const Var v = var_of(l);
      if (vdata_[v].level <= new_level) {
        vdata_[v].trail = static_cast<uint32_t>(j);
        trail_[j++] = l;
      } else {
        backtrack_tmp_.push_back(l);
      }
    }
    std::copy(backtrack_tmp_.begin(), backtrack_tmp_.end(), trail_.begin() + j);
  }
  // Unassign trail_[j..) from the top (the order decides ties in the heap). Both values of a
  // variable are cleared with one 2-byte store; variables still in the heap are not pushed (the
  // push would return at once, but as a call).
  int8_t* const vals = vals_.data();
  const Lit* const trail = trail_.data();
  if (stable_) {
    for (size_t i = trail_.size(); i-- > j;) {
      const Var v = var_of(trail[i]);
      std::memset(vals + 2 * size_t{v}, 0, 2);
      if (!heap_.contains(v)) heap_.push(v);
    }
  } else {
    const uint64_t* const bumped = bumped_.data();
    Var search = queue_search_;
    uint64_t search_stamp = search == UINT32_MAX ? 0 : bumped[search];
    for (size_t i = trail_.size(); i-- > j;) {
      const Var v = var_of(trail[i]);
      std::memset(vals + 2 * size_t{v}, 0, 2);
      if (bumped[v] > search_stamp) {
        search = v;
        search_stamp = bumped[v];
      }
    }
    queue_search_ = search;
  }
  trail_.resize(j);
  if (propagated_ > start) propagated_ = start;
  control_.resize(new_level);
}

}  // namespace psat
