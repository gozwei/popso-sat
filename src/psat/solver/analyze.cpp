// Conflict analysis: first-UIP learning, recursive minimization (MiniSat / Van Gelder, with the
// level checks of CaDiCaL), glue (LBD) computation and updates of used learned clauses, variable
// bumping, backjumping.

#include <algorithm>

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

void Solver::analyze() {
  ++stats_.conflicts;
  if (stable_) {
    ++stats_.stable_conflicts;
  } else {
    ++stats_.focused_conflicts;
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
  } else {
    Clause& c = clause(conflict_ref_);
    if (c.redundant) bump_reason_clause(conflict_ref_);
    lits = c.lits();
    n = c.size;
  }
  for (;;) {
    for (uint32_t k = 0; k < n; ++k) {
      const Lit l = lits[k];
      const Var v = var_of(l);
      if (flags_[v]) continue;
      const VarData& d = vdata_[v];
      if (d.level == 0) continue;
      flags_[v] = kSeen;
      analyzed_.push_back(v);
      if (d.level == cur) {
        ++open;
      } else {
        learned_.push_back(l);
        LevelInfo& li = levels_[d.level];
        if (li.seen++ == 0) touched_levels_.push_back(d.level);
        if (d.trail < li.trail) li.trail = d.trail;
      }
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

  backtrack(jump);
  learn_clause(jump, glue);
  update_conflict_statistics(glue);
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
  // Group by level (descending), latest trail position first.
  std::sort(learned_.begin() + 1, learned_.end(), [this](Lit a, Lit b) {
    const VarData& x = vdata_[var_of(a)];
    const VarData& y = vdata_[var_of(b)];
    return x.level != y.level ? x.level > y.level : x.trail > y.trail;
  });
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
            ok = false;
          }
        };
        if (r & kBinaryTag) {
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
  if (r & kBinaryTag) {
    res = minimize_literal(negate(r & ~kBinaryTag), depth + 1);
  } else {
    const Clause& c = clause(r);
    const Lit* lits = c.lits();
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit o = lits[k];
      if (var_of(o) == v) continue;
      if (!minimize_literal(negate(o), depth + 1)) {
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
    if (r & kBinaryTag) {
      const Var u = var_of(r & ~kBinaryTag);
      if (!flags_[u] && vdata_[u].level) {
        flags_[u] = kSeen;
        analyzed_.push_back(u);
      }
      continue;
    }
    const Clause& c = clause(r);
    const Lit* lits = c.lits();
    for (uint32_t m = 0; m < c.size; ++m) {
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
  const Lit uip = learned_[0];
  if (learned_.size() == 1) {
    ++stats_.learned_units;
    assign(uip, kNoReason);  // root level: logged to the proof by on_root_fixed
    return;
  }
  if (proof_) proof_->add(learned_.data(), learned_.size());
  if (opts_.eagersubsume) eager_subsume();
  if (learned_.size() == 2) {
    ++stats_.learned_binary;
    add_binary(learned_[0], learned_[1], true);
    assign(uip, kBinaryTag | learned_[1]);
    return;
  }
  const uint32_t ref = new_clause(learned_.data(), static_cast<uint32_t>(learned_.size()), true, glue);
  assign(uip, ref);
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
  const uint32_t n = static_cast<uint32_t>(learned_.size());
  for (const Lit l : learned_) marks_[l] = 1;
  for (const uint32_t ref : recent_learned_) {
    Clause& c = clause(ref);
    if (c.garbage || c.size <= n) continue;
    const Lit first = c.lits()[0];
    if (vals_[first] > 0 && vdata_[var_of(first)].reason == ref) continue;
    uint32_t found = 0;
    for (uint32_t k = 0; k < c.size && found < n; ++k) found += marks_[c.lits()[k]] ? 1u : 0u;
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
  const uint32_t start = control_[new_level];
  if (stable_) {
    for (size_t i = trail_.size(); i-- > start;) {
      const Lit l = trail_[i];
      vals_[l] = vals_[negate(l)] = 0;
      heap_.push(var_of(l));
    }
  } else {
    Var search = queue_search_;
    uint64_t search_stamp = search == UINT32_MAX ? 0 : bumped_[search];
    for (size_t i = trail_.size(); i-- > start;) {
      const Lit l = trail_[i];
      vals_[l] = vals_[negate(l)] = 0;
      const Var v = var_of(l);
      if (bumped_[v] > search_stamp) {
        search = v;
        search_stamp = bumped_[v];
      }
    }
    queue_search_ = search;
  }
  trail_.resize(start);
  if (propagated_ > start) propagated_ = start;
  control_.resize(new_level);
}

}  // namespace psat
