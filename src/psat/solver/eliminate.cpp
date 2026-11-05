// Simplification rounds at the root level: forward subsumption / strengthening (subsume.cpp)
// followed by bounded variable elimination (Een & Biere, SAT 2005) with the clause-count bound
// raised gradually over rounds (0, 1, 2, 4, ... eliminatebound, as Kissat does).
//
// During a round the long-clause watches are detached ("dense mode"): clauses can then be
// strengthened or replaced in place, resolvents are added unwatched, and occurrence lists over
// the irredundant long clauses stand in for the watches. Binary clauses stay in the watch lists,
// which double as their occurrence lists. At the end all long clauses are reattached on two
// non-false literals and the whole root trail is propagated again, which picks up units found
// during the round and any clause that became unit.
//
// Every eliminated variable's clauses go on the extension stack with the variable's literal as
// witness; after a SAT answer the stack is replayed backwards and each unsatisfied clause gets its
// witness flipped to true, which yields a model of the original formula.
//
// DRAT: resolvents and strengthened clauses are RUP and added before the clauses they replace are
// deleted.

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cmath>

#include "psat/io/proof.hpp"
#include "psat/core/small_sort.hpp"
#include "psat/solver/kitten.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

bool Solver::eliminating() const {
  if (!opts_.eliminate || stats_.conflicts < eliminate_limit_) return false;
  // A round costs about one pass over the arena (occurrence lists, cleanup): later rounds wait
  // for search effort of ten times that, four times more after every round in a row that
  // achieved nothing (productive rounds keep their pace: on ncc they eliminate 100k variables
  // each; on cfi-rigid, 16M mostly binary clauses, rounds achieve nothing but cost a second).
  if (eliminate_rounds_ > 0 &&
      stats_.ticks - eliminate_last_ticks_ < (10 * (arena_.size() / 16)) << (2 * eliminate_delay_)) {
    return false;
  }
  // Worth another round while the bound still grows (0, 1, 2, 4, ... --eliminatebound), or if the
  // irredundant formula changed since the last one. (Requiring a change alone meant that on
  // formulas no other pass touched the bound stayed at 0 forever.)
  const uint32_t next_bound = static_cast<uint32_t>(
      std::min<uint64_t>(opts_.eliminatebound, uint64_t{1} << std::min<uint64_t>(eliminate_rounds_ - 1, 20)));
  return eliminate_rounds_ == 0 || next_bound > eliminate_last_bound_ || fixed_ != eliminate_last_fixed_ ||
         irredundant_ + binaries_irredundant_ != eliminate_last_irredundant_;
}

void Solver::touch_clause(const Lit* lits, uint32_t size) {
  for (uint32_t i = 0; i < size; ++i) touched_[var_of(lits[i])] = 1;
}

void Solver::push_extension(Lit witness, const Lit* lits, uint32_t size) {
  extension_.push_back(witness);
  extension_.append(lits, size);
  extension_.push_back(kNoLit);
}

void Solver::disconnect_long_watches() {
  for (std::vector<Watch>& ws : watches_) {
    size_t j = 0;
    for (size_t i = 0; i < ws.size(); ++i) {
      if (ws[i].binary()) ws[j++] = ws[i];
    }
    ws.resize(j);
  }
  watched_clauses_ = 0;
}

void Solver::reconnect_long_watches() {
  // Watch two non-false literals where possible (a clause with fewer is unit or falsified at the
  // root and is found by the re-propagation below).
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    Lit* lits = c.lits();
    for (uint32_t w = 0; w < 2; ++w) {
      if (vals_[lits[w]] >= 0) continue;
      for (uint32_t k = 2; k < c.size; ++k) {
        if (vals_[lits[k]] >= 0) {
          std::swap(lits[w], lits[k]);
          break;
        }
      }
    }
    c.pos = 2;
  }
  watched_clauses_ = 0;
  connect_pending();
  propagated_ = 0;  // re-propagate the whole root trail over the new watches
}

// Removes one binary watch (owner -> other) with the given redundancy. The flag must match: a
// learned binary can duplicate an original one, and removing the wrong copy leaves an irredundant
// clause behind (found as a clause on an eliminated variable, then a wrong SAT model).
void Solver::remove_binary_watch(Lit owner, Lit other, bool redundant) {
  std::vector<Watch>& ws = watches_[owner];
  for (size_t i = 0; i < ws.size(); ++i) {
    if (ws[i].binary() && ws[i].blit == other && ws[i].redundant_binary() == redundant) {
      ws[i] = ws.back();
      ws.pop_back();
      return;
    }
  }
}

void Solver::delete_binary(Lit a, Lit b) {
  remove_binary_watch(a, b, false);
  remove_binary_watch(b, a, false);
  if (proof_) {
    const Lit bin[2] = {a, b};
    proof_->del(bin, 2);
  }
  touched_[var_of(a)] = touched_[var_of(b)] = 1;
}

void Solver::delete_irredundant(uint32_t ref) {
  Clause& c = clause(ref);
  delete_clause_proof(c);
  touch_clause(c.lits(), c.size);
  c.garbage = 1;
  note_garbage(c);
  garbage_words_ += kHeaderWords + c.size;
  if (c.redundant) {
    --redundant_;
  } else {
    --irredundant_;
  }
}

// Live irredundant long clauses containing l (drops garbage references from the list).
void Solver::gather_occurrences(Lit l, std::vector<uint32_t>& out, uint64_t& budget) {
  out.clear();
  uint32_t* os = occs_.begin(l);
  const uint32_t n = occs_.size(l);
  uint32_t j = 0;
  for (uint32_t i = 0; i < n; ++i) {
    const uint32_t ref = os[i];
    if (clause(ref).garbage) continue;
    os[j++] = ref;
    out.push_back(ref);
  }
  occs_.truncate(l, j);
  budget += j / 4 + 1;
}

void Solver::eliminate() {
  const PassTimer pass_timer(*this, kPassEliminate);
  ++stats_.eliminations;
  if (!backtrack_to_root()) return;
  // Root level, fully propagated.
  if (fixed_ > last_simplify_fixed_) simplify_root();
  uint64_t budget = 0;
  const uint64_t search_ticks = stats_.ticks - eliminate_last_ticks_;
  uint64_t limit = static_cast<uint64_t>(static_cast<double>(search_ticks) * opts_.eliminateeffort / 1000.0);
  // The first round (preprocessing) gets an effort floor proportional to the formula size.
  limit = std::max<uint64_t>(limit, eliminate_rounds_ == 0 ? 1'000'000 + arena_.size() / 2 : 100'000);
  const uint32_t bound = eliminate_rounds_ == 0
                             ? 0
                             : static_cast<uint32_t>(std::min<uint64_t>(
                                   opts_.eliminatebound, uint64_t{1} << std::min<uint64_t>(eliminate_rounds_ - 1, 20)));
  // A raised bound retries every variable; otherwise only those whose clauses changed.
  const bool all_candidates = eliminate_rounds_ == 0 || bound > eliminate_last_bound_;
  eliminate_last_bound_ = bound;
  ++eliminate_rounds_;

  const double t0 = seconds();
  auto scan = [&](const char* where) {
    if (!opts_.invariants) return;
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (!eliminated_[var_of(c.lits()[k])]) continue;
        std::fprintf(stderr, "c DEBUG round %llu after %s: clause %u has inactive %d:",
                     static_cast<unsigned long long>(eliminate_rounds_), where, ref, to_dimacs(c.lits()[k]));
        for (uint32_t m = 0; m < c.size; ++m) std::fprintf(stderr, " %d", to_dimacs(c.lits()[m]));
        std::fprintf(stderr, "\n");
        std::abort();
      }
    }
  };
  scan("start");
  // Equivalences from random simulation (first round only: elimination removes gate definitions).
  if (opts_.simeq && eliminate_rounds_ == 1) {
    simulate_equivalences();
    if (inconsistent_) return;
  }
  disconnect_long_watches();
  const uint32_t inactive_before = inactive_;
  if (opts_.substitute) substitute();
  scan("substitute");
  // Congruence closure: equal AND gates give equivalences, substitution merges them and renames
  // gate inputs, which can make more gates equal.
  // Rounds that find nothing double the number of rounds skipped before the next attempt.
  if (opts_.congruence && !inconsistent_) {
    if (congruence_skip_) {
      --congruence_skip_;
    } else {
      bool found = false;
      const double tc = seconds();
      const uint64_t congruent_before = stats_.congruent;
      int iterations = 0;
      for (int iter = 0; iter < 16 && !inconsistent_; ++iter) {
        ++iterations;
        const uint32_t n = congruence(budget);
        if (opts_.verbose >= 3) std::printf("c   congruence iteration %d: %u congruent\n", iter, n);
        if (!n) break;
        found = true;
        substitute();
        scan("congruence+substitute");
      }
      if (opts_.verbose >= 2) {
        std::printf("c [%.2f s] congruence: %d iterations, %llu congruent, %.2f s\n", seconds(), iterations,
                    static_cast<unsigned long long>(stats_.congruent - congruent_before), seconds() - tc);
      }
      congruence_delay_ = found ? 0 : std::min<uint32_t>(2 * congruence_delay_ + 1, 64);
      congruence_skip_ = congruence_delay_;
    }
  }
  if (inconsistent_) {
    reconnect_long_watches();
    return;
  }
  // Occurrence lists with exact sizes (a counting pass first: no reallocation churn).
  {
    std::vector<uint32_t> count(2 * size_t{num_vars_}, 0);
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) ++count[c.lits()[k]];
    }
    occs_.init(count);
  }
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    for (uint32_t k = 0; k < c.size; ++k) occs_.push(c.lits()[k], ref);
  }
  budget += arena_.size() / 8;
  const double t1 = seconds();

  const uint64_t subsumed_before = stats_.subsumed, strengthened_before = stats_.strengthened;
  if (opts_.subsume && !inconsistent_) subsume_round(budget);
  scan("subsume");
  // BVA before elimination (as SBVA and Kissat's factor in preprocessing): elimination first
  // removes much of the structure (binary clauses of at-most-one encodings) BVA would factor.
  const bool bva_round_now = opts_.bva && !inconsistent_ && (eliminate_rounds_ == 1 || opts_.bvaevery);
  if (bva_round_now && opts_.bvafirst) {
    bva_run(budget);
    scan("bva");
  }
  const double t2 = seconds();

  // Candidates: active, unassigned (touched) variables, fewest occurrences first.
  std::vector<std::pair<uint64_t, Var>> cands;
  for (Var v = 0; v < num_vars_; ++v) {
    if (eliminated_[v] || vals_[make_lit(v, false)] != 0) continue;
    if (!all_candidates && !touched_[v]) continue;
    if (opts_.bvaprotect && v < bva_added_.size() && bva_added_[v]) continue;  // would undo BVA
    const Lit p = make_lit(v, false), n = make_lit(v, true);
    uint64_t np = occs_.size(p), nn = occs_.size(n);
    for (const Watch& w : watches_[p]) np += w.binary() && !w.redundant_binary();
    for (const Watch& w : watches_[n]) nn += w.binary() && !w.redundant_binary();
    if (np > static_cast<uint64_t>(opts_.eliminateocclim) || nn > static_cast<uint64_t>(opts_.eliminateocclim)) continue;
    cands.emplace_back(np * nn, v);
  }
  std::sort(cands.begin(), cands.end());
  budget += cands.size();

  const uint32_t eliminated_before = inactive_;
  const double t3 = seconds();
  // Elimination has its own budget, whatever subsumption and substitution used.
  // A variable's mark is cleared when it is tried; candidates the budget did not reach stay
  // marked (also after a round with all candidates), so later rounds get to them.
  const uint64_t elim_start = budget;
  size_t tried = 0;
  for (; tried < cands.size(); ++tried) {
    if (inconsistent_ || budget - elim_start > limit) break;
    touched_[cands[tried].second] = 0;
    try_eliminate(cands[tried].second, bound, budget);
  }
  for (size_t i = tried; i < cands.size(); ++i) touched_[cands[i].second] = 1;
  // BVA once, in the first round (as SBVA preprocessing): repeated rounds keep adding variables.
  if (bva_round_now && !opts_.bvafirst && !inconsistent_) bva_run(budget);
  const double t4 = seconds();

  // Learned clauses on eliminated variables are dropped (they would constrain them again).
  if (inactive_ != inactive_before) {
    for (const uint32_t ref : clauses_) {
      Clause& c = clause(ref);
      if (c.garbage || !c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (eliminated_[var_of(c.lits()[k])]) {
          delete_clause_proof(c);
          c.garbage = 1;
          note_garbage(c);
          garbage_words_ += kHeaderWords + c.size;
          --redundant_;
          break;
        }
      }
    }
    for (Lit l = 0; l < 2 * num_vars_; ++l) {
      if (!eliminated_[var_of(l)]) continue;
      // Remaining binary watches of an eliminated variable are redundant (learned) binaries.
      for (const Watch& w : watches_[l]) {
        if (!w.binary()) continue;
        if (!eliminated_[var_of(w.blit)] || l < w.blit) {
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
        if (!eliminated_[var_of(w.blit)]) remove_binary_watch(w.blit, l, w.redundant_binary());
      }
      watches_[l].clear();
      watches_[l].shrink_to_fit();
    }
    drop_inactive_decisions();
  }

  occs_.clear();
  collect_garbage();
  reconnect_long_watches();
  eliminate_last_ticks_ = stats_.ticks;
  eliminate_last_fixed_ = fixed_;
  eliminate_last_irredundant_ = irredundant_ + binaries_irredundant_;
  eliminate_limit_ = stats_.conflicts + static_cast<uint64_t>(opts_.eliminateint) * eliminate_rounds_;
  const bool productive = inactive_ != inactive_before || stats_.subsumed != subsumed_before ||
                          stats_.strengthened != strengthened_before;
  eliminate_delay_ = productive ? 0 : std::min<uint32_t>(eliminate_delay_ + 1, 8);
  if (opts_.verbose >= 1) {
    std::printf("c [%.2f s] elimination round %llu: bound %u, substituted %u, eliminated %u (inactive %u), subsumed %llu, "
                "strengthened %llu, %llu irredundant clauses left, peak RSS %.0f MB\n",
                seconds(), static_cast<unsigned long long>(eliminate_rounds_), bound, eliminated_before - inactive_before,
                inactive_ - eliminated_before, inactive_, static_cast<unsigned long long>(stats_.subsumed - subsumed_before),
                static_cast<unsigned long long>(stats_.strengthened - strengthened_before),
                static_cast<unsigned long long>(irredundant_ + binaries_irredundant_), peak_rss_mb());
    if (opts_.verbose >= 2) {
      std::printf("c   times: occs %.2f, subsume %.2f, candidates %.2f, eliminate %.2f, cleanup %.2f s; "
                  "%zu candidates, budget %llu of %llu\n",
                  t1 - t0, t2 - t1, t3 - t2, t4 - t3, seconds() - t4, cands.size(),
                  static_cast<unsigned long long>(budget), static_cast<unsigned long long>(limit));
    }
    std::fflush(stdout);
  }
}

namespace {

// Sorted variables and negative-literal parity of a clause occurrence.
struct VarSet {
  Var vars[5];
  uint32_t n = 0;
  uint32_t neg_parity = 0;
};

}  // namespace

// Returns the size of the XOR found (0 if none). Clauses with skip[s][j] set are ignored; with
// gate == nullptr the XOR is only detected, not marked.
uint32_t Solver::find_xor_gate(Var v, std::vector<OccClause>* side, std::vector<uint8_t>* gate,
                               const std::vector<uint8_t>* skip, uint64_t& budget) {
  auto varset = [&](const OccClause& oc, Lit pivot, VarSet& out) -> bool {
    if (oc.ref == kNoReason) return false;
    const Clause& c = clause(oc.ref);
    if (c.size < 3 || c.size > 5) return false;
    out.n = c.size;
    out.neg_parity = 0;
    for (uint32_t k = 0; k < c.size; ++k) {
      out.vars[k] = var_of(c.lits()[k]);
      out.neg_parity ^= is_negative(c.lits()[k]) ? 1u : 0u;
    }
    small_sort(out.vars, out.n);
    for (uint32_t k = 1; k < out.n; ++k) {
      if (out.vars[k] == out.vars[k - 1]) return false;
    }
    (void)pivot;
    return true;
  };
  const Lit pivots[2] = {make_lit(v, false), make_lit(v, true)};
  size_t tries = 0;
  for (size_t i = 0; i < side[0].size() && tries < 8; ++i) {
    VarSet base;
    if (skip && skip[0][i]) continue;
    if (!varset(side[0][i], pivots[0], base)) continue;
    ++tries;
    const uint32_t need = 1u << (base.n - 1);
    // Collect matching clauses from both sides (distinct sign patterns).
    std::vector<std::pair<int, size_t>> members;
    std::vector<uint32_t> patterns;
    for (int s = 0; s < 2; ++s) {
      for (size_t j = 0; j < side[s].size(); ++j) {
        VarSet other;
        if (skip && skip[s][j]) continue;
        if (!varset(side[s][j], pivots[s], other) || other.n != base.n || other.neg_parity != base.neg_parity) continue;
        if (!std::equal(base.vars, base.vars + base.n, other.vars)) continue;
        const Clause& c = clause(side[s][j].ref);
        uint32_t pattern = 0;
        for (uint32_t k = 0; k < c.size; ++k) {
          if (!is_negative(c.lits()[k])) continue;
          const Var x = var_of(c.lits()[k]);
          pattern |= 1u << static_cast<uint32_t>(std::lower_bound(base.vars, base.vars + base.n, x) - base.vars);
        }
        if (std::find(patterns.begin(), patterns.end(), pattern) != patterns.end()) continue;
        patterns.push_back(pattern);
        members.emplace_back(s, j);
      }
      budget += side[s].size() / 4 + 1;
    }
    if (patterns.size() != need) continue;
    if (gate) {
      for (const auto& m : members) gate[m.first][m.second] = 1;
      ++stats_.xor_gates;
    }
    return base.n;
  }
  return 0;
}

bool Solver::find_ite_gate(Var v, std::vector<OccClause>* side, std::vector<uint8_t>* gate, uint64_t& budget) {
  // For s = polarity of v in the "then/else" clauses: (P' -c t), (P' c e) in side[s] with
  // P' = pivots[s], and (Q -c -t), (Q c -e) in side[1-s].
  const Lit pivots[2] = {make_lit(v, false), make_lit(v, true)};
  auto ternary = [&](const OccClause& oc, Lit pivot, Lit out[2]) -> bool {
    if (oc.ref == kNoReason) return false;
    const Clause& c = clause(oc.ref);
    if (c.size != 3) return false;
    int k = 0;
    for (uint32_t m = 0; m < 3; ++m) {
      if (c.lits()[m] != pivot) {
        if (k == 2) return false;
        out[k++] = c.lits()[m];
      }
    }
    return k == 2;
  };
  auto find = [&](int s, Lit a, Lit b) -> size_t {
    Lit o[2];
    for (size_t j = 0; j < side[s].size(); ++j) {
      if (!ternary(side[s][j], pivots[s], o)) continue;
      if ((o[0] == a && o[1] == b) || (o[0] == b && o[1] == a)) return j;
    }
    return SIZE_MAX;
  };
  for (int s = 0; s < 2; ++s) {
    const int o = 1 - s;
    const size_t n = std::min<size_t>(side[s].size(), 16);
    budget += n * n / 4 + 1;
    Lit x[2], y[2];
    for (size_t i = 0; i < n; ++i) {
      if (!ternary(side[s][i], pivots[s], x)) continue;
      for (size_t j = i + 1; j < n; ++j) {
        if (!ternary(side[s][j], pivots[s], y)) continue;
        // Find a complementary pair: x = {-c, t}, y = {c, e}.
        for (int a = 0; a < 2; ++a) {
          for (int b = 0; b < 2; ++b) {
            if (x[a] != negate(y[b])) continue;
            const Lit nc = x[a], t = x[1 - a], c = y[b], e = y[1 - b];
            if (var_of(t) == var_of(e)) continue;
            const size_t k1 = find(o, nc, negate(t));
            if (k1 == SIZE_MAX) continue;
            const size_t k2 = find(o, c, negate(e));
            if (k2 == SIZE_MAX) continue;
            gate[s][i] = gate[s][j] = 1;
            gate[o][k1] = gate[o][k2] = 1;
            ++stats_.ite_gates;
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool Solver::try_eliminate(Var v, uint32_t bound, uint64_t& budget) {
  if (eliminated_[v] || vals_[make_lit(v, false)] != 0) return false;
  const Lit pivots[2] = {make_lit(v, false), make_lit(v, true)};
  std::vector<OccClause>* side = elim_side_;
  std::vector<uint32_t>& refs = elim_refs_;
  side[0].clear();
  side[1].clear();
  for (int s = 0; s < 2; ++s) {
    const Lit p = pivots[s];
    gather_occurrences(p, refs, budget);
    for (const uint32_t ref : refs) {
      // Clauses satisfied at the root (by a unit found in this round) are simply removed.
      const Clause& c = clause(ref);
      bool satisfied = false;
      for (uint32_t k = 0; k < c.size; ++k) satisfied = satisfied || vals_[c.lits()[k]] > 0;
      if (satisfied) {
        delete_irredundant(ref);
        continue;
      }
      side[s].push_back(OccClause{ref, kNoLit});
    }
    for (const Watch& w : watches_[p]) {
      if (!w.binary() || w.redundant_binary()) continue;
      side[s].push_back(OccClause{kNoReason, w.blit});
    }
    budget += watches_[p].size() / 8 + 1;
  }
  const size_t np = side[0].size(), nn = side[1].size();
  if (np > static_cast<size_t>(opts_.eliminateocclim) || nn > static_cast<size_t>(opts_.eliminateocclim)) return false;

  // Resolvent of a positive and a negative occurrence, root-simplified. Returns false if it is a
  // tautology or satisfied; marks_ is clean on return.
  auto resolve = [&](const OccClause& a, const OccClause& b, std::vector<Lit>& out) -> bool {
    out.clear();
    bool keep = true;
    auto add_side = [&](const OccClause& oc, Lit pivot, bool second) {
      const Lit* lits;
      uint32_t size;
      Lit tmp[2];
      if (oc.ref == kNoReason) {
        tmp[0] = pivot;
        tmp[1] = oc.other;
        lits = tmp;
        size = 2;
      } else {
        const Clause& c = clause(oc.ref);
        lits = c.lits();
        size = c.size;
      }
      budget += size / 8 + 1;
      for (uint32_t k = 0; k < size && keep; ++k) {
        const Lit l = lits[k];
        if (var_of(l) == v) continue;
        const int8_t val = vals_[l];
        if (val > 0) {
          keep = false;
        } else if (val == 0) {
          if (marks_[negate(l)]) {
            keep = false;  // tautology
          } else if (!marks_[l]) {
            if (!second) marks_[l] = 1;
            out.push_back(l);
          }
        }
      }
    };
    add_side(a, pivots[0], false);
    if (keep) add_side(b, pivots[1], true);
    for (uint32_t k = 0; k < out.size(); ++k) marks_[out[k]] = 0;
    // (Only first-side literals were marked; clearing all of out is harmless.)
    return keep;
  };

  // Gate detection (Een & Biere 2005): if v is defined by an AND gate (an equivalence is the
  // one-input case), P = AND(l1..lk) with binaries (-P v li) and the base clause
  // (P v -l1 v ... v -lk), only gate x non-gate resolvents are needed: gate x gate ones are
  // tautologies and non-gate x non-gate ones are implied by the others.
  std::vector<uint8_t>* gate = elim_gate_;
  gate[0].assign(np, 0);
  gate[1].assign(nn, 0);
  bool gated = false;
  if (opts_.eliminategates) {
    for (int s = 0; s < 2 && !gated; ++s) {
      const int o = 1 - s;
      for (const OccClause& oc : side[o]) {
        if (oc.ref == kNoReason && vals_[oc.other] == 0) marks_[oc.other] = 1;
      }
      for (size_t i = 0; i < side[s].size() && !gated; ++i) {
        const OccClause& oc = side[s][i];
        bool base = true;
        if (oc.ref == kNoReason) {
          base = marks_[negate(oc.other)] != 0;
        } else {
          const Clause& c = clause(oc.ref);
          budget += c.size / 8 + 1;
          for (uint32_t k = 0; k < c.size && base; ++k) {
            const Lit l = c.lits()[k];
            if (var_of(l) != v && !marks_[negate(l)]) base = false;
          }
        }
        if (!base) continue;
        gated = true;
        gate[s][i] = 1;
        // The gate binaries are those (-P v l) with -l in the base clause.
        if (oc.ref == kNoReason) {
          marks_[negate(oc.other)] = 2;
        } else {
          const Clause& c = clause(oc.ref);
          for (uint32_t k = 0; k < c.size; ++k) {
            if (var_of(c.lits()[k]) != v) marks_[negate(c.lits()[k])] = 2;
          }
        }
        for (size_t j = 0; j < side[o].size(); ++j) {
          if (side[o][j].ref == kNoReason && marks_[side[o][j].other] == 2) gate[o][j] = 1;
        }
      }
      for (const OccClause& oc : side[o]) {
        if (oc.ref == kNoReason) marks_[oc.other] = 0;
      }
    }
    // XOR definition: all 2^(n-1) clauses over the variable set of a clause (3 <= n <= 5) with
    // the same parity of negative literals; every gate x gate resolvent is a tautology.
    // Eliminating a variable that occurs in two XORs of sizes k and m merges them into one XOR of
    // up to k + m - 2 variables (2^(k+m-3) clauses). Even at an unchanged clause count, CDCL
    // does much worse on the longer XORs (parity formulas need many times the conflicts), so
    // such merges are limited by --eliminatexorlim.
    if (!gated) {
      const uint32_t k = find_xor_gate(v, side, gate, nullptr, budget);
      if (k) {
        gated = true;
        const uint32_t m = opts_.eliminatexorlim ? find_xor_gate(v, side, nullptr, gate, budget) : 0;
        if (m && k + m - 2 > static_cast<uint32_t>(opts_.eliminatexorlim)) {
          ++stats_.xor_merges_skipped;
          return false;
        }
      }
    }
    // ITE definition v = ITE(c, t, e): (-v -c t), (-v c e), (v -c -t), (v c -e) (either polarity).
    if (!gated) gated = find_ite_gate(v, side, gate, budget);
    if (gated) ++stats_.gates;
  }
  // Semantic definition (an unsat core of the clauses of v without v): its gate x gate
  // resolvents are not tautologies and must be kept; non-gate x non-gate ones are implied.
  bool semantic = false;
  if (!gated && opts_.definitions) semantic = gated = find_definition(v, side, gate, budget);
  auto skip_pair = [&](size_t i, size_t j) {
    if (!gated) return false;
    return semantic ? !gate[0][i] && !gate[1][j] : gate[0][i] == gate[1][j];
  };

  // Count the resolvents first (abort above the bound or on a too long resolvent).
  const uint64_t limit = np + nn + bound;
  uint64_t count = 0;
  std::vector<Lit>& res = elim_res_;
  for (size_t i = 0; i < np; ++i) {
    const OccClause& a = side[0][i];
    for (size_t j = 0; j < nn; ++j) {
      const OccClause& b = side[1][j];
      if (skip_pair(i, j)) continue;
      if (!resolve(a, b, res)) continue;
      if (res.size() > static_cast<size_t>(opts_.eliminateclslim)) return false;
      if (++count > limit) return false;
    }
  }

  // Eliminate: add the resolvents, then save and delete the clauses of v.
  for (size_t i = 0; i < np; ++i) {
    const OccClause& a = side[0][i];
    for (size_t j = 0; j < nn; ++j) {
      const OccClause& b = side[1][j];
      if (skip_pair(i, j)) continue;
      if (!resolve(a, b, res)) continue;
      ++stats_.resolvents;
      if (proof_) proof_->add(res.data(), res.size());
      touch_clause(res.data(), static_cast<uint32_t>(res.size()));
      if (res.empty()) {
        inconsistent_ = true;
        return true;
      }
      if (res.size() == 1) {
        if (vals_[res[0]] == 0) assign(res[0], kNoReason);
        continue;
      }
      if (res.size() == 2) {
        add_binary(res[0], res[1], false);
        continue;
      }
      const uint32_t ref = new_clause(res.data(), static_cast<uint32_t>(res.size()), false, 0, false);
      for (const Lit l : res) occs_.push(l, ref);
    }
  }
  for (int s = 0; s < 2; ++s) {
    for (const OccClause& oc : side[s]) {
      if (oc.ref == kNoReason) {
        const Lit bin[2] = {pivots[s], oc.other};
        push_extension(pivots[s], bin, 2);
        delete_binary(pivots[s], oc.other);
        --binaries_irredundant_;
      } else {
        const Clause& c = clause(oc.ref);
        push_extension(pivots[s], c.lits(), c.size);
        delete_irredundant(oc.ref);
      }
    }
  }
  eliminated_[v] = 1;
  ++inactive_;
  ++stats_.eliminated;
  if (opts_.invariants) {
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (var_of(c.lits()[k]) != v) continue;
        const Lit l = c.lits()[k];
        const bool listed = std::find(occs_.begin(l), occs_.end(l), ref) != occs_.end(l);
        std::fprintf(stderr, "c DEBUG eliminated %d but clause %u (size %u, redundant %u, listed %d, gated %d) has it:",
                     to_dimacs(make_lit(v, false)), ref, c.size, c.redundant, listed, gated);
        for (uint32_t m = 0; m < c.size; ++m) std::fprintf(stderr, " %d", to_dimacs(c.lits()[m]));
        std::fprintf(stderr, "\n");
        std::abort();
      }
    }
  }
  return true;
}

void Solver::extend_model() {
  model_.assign(num_vars_, -1);
  for (Var v = 0; v < num_vars_; ++v) model_[v] = vals_[make_lit(v, false)] > 0 ? 1 : -1;
  size_t i = extension_.size();
  while (i > 0) {
    const size_t end = i - 1;  // the kNoLit terminator
    size_t start = end;
    while (start > 0 && extension_[start - 1] != kNoLit) --start;
    const Lit witness = extension_[start];
    bool satisfied = false;
    for (size_t k = start + 1; k < end && !satisfied; ++k) {
      const Lit l = extension_[k];
      satisfied = model_[var_of(l)] == (is_negative(l) ? -1 : 1);
    }
    if (!satisfied) model_[var_of(witness)] = is_negative(witness) ? -1 : 1;
    i = start;
  }
  model_valid_ = true;
}

// Definition mining (Fleury & Biere 2022): the clauses of v with v removed go to Kitten; if they
// are unsatisfiable, the clauses in the unsat core define v (in the paper's sense) and play the
// role of gate clauses. A one-sided core (v forced) works the same way.
bool Solver::find_definition(Var v, std::vector<OccClause>* side, std::vector<uint8_t>* gate, uint64_t& budget) {
  constexpr size_t kMaxClauses = 64;
  constexpr uint32_t kMaxSize = 32;
  const size_t np = side[0].size(), nn = side[1].size();
  if (np + nn < 2 || np + nn > kMaxClauses) return false;
  if (sweep_local_.size() < num_vars_) sweep_local_.resize(num_vars_, UINT32_MAX);
  std::vector<Var>& vars = sweep_env_;
  vars.clear();
  std::vector<Kitten::KLit>& kc = def_lits_;
  kitten_.clear();
  bool ok = true;
  auto klit = [&](Lit l) -> Kitten::KLit {
    const Var u = var_of(l);
    if (sweep_local_[u] == UINT32_MAX) {
      sweep_local_[u] = static_cast<uint32_t>(vars.size());
      vars.push_back(u);
      kitten_.resize(static_cast<uint32_t>(vars.size()));
    }
    return 2 * sweep_local_[u] + (is_negative(l) ? 1u : 0u);
  };
  for (int s = 0; s < 2 && ok; ++s) {
    for (size_t i = 0; i < side[s].size() && ok; ++i) {
      const OccClause& oc = side[s][i];
      kc.clear();
      if (oc.ref == kNoReason) {
        if (vals_[oc.other] == 0) kc.push_back(klit(oc.other));
        if (vals_[oc.other] > 0) continue;  // satisfied: not part of any definition
      } else {
        const Clause& c = clause(oc.ref);
        if (c.size > kMaxSize) {
          ok = false;
          break;
        }
        budget += c.size / 8 + 1;
        bool sat = false;
        for (uint32_t k = 0; k < c.size; ++k) {
          const Lit l = c.lits()[k];
          if (var_of(l) == v) continue;
          if (vals_[l] > 0) sat = true;
          if (vals_[l] == 0) kc.push_back(klit(l));
        }
        if (sat) continue;
      }
      const uint32_t id = static_cast<uint32_t>(s == 0 ? i : np + i);
      kitten_.add_clause(kc.data(), static_cast<uint32_t>(kc.size()), id);
    }
  }
  bool found = false;
  if (ok) {
    const uint64_t before = kitten_.ticks();
    const int r = kitten_.solve(static_cast<uint64_t>(opts_.definitionticks));
    budget += kitten_.ticks() - before;
    if (r == Kitten::kUnsat && kitten_.inconsistent()) {
      std::vector<uint32_t>& ids = def_core_;
      kitten_.compute_core(ids);
      for (const uint32_t id : ids) {
        if (id < np) {
          gate[0][id] = 1;
        } else {
          gate[1][id - np] = 1;
        }
      }
      found = !ids.empty();
      if (found) ++stats_.definitions;
    }
  }
  for (const Var u : vars) sweep_local_[u] = UINT32_MAX;
  return found;
}

}  // namespace psat
