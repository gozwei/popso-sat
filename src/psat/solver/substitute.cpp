// Equivalent literal substitution: strongly connected components of the binary implication
// graph (binary clause (a v b) gives edges -a -> b and -b -> a) are sets of equivalent literals.
// Every literal is replaced by its component's representative (the literal of the smallest
// variable, which keeps representatives of complementary components complementary), and the
// substituted variables become inactive, with x = r restored by two extension clauses.
//
// Runs inside an elimination round (long watches detached), before the occurrence lists are
// built. A component containing both x and -x makes the formula unsatisfiable; the unit -x is
// derived (RUP through the implication chain x -> ... -> -x) and left to propagation.
//
// DRAT: a rewritten clause C[x := r] is RUP while the binary clauses of the implication chains
// are still present, so all rewritten clauses are added before any old clause is deleted.

#include <algorithm>
#include <array>
#include <cstdio>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

bool Solver::substitute() {
  const PassTimer pass_timer(*this, kPassSubstitute);
  ++substitute_epoch_;
  const size_t nlits = 2 * size_t{num_vars_};
  constexpr uint32_t kUnvisited = UINT32_MAX;
  std::vector<uint32_t> index(nlits, kUnvisited), low(nlits, 0);
  std::vector<uint8_t> on_stack(nlits, 0);
  std::vector<uint32_t> comp(nlits, kUnvisited);
  uint32_t components = 0;
  std::vector<Lit> scc_stack;
  std::vector<std::pair<Lit, uint32_t>> dfs;  // literal, next watch position in watches_[-lit]
  std::vector<Lit> repr(nlits);
  for (size_t l = 0; l < nlits; ++l) repr[l] = static_cast<Lit>(l);
  uint32_t counter = 0;
  uint64_t equivalences = 0;
  Lit failed = kNoLit;

  auto active = [&](Lit l) { return vals_[l] == 0 && !eliminated_[var_of(l)]; };
  for (Lit root = 0; root < nlits && failed == kNoLit; ++root) {
    if (index[root] != kUnvisited || !active(root)) continue;
    dfs.emplace_back(root, 0);
    index[root] = low[root] = counter++;
    scc_stack.push_back(root);
    on_stack[root] = 1;
    while (!dfs.empty() && failed == kNoLit) {
      const Lit u = dfs.back().first;
      const WatchList ws = watches_[negate(u)];
      uint32_t& pos = dfs.back().second;
      bool descended = false;
      while (pos < ws.size()) {
        const Watch w = ws[pos++];
        if (!w.binary()) continue;
        const Lit v = w.blit;
        if (!active(v)) continue;
        if (index[v] == kUnvisited) {
          index[v] = low[v] = counter++;
          scc_stack.push_back(v);
          on_stack[v] = 1;
          dfs.emplace_back(v, 0);
          descended = true;
          break;
        }
        if (on_stack[v]) low[u] = std::min(low[u], index[v]);
      }
      if (descended) continue;
      // u is finished: pop its component; representative = literal with the smallest variable.
      if (low[u] == index[u]) {
        size_t first = scc_stack.size();
        Lit best = u;
        do {
          --first;
          if (var_of(scc_stack[first]) < var_of(best)) best = scc_stack[first];
        } while (scc_stack[first] != u);
        const uint32_t id = components++;
        for (size_t i = first; i < scc_stack.size(); ++i) {
          on_stack[scc_stack[i]] = 0;
          comp[scc_stack[i]] = id;
          repr[scc_stack[i]] = best;
        }
        for (size_t i = first; i < scc_stack.size() && failed == kNoLit; ++i) {
          if (comp[negate(scc_stack[i])] == id) failed = scc_stack[i];  // x and -x equivalent
        }
        scc_stack.resize(first);
      }
      dfs.pop_back();
      if (!dfs.empty()) {
        const Lit parent = dfs.back().first;
        low[parent] = std::min(low[parent], low[u]);
      }
    }
  }
  if (failed != kNoLit) {
    // x and -x are equivalent: -x holds (assuming x propagates -x), then the empty clause follows.
    const Lit unit = negate(failed);
    if (proof_) proof_->add_unit(unit);
    if (vals_[unit] == 0) assign_unit_in_proof(unit);
    scc_stack.clear();
    return true;
  }

  // Representatives of complementary components must be complementary; components are found in
  // pairs (the graph is symmetric under negation), and the smallest-variable choice makes them so.
  for (Var v = 0; v < num_vars_; ++v) {
    const Lit p = make_lit(v, false);
    if (!active(p)) continue;
    if (repr[p] != p) {
      if (repr[negate(p)] != negate(repr[p])) return false;  // inconsistent (should not happen): skip
      ++equivalences;
    }
  }
  if (!equivalences) return false;

  // Rewrite long clauses (in place: long watches are detached). The proof deletes each old clause
  // right after its rewritten copy (RUP from it and the equivalence binaries, which stay until the
  // end): the checker's formula never holds both versions of every clause at once (on
  // linked_list_swap_contents 11M rewritten clauses beside the 15M input clauses).
  std::vector<Lit> tmp;
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (c.garbage) continue;
    Lit* lits = c.lits();
    bool changed = false;
    for (uint32_t k = 0; k < c.size && !changed; ++k) changed = repr[lits[k]] != lits[k];
    if (!changed) continue;
    tmp.clear();
    bool taut = false;
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit r = repr[lits[k]];
      if (vals_[r] > 0) {
        taut = true;
        break;
      }
      if (vals_[r] < 0) continue;
      if (marks_[negate(r)]) {
        taut = true;
        break;
      }
      if (!marks_[r]) {
        marks_[r] = 1;
        tmp.push_back(r);
      }
    }
    for (const Lit r : tmp) marks_[r] = 0;
    if (!c.redundant) touch_clause(lits, c.size);
    if (taut) {
      if (proof_) proof_->del(lits, c.size);
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
    if (proof_) {
      proof_->add(tmp.data(), tmp.size());
      proof_->del(lits, c.size);
    }
    if (tmp.size() <= 2) {
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      if (tmp.size() == 2) {
        add_binary(tmp[0], tmp[1], c.redundant);
      } else if (tmp.size() == 1) {
        if (vals_[tmp[0]] == 0) assign_unit_in_proof(tmp[0]);
      } else {
        inconsistent_ = true;
        if (proof_) proof_->add_empty();
        return true;
      }
      continue;
    }
    garbage_words_ += c.size - static_cast<uint32_t>(tmp.size());
    shrunk_words_ += c.size - static_cast<uint32_t>(tmp.size());
    std::copy(tmp.begin(), tmp.end(), lits);
    c.size = static_cast<uint32_t>(tmp.size());
    if (c.glue > c.size - 1) c.glue = c.size - 1;
  }

  // Binary clauses with a substituted literal: collect, remove, re-add rewritten.
  struct Bin {
    Lit a, b;
    bool redundant;
  };
  std::vector<Bin> bins;
  for (Lit l = 0; l < nlits; ++l) {
    for (const Watch& w : watches_[l]) {
      if (!w.binary() || l > w.blit) continue;
      if (repr[l] == l && repr[w.blit] == w.blit) continue;
      bins.push_back(Bin{l, w.blit, w.redundant_binary()});
    }
  }
  // Rewritten binaries are re-added whatever the root values of their literals: the root trail is
  // propagated again after the round, which handles false or true literals (a binary dropped here
  // because one literal is false would lose the implied unit).
  for (const Bin& b : bins) {
    const Lit ra = repr[b.a], rb = repr[b.b];
    if (ra == negate(rb)) continue;  // tautology
    if (ra == rb) {
      if (proof_) proof_->add_unit(ra);
      if (vals_[ra] == 0) {
        assign_unit_in_proof(ra);
      } else if (vals_[ra] < 0) {
        inconsistent_ = true;
        if (proof_) proof_->add_empty();
      }
      continue;
    }
    if (proof_) {
      const Lit nb[2] = {ra, rb};
      proof_->add(nb, 2);
    }
  }
  // Every binary watch of a substituted literal is in `bins`, and the rewritten binaries go to
  // representatives only, so these lists end up without binary watches whatever the order of
  // the removals: with long watches detached (always, in practice) they are emptied at the end
  // instead of one linear search per watch (quadratic on long lists). The representatives'
  // lists go through the same removals and additions in the same order as before.
  bool clear_substituted = true;
  for (Lit l = 0; l < nlits && clear_substituted; ++l) {
    if (repr[l] == l) continue;
    for (const Watch& w : watches_[l]) {
      if (!w.binary()) {
        clear_substituted = false;
        break;
      }
    }
  }
  for (const Bin& b : bins) {
    if (!clear_substituted || repr[b.a] == b.a) remove_binary_watch(b.a, b.b, b.redundant);
    if (!clear_substituted || repr[b.b] == b.b) remove_binary_watch(b.b, b.a, b.redundant);
    if (b.redundant) {
      --binaries_redundant_;
    } else {
      --binaries_irredundant_;
    }
    touch_var(var_of(b.a));
    touch_var(var_of(b.b));
    const Lit ra = repr[b.a], rb = repr[b.b];
    if (ra == negate(rb) || ra == rb) continue;
    add_binary(ra, rb, b.redundant);
  }
  if (clear_substituted) {
    for (Lit l = 0; l < nlits; ++l) {
      if (repr[l] != l) watches_[l].clear();
    }
  }
  // Now the old binary clauses can go (the equivalences among them).
  if (proof_) {
    for (const Bin& b : bins) {
      const Lit ob[2] = {b.a, b.b};
      proof_->del(ob, 2);
    }
  }
  // Substituted variables become inactive; x = r is restored from the extension stack.
  for (Var v = 0; v < num_vars_; ++v) {
    const Lit p = make_lit(v, false);
    if (!active(p) || repr[p] == p) continue;
    const Lit r = repr[p];
    const Lit c1[2] = {p, negate(r)};
    const Lit c2[2] = {negate(p), r};
    push_extension(p, c1, 2);
    push_extension(negate(p), c2, 2);
    eliminated_[v] = 1;
    ++inactive_;
    ++stats_.substituted;
  }
  // Rewritten binaries often coincide with existing ones (the two copies of a merged gate).
  if (opts_.dedup && !bins.empty()) dedup_binaries();
  return true;
}

// --binpairunits: binary clauses (a b) and (a -b) imply the unit a (RUP: -a propagates b and -b).
// Root level, fully propagated; a linear pass over the binary watches, then the units are assigned
// and propagated. With --binpairunits=2 the binary clauses include the resolvents (a b) of ternary
// pairs (a b c) (a b -c) and the clauses with exactly two unassigned literals; a pass that finds
// units adds the resolvents as binary clauses. Elimination makes such pairs, and so do adder circuits with constant
// inputs once units are propagated: sum_of_three_cubes_906 has 85k binary pairs after root
// propagation, which fix 87k more variables, then 993 more with the ternary pairs, which fix 82k
// more and turn as many XOR gates into equivalences. Returns false if the formula became
// inconsistent.
bool Solver::binary_pair_units() {
  // With the ternary pairs: again while a pass finds units (their propagation shortens clauses
  // into new ternary pairs; at most 4 passes).
  for (int pass = 0; pass < (opts_.binpairunits >= 2 ? 4 : 1); ++pass) {
    const uint64_t before = stats_.binpair_units;
    if (!binary_pair_units_pass()) return false;
    if (stats_.binpair_units == before) break;
  }
  return true;
}

bool Solver::binary_pair_units_pass() {
  const size_t nlits = 2 * size_t{num_vars_};
  // Resolvents of ternary pairs, as lists per literal (CSR): (x y) is under x and under y.
  std::vector<uint32_t> tstart;
  std::vector<Lit> tother;
  // Ternary-pair resolvents, and clauses with exactly two unassigned literals (the others false).
  std::vector<std::pair<Lit, Lit>> resolvents, shortened;
  if (opts_.binpairunits >= 2) {
    const auto mix = [](uint64_t x) {
      x ^= x >> 33;
      x *= 0xff51afd7ed558ccdULL;
      x ^= x >> 33;
      x *= 0xc4ceb9fe1a85ec53ULL;
      x ^= x >> 33;
      return x;
    };
    struct Tern {
      uint64_t key;
      std::array<Lit, 3> lits;  // by variable
    };
    std::vector<Tern> terns;
    // Clauses with exactly 3 unassigned literals (the others false at the root; a resolvent of
    // two of them is RUP the same way). Those with 2 are binary clauses for the pairs.
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant || c.size > 8) continue;
      std::array<Lit, 3> t{};
      uint32_t n = 0;
      bool sat = false;
      for (uint32_t k = 0; k < c.size && !sat; ++k) {
        const Lit l = c.lits()[k];
        if (vals_[l] > 0) sat = true;
        if (vals_[l] != 0) continue;
        if (n < 3) t[n] = l;
        ++n;
      }
      if (sat || n < 2 || n > 3) continue;
      if (n == 2) {
        if (c.size > 2) shortened.emplace_back(t[0], t[1]);
        continue;
      }
      std::sort(t.begin(), t.end(), [](Lit a, Lit b) { return var_of(a) < var_of(b); });
      terns.push_back(Tern{mix(var_of(t[0]) + 1) + mix(uint64_t{var_of(t[1])} << 21 | 1) + mix(uint64_t{var_of(t[2])} << 42 | 2), t});
    }
    std::sort(terns.begin(), terns.end(), [](const Tern& a, const Tern& b) {
      if (a.key != b.key) return a.key < b.key;
      return a.lits < b.lits;
    });
    for (size_t a = 0; a < terns.size();) {
      size_t b = a + 1;
      while (b < terns.size() && terns[b].key == terns[a].key) ++b;
      for (size_t i = a; i < b; ++i) {
        for (size_t j = i + 1; j < b; ++j) {
          const auto& x = terns[i].lits;
          const auto& y = terns[j].lits;
          int diff = -1, ndiff = 0;
          bool same_vars = true;
          for (int k = 0; k < 3; ++k) {
            if (var_of(x[k]) != var_of(y[k])) same_vars = false;
            if (x[k] != y[k]) {
              diff = k;
              ++ndiff;
            }
          }
          if (!same_vars || ndiff != 1) continue;
          const Lit p = x[diff == 0 ? 1 : 0], q = x[diff == 2 ? 1 : 2];
          resolvents.emplace_back(p, q);
        }
      }
      a = b;
    }
    tstart.assign(nlits + 1, 0);
    for (const auto* list : {&resolvents, &shortened}) {
      for (const auto& [p, q] : *list) {
        ++tstart[p + 1];
        ++tstart[q + 1];
      }
    }
    for (size_t l = 0; l < nlits; ++l) tstart[l + 1] += tstart[l];
    tother.resize(tstart[nlits]);
    std::vector<uint32_t> fill(tstart.begin(), tstart.end() - 1);
    for (const auto* list : {&resolvents, &shortened}) {
      for (const auto& [p, q] : *list) {
        tother[fill[p]++] = q;
        tother[fill[q]++] = p;
      }
    }
  }
  // seen[x]: 1 a binary clause (a x), 2 only a ternary-pair resolvent (a x).
  std::vector<uint8_t> seen(nlits, 0);
  struct Found {
    Lit unit, b;           // (unit b) and (unit -b)
    uint8_t sb, snb;       // their sources (1 binary clause, 2 resolvent)
  };
  std::vector<Found> units;
  for (Lit a = 0; a < nlits; ++a) {
    if (vals_[a] != 0 || eliminated_[var_of(a)]) continue;
    const ConstWatchList ws = std::as_const(watches_)[a];
    bool found = false;
    for (const Watch& w : ws) {
      if (!w.binary()) continue;
      if (seen[negate(w.blit)]) {
        units.push_back(Found{a, w.blit, 1, seen[negate(w.blit)]});
        found = true;
        break;
      }
      seen[w.blit] = 1;
    }
    if (!found && !tstart.empty()) {
      for (uint32_t i = tstart[a]; i < tstart[a + 1]; ++i) {
        const Lit x = tother[i];
        if (seen[negate(x)]) {
          units.push_back(Found{a, x, 2, seen[negate(x)]});
          break;
        }
        if (!seen[x]) seen[x] = 2;
      }
    }
    for (const Watch& w : ws) {
      if (w.binary()) seen[w.blit] = 0;
    }
    if (!tstart.empty()) {
      for (uint32_t i = tstart[a]; i < tstart[a + 1]; ++i) seen[tother[i]] = 0;
    }
  }
  ++stats_.binpair_rounds;
  // A productive pass adds the ternary-pair resolvents as binary clauses (RUP; they subsume their
  // pair): unit propagation then runs through them, where a chain of pairs (a carry chain with
  // constant inputs) would otherwise give one more unit per pass.
  if (!units.empty() && !resolvents.empty()) {
    for (const auto& [p, q] : resolvents) {
      if (vals_[p] || vals_[q]) continue;
      if (proof_) {
        const Lit b[2] = {p, q};
        proof_->add(b, 2);
      }
      add_binary(p, q, false);
      ++stats_.binpair_binaries;
    }
  }
  for (const Found& f : units) {
    const Lit u = f.unit;
    if (vals_[u] > 0) continue;
    ++stats_.binpair_units;
    if (proof_) {
      // A binary of a shortened clause (RUP) first; resolvents are in the proof already. Neither
      // is deleted (the resolvents are clauses of the formula now; the others stay implied).
      const Lit b1[2] = {u, f.b}, b2[2] = {u, negate(f.b)};
      if (f.sb == 2) proof_->add(b1, 2);
      if (f.snb == 2) proof_->add(b2, 2);
      proof_->add_unit(u);
    }
    if (vals_[u] < 0) {  // both a and -a: the empty clause by unit propagation
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
      return false;
    }
    assign_unit_in_proof(u);
  }
  if (opts_.verbose >= 2 && !units.empty()) {
    std::printf("c [%.2f s] binary pairs: %zu units (ternary-pair resolvents %zu, shortened clauses %zu)\n", seconds(),
                units.size(), resolvents.size(), shortened.size());
  }
  if (propagated_ < trail_.size() && !propagate()) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return false;
  }
  return true;
}

// --substituterounds: substitution again while the last pass substituted variables (rewritten
// clauses that became binary can close new implication cycles).
void Solver::substitute_rounds() {
  for (int round = 0; round < opts_.substituterounds && !inconsistent_; ++round) {
    const uint32_t before = inactive_;
    substitute();
    if (inactive_ == before) break;
    if (opts_.verbose >= 3) std::printf("c   substitution pass %d: %u substituted\n", round + 1, inactive_ - before);
  }
}

// Removes duplicate binary clauses, keeping one copy per literal pair (irredundant if one is).
// Each list is filtered on its own with the same rule, so both sides keep the same copy; the
// counters and the proof are updated from the side of the smaller literal. The order of the
// remaining watches is kept.
uint64_t Solver::dedup_binaries() {
  const size_t nlits = 2 * size_t{num_vars_};
  std::vector<uint8_t> seen(nlits, 0);  // per other literal: 1 a redundant copy, 2 an irredundant one, | 4 kept
  // Counted first: a handful of duplicates is left alone (removing them changes the watch
  // lists, hence the search, for nothing).
  uint64_t copies = 0;
  for (Lit a = 0; a < nlits; ++a) {
    const ConstWatchList ws = std::as_const(watches_)[a];
    for (const Watch& w : ws) {
      if (!w.binary() || a > w.blit) continue;
      copies += seen[w.blit] ? 1 : 0;
      seen[w.blit] = 1;
    }
    for (const Watch& w : ws) {
      if (w.binary()) seen[w.blit] = 0;
    }
  }
  if (copies < std::max<uint64_t>(1000, (binaries_irredundant_ + binaries_redundant_) / 100)) return 0;
  uint64_t removed = 0;
  for (Lit a = 0; a < nlits; ++a) {
    const WatchList ws = watches_[a];
    bool dup = false;
    for (const Watch& w : ws) {
      if (!w.binary()) continue;
      uint8_t& s = seen[w.blit];
      if (s) dup = true;
      s |= w.redundant_binary() ? 1 : 2;
    }
    if (dup) {
      size_t j = 0;
      for (size_t i = 0; i < ws.size(); ++i) {
        const Watch w = ws[i];
        if (w.binary()) {
          uint8_t& s = seen[w.blit];
          const bool irr = !w.redundant_binary();
          const bool keep = !(s & 4) && (irr || !(s & 2));
          if (!keep) {
            if (a < w.blit) {
              ++removed;
              if (irr) {
                --binaries_irredundant_;
              } else {
                --binaries_redundant_;
              }
              if (proof_) {
                const Lit bin[2] = {a, w.blit};
                proof_->del(bin, 2);
              }
            }
            continue;
          }
          s |= 4;
        }
        ws[j++] = w;
      }
      ws.resize(j);
    }
    for (const Watch& w : ws) {
      if (w.binary()) seen[w.blit] = 0;
    }
  }
  stats_.deduplicated += removed;
  return removed;
}

// Equivalences found outside elimination rounds (by sweeping) are substituted right away, in a
// round of their own at the root: long watches detached, garbage collected, root trail
// propagated again over the new watches.
void Solver::substitute_now() {
  const uint32_t inactive_before = inactive_;
  disconnect_long_watches();
  substitute_rounds();
  if (inactive_ != inactive_before) drop_inactive_decisions();
  if (opts_.verbose >= 2) std::printf("c [%.2f s] substitution after sweeping: %u substituted (equivalences so far %llu, sweeps %llu)\n", seconds(), inactive_ - inactive_before, static_cast<unsigned long long>(stats_.sweep_equivalences), static_cast<unsigned long long>(stats_.sweeps));
  collect_garbage();
  reconnect_long_watches();
  if (!inconsistent_ && !propagate_vivify(kNoReason)) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
  }
}

}  // namespace psat
