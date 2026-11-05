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
#include <cstdio>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

bool Solver::substitute() {
  const PassTimer pass_timer(*this, kPassSubstitute);
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
      const std::vector<Watch>& ws = watches_[negate(u)];
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
    if (vals_[unit] == 0) assign(unit, kNoReason);
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

  // Rewrite long clauses (in place: long watches are detached) and collect the rewritten ones.
  std::vector<Lit> tmp;
  std::vector<std::vector<Lit>> to_delete;
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
    to_delete.emplace_back(lits, lits + c.size);
    if (!c.redundant) touch_clause(lits, c.size);
    if (taut) {
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
    if (proof_) proof_->add(tmp.data(), tmp.size());
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
        if (vals_[tmp[0]] == 0) assign(tmp[0], kNoReason);
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
        assign(ra, kNoReason);
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
  for (const Bin& b : bins) {
    remove_binary_watch(b.a, b.b, b.redundant);
    remove_binary_watch(b.b, b.a, b.redundant);
    if (b.redundant) {
      --binaries_redundant_;
    } else {
      --binaries_irredundant_;
    }
    touched_[var_of(b.a)] = touched_[var_of(b.b)] = 1;
    const Lit ra = repr[b.a], rb = repr[b.b];
    if (ra == negate(rb) || ra == rb) continue;
    add_binary(ra, rb, b.redundant);
  }
  // Now the old clauses can go.
  if (proof_) {
    for (const auto& c : to_delete) proof_->del(c.data(), c.size());
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
  return true;
}

// Equivalences found outside elimination rounds (by sweeping) are substituted right away, in a
// round of their own at the root: long watches detached, garbage collected, root trail
// propagated again over the new watches.
void Solver::substitute_now() {
  const uint32_t inactive_before = inactive_;
  disconnect_long_watches();
  substitute();
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
