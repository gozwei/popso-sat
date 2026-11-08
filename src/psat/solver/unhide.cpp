// Unhiding (Heule, Järvisalo & Biere, "Efficient CNF Simplification based on Binary Implication
// Graphs", SAT 2011): a randomized depth-first search over the binary implication graph gives
// every literal a discovered-finished interval [dsc, fin]; an interval containing another one
// represents an implication between the two literals. The search itself (the paper's advanced
// stamping) finds failed literals and transitive binary clauses; the stamps then remove hidden
// tautologies (clauses subsumed by a binary clause implied by the graph) and hidden literals (a
// literal of a clause that implies another literal of the same clause) from the long clauses.
//
// Our choices:
// - The graph has the irredundant binary clauses only, so deleting an irredundant clause never
//   depends on a learned clause (which might have been derived from the deleted one).
//   Learned long clauses are simplified with the same stamps.
// - The search runs on its own compact copy of the graph (edges with a dead flag), so removing a
//   transitive edge never disturbs a watch list that an open search frame is iterating; the
//   binary clauses are deleted from the watch lists at the end.
// - Proof order: units and shortened clauses (all RUP through binary clauses of the graph) are
//   added before any transitive binary clause is deleted, so every addition can be checked
//   against the complete set of binary clauses.
// - Runs at the root, inside vivification rounds, before failed literal probing; the long-clause
//   phase has a ticks budget (the linear graph search is not limited) and continues where the
//   previous round stopped.

#include <algorithm>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

void Solver::unhide(uint64_t ticks_limit) {
  const PassTimer pass_timer(*this, kPassUnhide);
  ++stats_.unhides;
  const size_t nlits = 2 * size_t{num_vars_};
  auto active = [&](Lit l) { return vals_[l] == 0 && !eliminated_[var_of(l)]; };
  uint64_t ticks = 0;

  // The graph: edge u -> v for every irredundant binary clause (-u v), from watches_[-u].
  std::vector<uint32_t>& start = unhide_start_;
  std::vector<Lit>& target = unhide_target_;
  start.assign(nlits + 1, 0);
  for (Lit u = 0; u < nlits; ++u) {
    if (!active(u)) continue;
    uint32_t n = 0;
    for (const Watch& w : watches_[negate(u)]) n += w.binary() && !w.redundant_binary() && active(w.blit);
    start[u + 1] = n;
  }
  for (size_t u = 0; u < nlits; ++u) start[u + 1] += start[u];
  const uint32_t edges = start[nlits];
  if (edges == 0) return;
  target.resize(edges);
  std::vector<uint8_t> dead(edges, 0);
  {
    std::vector<uint32_t> fill(start.begin(), start.end() - 1);
    for (Lit u = 0; u < nlits; ++u) {
      if (!active(u)) continue;
      for (const Watch& w : watches_[negate(u)]) {
        if (w.binary() && !w.redundant_binary() && active(w.blit)) target[fill[u]++] = w.blit;
      }
    }
  }
  ticks += nlits / 8 + edges / 4;

  // Stamps. dsc = 0: not visited yet. obs: the latest time the literal was observed.
  std::vector<uint32_t>& dsc = unhide_dsc_;
  std::vector<uint32_t>& fin = unhide_fin_;
  std::vector<uint32_t> obs(nlits, 0);
  std::vector<Lit> prt(nlits), root(nlits);
  dsc.assign(nlits, 0);
  fin.assign(nlits, 0);
  uint32_t stamp = 0;
  std::vector<Lit> scc;        // literals whose component is not complete yet
  std::vector<Lit> units;      // negations of failed literals
  std::vector<uint8_t> unit_mark(nlits, 0);
  std::vector<std::pair<Lit, Lit>> transitive;  // binary clauses to delete
  struct Frame {
    Lit lit;
    uint32_t pos;  // next edge
    bool repr;     // still the representative of its component
  };
  std::vector<Frame> frames;

  auto discover = [&](Lit l) {
    dsc[l] = obs[l] = ++stamp;
    scc.push_back(l);
    frames.push_back(Frame{l, start[l], true});
  };
  // After an edge l -> v with v visited (now or before): equivalences and observation.
  auto observed = [&](Frame& f, Lit v) {
    if (fin[v] == 0 && dsc[v] < dsc[f.lit]) {  // v is an open ancestor: l and v are equivalent
      dsc[f.lit] = dsc[v];
      f.repr = false;
    }
    obs[v] = stamp;
  };
  auto kill = [&](uint32_t e, Lit u, Lit v) {  // edge u -> v and its mirror -v -> -u
    dead[e] = 1;
    const Lit nv = negate(v), nu = negate(u);
    for (uint32_t k = start[nv]; k < start[nv + 1]; ++k) {
      if (!dead[k] && target[k] == nu) {
        dead[k] = 1;
        break;
      }
    }
    ticks += 1 + (start[nv + 1] - start[nv]) / 8;
    transitive.emplace_back(nu, v);
  };
  auto stamp_tree = [&](Lit r) {
    prt[r] = root[r] = r;
    discover(r);
    while (!frames.empty()) {
      Frame& f = frames.back();
      const Lit l = f.lit;
      if (f.pos < start[l + 1]) {
        const uint32_t e = f.pos++;
        ++ticks;
        if (dead[e]) continue;
        const Lit v = target[e];
        if (!active(v)) continue;
        // Transitive edge: v was observed since l was discovered, i.e. through another path.
        if (dsc[l] < obs[v]) {
          kill(e, l, v);
          continue;
        }
        // Failed literal: -v observed in this tree; the lowest common ancestor implies v and -v.
        const Lit nv = negate(v);
        if (dsc[root[l]] <= obs[nv]) {
          Lit failed = l;
          while (dsc[failed] > obs[nv]) failed = prt[failed];
          const Lit unit = negate(failed);
          if (!unit_mark[unit]) {
            unit_mark[unit] = 1;
            units.push_back(unit);
          }
          if (dsc[nv] != 0 && fin[nv] == 0) continue;  // -v is an open ancestor: v is a unit
        }
        if (dsc[v] == 0) {
          prt[v] = l;
          root[v] = root[l];
          discover(v);  // f may dangle from here on
          continue;
        }
        observed(f, v);
        continue;
      }
      // l is finished; as a representative it closes its component (one interval for all).
      const bool repr = f.repr;
      frames.pop_back();
      if (repr) {
        ++stamp;
        Lit m;
        do {
          m = scc.back();
          scc.pop_back();
          dsc[m] = dsc[l];
          fin[m] = stamp;
        } while (m != l);
      }
      if (!frames.empty()) observed(frames.back(), l);
    }
  };

  // Roots (literals without incoming edges, i.e. whose negation has no outgoing edge) in random
  // order first, then every literal not visited yet.
  std::vector<Lit> order;
  for (Lit l = 0; l < nlits; ++l) {
    if (active(l) && start[l + 1] > start[l] && start[negate(l) + 1] == start[negate(l)]) order.push_back(l);
  }
  for (size_t i = order.size(); i > 1; --i) {
    rng_ ^= rng_ << 13;
    rng_ ^= rng_ >> 7;
    rng_ ^= rng_ << 17;
    std::swap(order[i - 1], order[rng_ % i]);
  }
  for (const Lit r : order) {
    if (dsc[r] == 0) stamp_tree(r);
  }
  for (Lit l = 0; l < nlits; ++l) {
    if (active(l) && dsc[l] == 0) stamp_tree(l);
  }

  // Units first (RUP: the failed literal propagates to a conflict over the binary clauses).
  for (const Lit u : units) {
    if (inconsistent_) break;
    if (vals_[u] > 0) continue;
    ++stats_.unhide_units;
    if (proof_) proof_->add_unit(u);
    if (vals_[u] < 0) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
      break;
    }
    assign_unit_in_proof(u);
    if (!propagate_vivify(kNoReason)) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
    }
  }

  // Long clauses: hidden tautologies are deleted, hidden literals removed. Clauses with assigned
  // literals are left to root simplification (a path through an assigned literal makes a
  // literal of the clause assigned too, so the stamps stay valid for the others).
  std::vector<Lit> pos, neg, kept;
  const uint64_t search_ticks = ticks;
  auto by_dsc = [&](Lit a, Lit b) { return dsc[a] < dsc[b]; };
  size_t i = unhide_next_ < clauses_.size() ? unhide_next_ : 0;
  const size_t count = clauses_.size();
  for (size_t done = 0; done < count && !inconsistent_; ++done, ++i) {
    if (i >= clauses_.size()) i = 0;
    if (ticks - search_ticks > ticks_limit || stop_requested()) break;
    const uint32_t ref = clauses_[i];
    Clause& c = clause(ref);
    if (c.garbage) continue;
    const uint32_t n = c.size;
    ticks += 1 + n / 4;
    const Lit* lits = c.lits();
    bool skip = false;
    for (uint32_t k = 0; k < n && !skip; ++k) skip = !active(lits[k]);
    if (skip) continue;
    pos.assign(lits, lits + n);
    neg.resize(n);
    for (uint32_t k = 0; k < n; ++k) neg[k] = negate(lits[k]);
    std::sort(pos.begin(), pos.end(), by_dsc);
    std::sort(neg.begin(), neg.end(), by_dsc);
    ticks += n;
    // Hidden tautology: some -x (x in C) whose interval contains that of a y in C, so the graph
    // implies the binary clause (x y), which subsumes C.
    bool tautology = false;
    {
      size_t p = 0, q = 0;
      for (;;) {
        if (dsc[neg[q]] > dsc[pos[p]]) {
          if (++p == n) break;
        } else if (fin[neg[q]] < fin[pos[p]]) {
          if (++q == n) break;
        } else {
          tautology = true;
          break;
        }
      }
    }
    if (tautology) {
      ++stats_.unhide_tautologies;
      if (c.redundant) {
        delete_clause_proof(c);
        c.garbage = 1;
        note_garbage(c);
        garbage_words_ += kHeaderWords + c.size;
        --redundant_;
      } else {
        delete_irredundant(ref);
      }
      continue;
    }
    // Hidden literals: in decreasing discovery order, a literal whose interval contains that of
    // the last kept one implies it; then the same over the negations (increasing order), where
    // the interval of a kept -y containing that of -x means -y -> -x, i.e. x -> y.
    kept.clear();
    {
      uint32_t finished = fin[pos[n - 1]];
      kept.push_back(pos[n - 1]);
      for (size_t k = n - 1; k-- > 0;) {
        if (fin[pos[k]] > finished) continue;
        finished = fin[pos[k]];
        kept.push_back(pos[k]);
      }
    }
    if (kept.size() > 1) {
      neg.resize(kept.size());
      for (size_t k = 0; k < kept.size(); ++k) neg[k] = negate(kept[k]);
      std::sort(neg.begin(), neg.end(), by_dsc);
      kept.clear();
      uint32_t finished = fin[neg[0]];
      kept.push_back(negate(neg[0]));
      for (size_t k = 1; k < neg.size(); ++k) {
        if (fin[neg[k]] < finished) continue;
        finished = fin[neg[k]];
        kept.push_back(negate(neg[k]));
      }
    }
    if (kept.size() == n) continue;
    // Replace C by the kept literals (RUP: falsifying them falsifies the removed ones through
    // the binary clauses, so C is falsified).
    ++stats_.unhide_strengthened;
    stats_.unhide_literals += n - kept.size();
    const bool red = c.redundant;
    const uint32_t glue = c.glue;
    if (proof_) proof_->add(kept.data(), kept.size());
    if (red) {
      delete_clause_proof(c);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      --redundant_;
    } else {
      delete_irredundant(ref);
    }
    if (kept.size() == 1) {
      if (vals_[kept[0]] == 0) {
        assign_unit_in_proof(kept[0]);
        if (!propagate_vivify(kNoReason)) {
          inconsistent_ = true;
          if (proof_) proof_->add_empty();
        }
      }
    } else if (kept.size() == 2) {
      add_binary(kept[0], kept[1], red);
    } else {
      const uint32_t size = static_cast<uint32_t>(kept.size());
      new_clause(kept.data(), size, red, std::min(glue, size - 1));
    }
  }
  unhide_next_ = i;

  // Transitive binary clauses last (the additions above may have used them).
  for (const auto& [a, b] : transitive) {
    if (inconsistent_) break;
    if (vals_[a] != 0 || vals_[b] != 0) continue;  // left to root simplification
    delete_binary(a, b);
    --binaries_irredundant_;
    ++stats_.unhide_transitive;
  }
  stats_.unhide_ticks += ticks;
}

}  // namespace psat
