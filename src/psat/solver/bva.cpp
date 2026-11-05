// Bounded variable addition (Manthey, Heule & Biere, HVC 2012; SBVA, Haberlandt et al., SAT 2023;
// Kissat's "factor"). Runs inside an elimination round (dense mode, occurrence lists built).
//
// For a literal l, find literals M_lit = {l, l2, ...} and clause remainders M_cls = {C1', ...}
// such that every clause (k v Ci') with k in M_lit exists. Replacing those |M_lit| * |M_cls|
// clauses by (x v Ci') for each Ci' and (-x v k) for each k, with a fresh variable x, removes
// |M_lit| * |M_cls| - |M_lit| - |M_cls| clauses. The matching grows M_lit greedily by the literal
// that keeps the most clauses, while the reduction grows.
//
// DRAT: the clauses (x v Ci') are RAT on x (no clause contains -x yet), then (-x v k) are RAT on
// -x (every resolvent with an (x v Ci') clause is the existing clause (k v Ci')); the pivot is
// written first. The replaced clauses are then deleted. Models need no reconstruction: x true
// forces every k, x false forces every Ci', so the original clauses hold either way.
//
// Trial rounds (--bvamin): the same matching without replacements; the clauses a replacement
// would remove are only marked, so later matchings skip them, and the reductions are summed.
// BVA pays off where it removes a large share of the formula (at-most-one cliques: battleship,
// stb); a few replacements in a large formula only perturb the search (spg: 2 variables, 10x
// slower), so a round is made only when the trial's reduction reaches the threshold.

#include <algorithm>
#include <unordered_set>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

int64_t reduction(size_t lits, size_t clauses) {
  return static_cast<int64_t>(lits * clauses) - static_cast<int64_t>(lits) - static_cast<int64_t>(clauses);
}

// An irredundant clause in BVA: a long clause reference, or a binary clause (a, b).
struct BClause {
  uint32_t ref;  // kNoReason for binary clauses
  Lit a, b;
};

}  // namespace

size_t Solver::bva_count(Lit l, uint64_t& budget) {
  size_t n = occs_.size(l);
  for (const Watch& w : watches_[l]) n += w.binary() && !w.redundant_binary();
  budget += watches_[l].size() / 8 + 1;
  return n;
}

int64_t Solver::bva_round(uint64_t& budget, uint64_t limit, bool dry) {
  const PassTimer pass_timer(*this, kPassBva);
  int64_t reduced = 0;
  // Trial rounds: the clauses later replacements may not use (long by reference, binary by
  // their ordered literal pair).
  std::unordered_set<uint32_t> consumed_long;
  std::unordered_set<uint64_t> consumed_bin;
  auto bin_key = [](Lit a, Lit b) { return (uint64_t{std::min(a, b)} << 32) | std::max(a, b); };
  // New variables per round: a tenth of the variables, but at least --bvavars (small crafted
  // formulas, such as at-most-one cliques over a few hundred variables, need several per clique).
  const uint32_t max_new = std::max<uint32_t>(static_cast<uint32_t>(opts_.bvavars), num_vars_ / 10);
  uint32_t added = 0;

  auto occurrences = [&](Lit l, std::vector<BClause>& out) {
    out.clear();
    uint32_t* os = occs_.begin(l);
    const uint32_t n = occs_.size(l);
    uint32_t j = 0;
    // (A trial leaves the occurrence lists as they are: when it declines, elimination sees the
    // same lists, in particular the same counts for its candidate order, as without BVA.)
    for (uint32_t i = 0; i < n; ++i) {
      if (clause(os[i]).garbage) continue;
      if (!dry) os[j++] = os[i];
      if (dry && consumed_long.count(os[i])) continue;
      out.push_back(BClause{os[i], kNoLit, kNoLit});
    }
    if (!dry) occs_.truncate(l, j);
    for (const Watch& w : watches_[l]) {
      if (!w.binary() || w.redundant_binary()) continue;
      if (dry && consumed_bin.count(bin_key(l, w.blit))) continue;
      out.push_back(BClause{kNoReason, l, w.blit});
    }
    budget += out.size() / 4 + 1;
  };
  auto lits_of = [&](const BClause& c, std::vector<Lit>& out) {
    out.clear();
    if (c.ref == kNoReason) {
      out.push_back(c.a);
      out.push_back(c.b);
    } else {
      const Clause& k = clause(c.ref);
      out.assign(k.lits(), k.lits() + k.size);
    }
  };

  // Literals by occurrence count, most frequent first.
  std::vector<std::pair<size_t, Lit>> queue;
  for (Lit l = 0; l < 2 * num_vars_; ++l) {
    if (vals_[l] != 0 || eliminated_[var_of(l)]) continue;
    const size_t n = bva_count(l, budget);
    if (n >= 3) queue.emplace_back(n, l);
  }
  std::sort(queue.begin(), queue.end(), [](const auto& a, const auto& b) { return a.first > b.first; });

  struct Pair {
    Lit lit;
    uint32_t cidx;
    BClause d;
  };
  std::vector<BClause> m_cls, occ;
  std::vector<std::vector<BClause>> matched;  // per M_cls entry: its clause for each M_lit literal
  std::vector<Lit> m_lit, cl, dl, rest;
  std::vector<Pair> pairs;
  std::vector<uint32_t> lit_count(2 * size_t{num_vars_}, 0);
  uint32_t retries = 0;

  // Ties between matching literals (SBVA's 3-hop heuristic, Kissat's factorhops): the candidate
  // b with the largest (A^3)[l][b], where A[x][y] is the number of irredundant clauses with both
  // variables x and y (the diagonal A[x][x] is x's number of clauses, as in SBVA). hop1 = A[l]
  // and hop2 = A^2[l] are computed once per l (the formula only changes when a replacement is
  // made); b's score is the sum of hop2 over the variables of b's clauses. Equal scores: the
  // smaller literal. Skipped (smaller literal) when l's second neighbourhood is too large.
  std::vector<uint64_t> hop1(num_vars_, 0), hop2(num_vars_, 0);
  std::vector<Var> hop1_vars, hop2_vars, ties;
  Var hops_for = UINT32_MAX;
  bool hops_ok = false;
  constexpr uint64_t kHopVisits = uint64_t{1} << 20;
  auto neighbors = [&](Var u, auto&& visit) {
    for (int sign = 0; sign < 2; ++sign) {
      const Lit lit = make_lit(u, sign != 0);
      const uint32_t* os = occs_.begin(lit);
      const uint32_t n = occs_.size(lit);
      for (uint32_t i = 0; i < n; ++i) {
        const Clause& c = clause(os[i]);
        if (c.garbage) continue;
        budget += c.size / 4 + 1;
        for (uint32_t k = 0; k < c.size; ++k) visit(var_of(c.lits()[k]));  // (u itself too)
      }
      for (const Watch& w : watches_[lit]) {
        if (w.binary() && !w.redundant_binary()) {
          visit(u);
          visit(var_of(w.blit));
        }
      }
      budget += watches_[lit].size() / 8 + 1;
    }
  };
  auto compute_hops = [&](Var a) {
    for (const Var y : hop2_vars) hop2[y] = 0;
    for (const Var x : hop1_vars) hop1[x] = 0;
    hop1_vars.clear();
    hop2_vars.clear();
    hops_for = a;
    neighbors(a, [&](Var x) {
      if (!hop1[x]++) hop1_vars.push_back(x);
    });
    uint64_t visits = 0;
    for (const Var x : hop1_vars) {
      for (int sign = 0; sign < 2; ++sign) visits += occs_.size(make_lit(x, sign != 0)) + watches_[make_lit(x, sign != 0)].size();
    }
    hops_ok = visits <= kHopVisits;
    if (!hops_ok) return;
    for (const Var x : hop1_vars) {
      const uint64_t w = hop1[x];
      neighbors(x, [&](Var y) {
        if (!hop2[y]) hop2_vars.push_back(y);
        hop2[y] += w;
      });
    }
  };
  auto hop_score = [&](Var b) {
    uint64_t score = 0;
    neighbors(b, [&](Var y) { score += hop2[y]; });
    return score;
  };
  Lit last_l = kNoLit;

  for (size_t qi = 0; qi < queue.size() && budget <= limit && added < max_new && !inconsistent_; ++qi) {
    const Lit l = queue[qi].second;
    if (l != last_l) retries = 0;
    last_l = l;
    if (vals_[l] != 0 || eliminated_[var_of(l)]) continue;
    occurrences(l, m_cls);
    if (m_cls.size() < 3) continue;
    m_lit.assign(1, l);
    matched.assign(m_cls.size(), {});
    for (size_t i = 0; i < m_cls.size(); ++i) matched[i].push_back(m_cls[i]);
    // Each step extends the last complete matching; when the budget runs out the matching found
    // so far is used (the inner loops are charged: on large formulas one literal's matching
    // can otherwise take seconds).
    for (;;) {
      if (budget > limit) break;
      pairs.clear();
      bool out_of_budget = false;
      for (uint32_t ci = 0; ci < m_cls.size(); ++ci) {
        // Checked per clause too: on formulas with few variables and many clauses one step
        // scans thousands of clauses with thousands of partner occurrences each.
        if (budget > limit) {
          out_of_budget = true;
          break;
        }
        lits_of(m_cls[ci], cl);
        budget += cl.size() / 4 + 1;
        // Mark C - {l} and pick its literal with the fewest occurrences.
        Lit lmin = kNoLit;
        size_t best = SIZE_MAX;
        for (const Lit y : cl) {
          if (y == l) continue;
          marks_[y] = 1;
          const size_t n = bva_count(y, budget);
          if (n < best) {
            best = n;
            lmin = y;
          }
        }
        if (lmin != kNoLit) {
          occurrences(lmin, occ);
          for (const BClause& d : occ) {
            lits_of(d, dl);
            budget += dl.size() / 4 + 1;
            if (dl.size() != cl.size()) continue;
            Lit extra = kNoLit;
            bool ok = true;
            for (const Lit y : dl) {
              if (marks_[y]) continue;
              if (extra != kNoLit) {
                ok = false;
                break;
              }
              extra = y;
            }
            if (!ok || extra == kNoLit || vals_[extra] != 0 || eliminated_[var_of(extra)]) continue;
            if (marks_[negate(extra)]) continue;
            // Not a literal of a matched variable (in particular not -l: (l v C) and (-l v C) are
            // for strengthening, and -l would always win the 3-hop tie-break).
            if (std::any_of(m_lit.begin(), m_lit.end(), [&](Lit k) { return var_of(k) == var_of(extra); })) continue;
            pairs.push_back(Pair{extra, ci, d});
          }
        }
        for (const Lit y : cl) marks_[y] = 0;
      }
      if (out_of_budget || pairs.empty()) break;  // (an incomplete step: the last complete matching)
      // The literal matching the most clauses (ties: smaller literal, deterministic).
      Lit lmax = kNoLit;
      uint32_t best_count = 0;
      uint32_t last = UINT32_MAX;
      Lit last_lit = kNoLit;
      for (const Pair& p : pairs) {
        if (p.cidx == last && p.lit == last_lit) continue;  // one partner per clause and literal
        last = p.cidx;
        last_lit = p.lit;
        const uint32_t c = ++lit_count[p.lit];
        if (c > best_count || (c == best_count && p.lit < lmax)) {
          best_count = c;
          lmax = p.lit;
        }
      }
      const bool improves = reduction(m_lit.size() + 1, best_count) > reduction(m_lit.size(), m_cls.size());
      if (improves && opts_.bvahops) {
        ties.clear();
        for (const Pair& p : pairs) {
          if (lit_count[p.lit] != best_count) continue;
          lit_count[p.lit] = 0;  // (once per literal)
          ties.push_back(p.lit);
        }
        if (ties.size() > 1) {
          if (hops_for != var_of(l)) compute_hops(var_of(l));
          if (hops_ok) {
            uint64_t best_score = 0;
            for (const Lit t : ties) {
              const uint64_t sc = hop_score(var_of(t));
              if (sc > best_score || (sc == best_score && t < lmax)) {
                best_score = sc;
                lmax = t;
              }
            }
            ++stats_.bva_hop_ties;
          }
        }
      }
      for (const Pair& p : pairs) lit_count[p.lit] = 0;
      if (!improves) break;
      std::vector<BClause> next_cls;
      std::vector<std::vector<BClause>> next_matched;
      last = UINT32_MAX;
      for (const Pair& p : pairs) {
        if (p.lit != lmax || p.cidx == last) continue;
        last = p.cidx;
        next_cls.push_back(m_cls[p.cidx]);
        next_matched.push_back(matched[p.cidx]);
        next_matched.back().push_back(p.d);
      }
      m_cls.swap(next_cls);
      matched.swap(next_matched);
      m_lit.push_back(lmax);
    }
    if (m_lit.size() < 2 || reduction(m_lit.size(), m_cls.size()) <= 0) continue;
    if (dry) {
      reduced += reduction(m_lit.size(), m_cls.size());
      ++added;
      for (const auto& row : matched) {
        for (const BClause& d : row) {
          if (d.ref != kNoReason) {
            consumed_long.insert(d.ref);
          } else {
            consumed_bin.insert(bin_key(d.a, d.b));
          }
        }
      }
      budget += m_lit.size() * m_cls.size();
      if (retries++ < 8) --qi;
      continue;
    }

    // Replace with a fresh variable x.
    const Var xv = num_vars_;
    grow_vars(num_vars_ + 1);
    occs_.grow(2 * size_t{num_vars_});
    lit_count.resize(2 * size_t{num_vars_}, 0);
    hop1.resize(num_vars_, 0);
    hop2.resize(num_vars_, 0);
    hops_for = UINT32_MAX;  // the formula changes
    touched_[xv] = 1;
    if (bva_added_.size() < num_vars_) bva_added_.resize(num_vars_, 0);
    bva_added_[xv] = 1;
    ++added;
    ++stats_.bva_vars;
    const Lit x = make_lit(xv, false);
    for (const BClause& c : m_cls) {
      lits_of(c, cl);
      rest.assign(1, x);
      for (const Lit y : cl) {
        if (y != l) rest.push_back(y);
      }
      if (proof_) proof_->add(rest.data(), rest.size());
      touch_clause(rest.data(), static_cast<uint32_t>(rest.size()));
      if (rest.size() == 2) {
        add_binary(rest[0], rest[1], false);
      } else {
        const uint32_t ref = new_clause(rest.data(), static_cast<uint32_t>(rest.size()), false, 0, false);
        for (const Lit y : rest) occs_.push(y, ref);
      }
    }
    for (const Lit k : m_lit) {
      const Lit bin[2] = {negate(x), k};
      if (proof_) proof_->add(bin, 2);
      add_binary(negate(x), k, false);
    }
    // Delete the replaced clauses (each once, even if the input had duplicates).
    std::vector<std::pair<Lit, Lit>> deleted_bins;
    for (const auto& row : matched) {
      for (const BClause& d : row) {
        if (d.ref != kNoReason) {
          if (!clause(d.ref).garbage) delete_irredundant(d.ref);
          continue;
        }
        const std::pair<Lit, Lit> key{std::min(d.a, d.b), std::max(d.a, d.b)};
        if (std::find(deleted_bins.begin(), deleted_bins.end(), key) != deleted_bins.end()) continue;
        deleted_bins.push_back(key);
        delete_binary(d.a, d.b);
        --binaries_irredundant_;
      }
    }
    stats_.bva_removed += m_lit.size() * m_cls.size();
    stats_.bva_added += m_lit.size() + m_cls.size();
    reduced += reduction(m_lit.size(), m_cls.size());
    if (retries++ < 8) --qi;  // try l again
  }
  return reduced;
}

void Solver::bva_run(uint64_t& budget) {
  const uint64_t extra = std::max<uint64_t>(static_cast<uint64_t>(opts_.bvaticks), arena_.size() / 4);
  if (opts_.bvamin > 0) {
    const uint64_t clauses = irredundant_ + binaries_irredundant_;
    const int64_t trial = bva_round(budget, budget + extra, true);
    ++stats_.bva_trials;
    const bool go = clauses > 0 && trial > 0 &&
                    static_cast<uint64_t>(trial) * 1000 >= static_cast<uint64_t>(opts_.bvamin) * clauses;
    if (opts_.verbose >= 2) {
      std::printf("c [%.2f s] bva trial: reduction %lld of %llu irredundant clauses (%.1f%%), %s\n", seconds(),
                  static_cast<long long>(trial), static_cast<unsigned long long>(clauses),
                  clauses ? 100.0 * static_cast<double>(trial) / static_cast<double>(clauses) : 0.0,
                  go ? "replacing" : "skipped");
    }
    if (!go) return;
    ++stats_.bva_rounds;
  }
  bva_round(budget, budget + extra, false);
}

}  // namespace psat
