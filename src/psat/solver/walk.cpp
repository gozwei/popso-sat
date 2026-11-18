// Local search for phases ("walk" rephasing, as in Kissat) over the irredundant clauses,
// root-simplified, starting from the saved phases. The assignment with the fewest unsatisfied
// clauses seen becomes the saved phases. Effort is a share of the search ticks since the last
// walk, counted in occurrences visited. Two algorithms (--walkmode):
//
// ProbSAT (0, Balint & Schoening 2012): pick a random unsatisfied clause, flip one of its
// variables chosen with probability proportional to cb^-break, where break is the number of
// clauses that would become unsatisfied and cb depends on the average clause length (2.06 for
// 3-SAT, larger for longer clauses).
//
// Break values are cached: every clause keeps its number of true literals and the XOR of them,
// so when one true literal is left it is known without a scan, and break[v] (the clauses in which
// v's literal is the only true one) is updated during the flip. A flip then visits the
// occurrences of the flipped variable once; computing breaks on demand visited the occurrences
// of every literal of the picked clause as well (11 x 5000 on dense 11-SAT formulas).
//
// DDFW (1, "divide and distribute fixed weights": Ishtaiwi, Thornton, Sattar & Pham, CP 2005;
// parameters as restated by Chowdhury, Codel & Heule, "A Linear Weight Transfer Rule for Local
// Search", NFM 2023): every clause has a weight, initially w0 = 8. A variable's score is the
// weight of the unsatisfied clauses that flipping it satisfies minus the weight of the clauses
// in which its literal is the only true one. While a variable with a positive score exists,
// flip one with the largest score. Otherwise (a local minimum of the weighted cost), with
// probability 0.15 flip a variable of an unsatisfied clause whose score is 0 (a sideways move),
// else every unsatisfied clause takes weight from a satisfied neighbour (a clause that shares a
// literal with it, so that flipping that literal's variable satisfies the one without breaking
// the other): the heaviest one, or with probability 0.01, or if the heaviest weighs less than w0,
// a random satisfied clause of weight at least w0. The donor gives 2 if it weighs more than w0,
// else 1. Weight thus moves to the clauses that stay unsatisfied and the local minimum fills up.
//
// --walkmode=2 uses the modifications of Chowdhury, Codel & Heule 2023 (their recommended
// setting lw-ith with cspt 0.1 and weighted-random selection): a donor heavier than w0 gives
// 0.05 w + 1, one of weight w0 gives 0.1 w + 2; the random donor is taken with probability 0.1;
// the flipped variable is drawn with probability proportional to its positive score.
//
// Weights are fixed-point integers (w0 = 800), scores 64-bit sums of them: the same walk on
// every platform. Variables with a positive score are kept in a list; the choice scans it when it
// has at most 64 entries and otherwise draws 64 of them ("best from multiple selections", Cai
// 2015), and a neighbour scan reads at most 256 occurrences per literal, from a random offset
// (formulas with literals in a million clauses).
//
// --walkmode=3 keeps the ProbSAT walk for the phases and then runs the walk of mode 2 from its
// best assignment, with the same budget, for a model only: its assignment is dropped otherwise.
// On the paired sets the clause-weighting phases of modes 1 and 2 changed the search on both
// sides (UNSAT trajectories, and SAT instances found 10-40x later as well as earlier), while the
// ProbSAT walk moves the saved phases little; mode 3 keeps that search unless a model is found.
//
// --walkmodel (off by default) budgets mode 3's model walk by how close the walks come to a model:
// far from one (more unsatisfied clauses than sqrt(clauses)), it backs off and gets the share of
// the search ticks only (at the end of walk()).
//
// With --walkmode=1, 2 or 3 a walk that ends with no unsatisfied clause leaves its model on the
// trail (decisions in input order with propagation, every walk clause checked again), and the
// search reports SAT at its next step; the program checks the model against the input formula.

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>

#include "psat/solver/solver.hpp"

namespace psat {

namespace {

struct Rng {
  uint64_t s;
  uint64_t next() {
    s ^= s << 13;
    s ^= s >> 7;
    s ^= s << 17;
    return s;
  }
  double uniform() { return static_cast<double>(next() >> 11) * (1.0 / 9007199254740992.0); }
};

}  // namespace

void Solver::walk() {
  const PassTimer pass_timer(*this, kPassWalk);
  const double walk_start = opts_.verbose >= 3 ? seconds() : 0;
  ++stats_.walks;
  if (level() > 0) backtrack(0);
  // Root-simplified irredundant clauses, numbered long clauses first (clauses_ order), then binary
  // clauses (watch order). Long clauses are read in place in the arena, skipping literals false at
  // the root (no root-satisfied clause is included); binary clauses are copied as literal pairs (a
  // pair with a root-false literal keeps the other one and kNoLit). A copy of the long clauses in
  // CSR form took 4 bytes per literal and per clause (velev-vliw-sat-4.0-b8: the walk's arrays
  // 508 MB, as-p147: 389 MB, on top of everything the search keeps).
  std::vector<uint32_t> refs;  // clause c < nlong: arena reference
  std::vector<Lit> bins;       // clause c >= nlong: bins[2 (c - nlong)], bins[2 (c - nlong) + 1]
  size_t nlits = 0;            // literals of all clauses (root-false ones not counted)
  {
    size_t nlong = 0;
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (!c.garbage && !c.redundant) ++nlong;
    }
    refs.reserve(nlong);
    bins.reserve(2 * size_t{binaries_irredundant_});
  }
  auto keep = [&](const Lit* cl, uint32_t n) -> uint32_t {  // literals left, 0 if satisfied
    uint32_t left = 0;
    for (uint32_t k = 0; k < n; ++k) {
      const int8_t v = vals_[cl[k]];
      if (v > 0) return 0;
      left += v == 0;
    }
    return left;  // (0 for a clause falsified at the root: cannot happen after propagation)
  };
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    const uint32_t left = keep(c.lits(), c.size);
    if (!left) continue;
    refs.push_back(ref);
    nlits += left;
  }
  const uint32_t nlong = static_cast<uint32_t>(refs.size());
  // (binary clauses in input numbering order: the same walk after a renumbering)
  for (Lit k = 0; k < 2 * num_vars_; ++k) {
    const Lit l = make_lit(internal_var(var_of(k)), is_negative(k));
    for (const Watch& w : watches_[l]) {
      if (w.binary() && !w.redundant_binary() && k < external_lit(w.blit)) {
        const Lit b[2] = {l, w.blit};
        const uint32_t left = keep(b, 2);
        if (!left) continue;
        if (left == 2) {
          bins.push_back(l);
          bins.push_back(w.blit);
        } else {
          bins.push_back(vals_[l] ? w.blit : l);
          bins.push_back(kNoLit);
        }
        nlits += left;
      }
    }
  }
  const uint32_t nclauses = nlong + static_cast<uint32_t>(bins.size() / 2);
  if (!nclauses) return;
  // Calls f(lit) for the literals of clause c (in clause order, root-false ones skipped).
  auto for_lits = [&](uint32_t c, auto&& f) {
    if (c < nlong) {
      const Clause& cl = clause(refs[c]);
      const Lit* l = cl.lits();
      for (uint32_t k = 0; k < cl.size; ++k) {
        if (!vals_[l[k]]) f(l[k]);
      }
    } else {
      const Lit* b = bins.data() + 2 * size_t{c - nlong};
      f(b[0]);
      if (b[1] != kNoLit) f(b[1]);
    }
  };
  // Occurrence lists (CSR).
  const size_t nlits2 = 2 * size_t{num_vars_};
  std::vector<uint32_t> occ_start(nlits2 + 1, 0), occ(nlits);
  for (uint32_t c = 0; c < nclauses; ++c) for_lits(c, [&](Lit l) { ++occ_start[l + 1]; });
  for (size_t l = 0; l < nlits2; ++l) occ_start[l + 1] += occ_start[l];
  {
    std::vector<uint32_t> fill(occ_start.begin(), occ_start.end() - 1);
    for (uint32_t c = 0; c < nclauses; ++c) for_lits(c, [&](Lit l) { occ[fill[l]++] = c; });
  }
  // Assignment from the saved phases, or with --walkfrom=1 from the phases the next decisions
  // would take (root values for fixed variables).
  std::vector<int8_t> value(nlits2, 0);  // per literal: 1 true, 0 false
  const bool from_target = opts_.walkfrom && (opts_.target == 2 || (opts_.target == 1 && stable_));
  for (Var v = 0; v < num_vars_; ++v) {
    const int8_t root = vals_[make_lit(v, false)];
    const int8_t phase = from_target && target_[v] ? target_[v] : saved_[v];
    const bool pos = root ? root > 0 : phase > 0;
    value[make_lit(v, false)] = pos;
    value[make_lit(v, true)] = !pos;
  }
  // Per clause: the number of true literals and their XOR, side by side (a flip reads and writes
  // both for every occurrence it visits).
  struct ClauseState {
    uint32_t sat = 0, true_xor = 0;
  };
  std::vector<ClauseState> state;  // (ProbSAT; the DDFW walk keeps its own, with the weights)
  std::vector<uint32_t> unsat, unsat_pos(nclauses, UINT32_MAX);
  auto make_unsat = [&](uint32_t c) {
    unsat_pos[c] = static_cast<uint32_t>(unsat.size());
    unsat.push_back(c);
  };
  auto make_sat = [&](uint32_t c) {
    const uint32_t pos = unsat_pos[c], last = unsat.back();
    unsat[pos] = last;
    unsat_pos[last] = pos;
    unsat.pop_back();
    unsat_pos[c] = UINT32_MAX;
  };

  const uint64_t search = stats_.ticks - walk_last_ticks_;
  const uint64_t share = static_cast<uint64_t>(static_cast<double>(search) * opts_.walkeffort / 1000.0);
  uint64_t limit = std::max<uint64_t>(share, 2 * nlits);
  uint64_t effort = nlits / 4;
  size_t best = 0;
  std::vector<int8_t> best_value;
  Rng rng{static_cast<uint64_t>(opts_.seed) * 0x9E3779B97F4A7C15ull + stats_.walks + 1};
  // -v -v -v: the fewest unsatisfied clauses as a function of the effort (quality per tick)
  const bool tracing = opts_.verbose >= 3;
  std::vector<std::pair<uint64_t, size_t>> trace;

  // DDFW from the assignment in `value` (see the top of the file); sets best, best_value and
  // effort. Weights in units of 1/100 of the papers' weights.
  auto ddfw = [&](bool linear) {
    std::fill(unsat_pos.begin(), unsat_pos.end(), UINT32_MAX);
    unsat.clear();
    constexpr uint32_t kInit = 800;               // w0 = 8
    constexpr uint64_t kSidewaysPerMille = 150;   // spt = 0.15
    const uint64_t random_donor = linear ? 100 : 10;  // cspt per mille: 0.1 / 0.01
    constexpr size_t kChoice = 64;                // candidates scanned or drawn per flip
    constexpr uint32_t kNeighbours = 256;         // occurrences read per literal for a donor
    constexpr int kDonorTries = 16;               // random clauses tried for a random donor
    // Per clause the counters of ClauseState and the weight; per variable the score and the
    // position in the list of variables with a positive score (one cache line per access).
    struct DState {
      uint32_t sat, true_xor, weight;
    };
    struct DVar {
      int64_t score;
      uint32_t pos;
    };
    std::vector<DState> ds(nclauses, DState{0, 0, kInit});
    std::vector<DVar> dv(num_vars_, DVar{0, UINT32_MAX});
    std::vector<uint32_t> good;  // variables with score > 0
    auto update = [&](Var u) {
      const bool is_good = dv[u].score > 0, listed = dv[u].pos != UINT32_MAX;
      if (is_good == listed) return;
      if (is_good) {
        dv[u].pos = static_cast<uint32_t>(good.size());
        good.push_back(u);
      } else {
        const uint32_t pos = dv[u].pos, last = good.back();
        good[pos] = last;
        dv[last].pos = pos;
        good.pop_back();
        dv[u].pos = UINT32_MAX;
      }
    };
    for (uint32_t c = 0; c < nclauses; ++c) {
      DState& cs = ds[c];
      for_lits(c, [&](Lit l) {
        if (value[l]) {
          ++cs.sat;
          cs.true_xor ^= l;
        }
      });
      if (!cs.sat) {
        make_unsat(c);
        for_lits(c, [&](Lit l) { dv[var_of(l)].score += kInit; });
      } else if (cs.sat == 1) {
        dv[var_of(cs.true_xor)].score -= kInit;
      }
    }
    // (input order: the same list after a renumbering)
    for (Var i = 0; i < num_vars_; ++i) update(internal_var(i));
    best = unsat.size();
    best_value = value;
    if (tracing) trace.emplace_back(effort, best);
    // The best assignment is kept lazily: best_value plus the first best_flips of the flips logged
    // since. A greedy descent improves at almost every flip, and a copy of the assignment for each
    // improvement made the walk on station-repacking (317k clauses, 42k unsatisfied at the start)
    // a sequence of copies. The log is folded into best_value when it outgrows a cap, and dropped
    // when the flips since the best alone do (the next improvement copies the assignment then).
    std::vector<Var> flipped;
    size_t best_flips = 0;
    bool logging = true;
    const size_t log_cap = std::max<size_t>(1024, num_vars_ / 8);
    auto fold = [&]() -> uint64_t {  // best_value := the best assignment; returns the flips applied
      for (size_t k = 0; k < best_flips; ++k) {
        const Var u = flipped[k];
        best_value[make_lit(u, false)] ^= 1;
        best_value[make_lit(u, true)] ^= 1;
      }
      flipped.erase(flipped.begin(), flipped.begin() + static_cast<std::ptrdiff_t>(best_flips));
      const uint64_t applied = best_flips;
      best_flips = 0;
      return applied;
    };

    // Flips variable v; returns the clause literals and occurrences visited.
    auto flip = [&](Var v) -> uint64_t {
      const Lit f = value[make_lit(v, false)] ? make_lit(v, true) : make_lit(v, false), t = negate(f);
      value[f] = 1;
      value[t] = 0;
      if (logging) flipped.push_back(v);
      uint64_t visited = occ_start[f + 1] - occ_start[f] + occ_start[t + 1] - occ_start[t];
      for (uint32_t o = occ_start[f], oe = occ_start[f + 1]; o < oe; ++o) {
        const uint32_t d = occ[o];
        DState& cs = ds[d];
        const uint32_t before = cs.sat++;
        const int64_t w = cs.weight;
        if (before == 0) {  // satisfied now, by f alone: no literal of d makes it any more
          for_lits(d, [&](Lit l) {
            dv[var_of(l)].score -= w;
            update(var_of(l));
            ++visited;
          });
          dv[v].score -= w;  // and v breaks it
          make_sat(d);
        } else if (before == 1) {  // its single true literal no longer breaks it
          const Var u = var_of(cs.true_xor);
          dv[u].score += w;
          update(u);
        }
        cs.true_xor ^= f;
      }
      for (uint32_t o = occ_start[t], oe = occ_start[t + 1]; o < oe; ++o) {
        const uint32_t d = occ[o];
        DState& cs = ds[d];
        cs.true_xor ^= t;
        const uint32_t after = --cs.sat;
        const int64_t w = cs.weight;
        if (after == 0) {  // unsatisfied now: every literal of d makes it, v no longer breaks it
          for_lits(d, [&](Lit l) {
            dv[var_of(l)].score += w;
            update(var_of(l));
            ++visited;
          });
          dv[v].score += w;
          make_unsat(d);
        } else if (after == 1) {  // the remaining true literal breaks it now
          const Var u = var_of(cs.true_xor);
          dv[u].score -= w;
          update(u);
        }
      }
      update(v);
      ++stats_.walk_flips;
      return visited;
    };
    // Moves weight to every unsatisfied clause from a satisfied one; returns occurrences and
    // literals visited.
    auto transfer = [&]() -> uint64_t {
      uint64_t visited = 0;
      for (const uint32_t c : unsat) {
        uint32_t donor = UINT32_MAX, heaviest = 0;
        if (rng.next() % 1000 >= random_donor) {
          for_lits(c, [&](Lit l) {  // neighbours: the other clauses of l (false in all of them)
            const uint32_t begin = occ_start[l], n = occ_start[l + 1] - begin;
            const uint32_t m = std::min(n, kNeighbours);
            const uint32_t offset = n > kNeighbours ? static_cast<uint32_t>(rng.next() % n) : 0;
            for (uint32_t k = 0; k < m; ++k) {
              const uint32_t j = offset + k;
              const uint32_t d = occ[begin + (j < n ? j : j - n)];
              if (ds[d].sat && ds[d].weight > heaviest) {
                heaviest = ds[d].weight;
                donor = d;
              }
            }
            visited += m + 1;
          });
        }
        if (donor == UINT32_MAX || heaviest < kInit) {
          donor = UINT32_MAX;
          for (int k = 0; k < kDonorTries && donor == UINT32_MAX; ++k) {
            const uint32_t d = static_cast<uint32_t>(rng.next() % nclauses);
            if (ds[d].sat && ds[d].weight >= kInit) donor = d;
          }
          visited += kDonorTries;
          if (donor == UINT32_MAX) continue;
        }
        const uint32_t w = ds[donor].weight;
        const uint32_t amount = linear ? (w > kInit ? w / 20 + 100 : w / 10 + 200) : (w > kInit ? 200 : 100);
        if (ds[c].weight > UINT32_MAX - amount) continue;  // (never on formulas below 5M clauses)
        ds[donor].weight = w - amount;
        if (ds[donor].sat == 1) {  // its single true literal breaks less weight
          const Var u = var_of(ds[donor].true_xor);
          dv[u].score += amount;
          update(u);
        }
        ds[c].weight += amount;
        for_lits(c, [&](Lit l) {  // every literal of c makes more weight
          dv[var_of(l)].score += amount;
          update(var_of(l));
          ++visited;
        });
        ++stats_.walk_transfers;
      }
      return visited;
    };

    std::vector<Var> drawn;
    while (!unsat.empty() && effort < limit && !stop_requested()) {
      uint64_t visited = 0;
      if (!good.empty()) {
        const size_t n = good.size();
        drawn.clear();
        if (n <= kChoice) {  // all of them, from a random start (ties: the first one)
          const size_t start = rng.next() % n;
          for (size_t k = 0; k < n; ++k) drawn.push_back(good[start + k < n ? start + k : start + k - n]);
        } else {
          for (size_t k = 0; k < kChoice; ++k) drawn.push_back(good[rng.next() % n]);
        }
        Var pick = drawn[0];
        if (!linear) {
          for (const Var u : drawn) {
            if (dv[u].score > dv[pick].score) pick = u;
          }
        } else {  // with probability proportional to the score
          uint64_t sum = 0;
          for (const Var u : drawn) sum += static_cast<uint64_t>(dv[u].score);
          uint64_t r = rng.next() % sum;
          for (const Var u : drawn) {
            const uint64_t s = static_cast<uint64_t>(dv[u].score);
            if (r < s) {
              pick = u;
              break;
            }
            r -= s;
          }
        }
        visited += drawn.size() + flip(pick);
      } else {
        // A sideways move: a variable of a random unsatisfied clause whose flip leaves the
        // weighted cost unchanged.
        Var sideways = UINT32_MAX;
        if (rng.next() % 1000 < kSidewaysPerMille) {
          const uint32_t c = unsat[rng.next() % unsat.size()];
          for_lits(c, [&](Lit l) {
            if (sideways == UINT32_MAX && dv[var_of(l)].score == 0) sideways = var_of(l);
            ++visited;
          });
        }
        visited += sideways != UINT32_MAX ? flip(sideways) : transfer();
      }
      if (unsat.size() < best) {
        best = unsat.size();
        if (logging) {
          best_flips = flipped.size();
        } else {
          best_value = value;
          effort += num_vars_ / 16;
          logging = true;
        }
      }
      if (flipped.size() > log_cap) {
        visited += fold();
        if (flipped.size() > log_cap / 2) {  // no improvement for a while: stop logging
          flipped.clear();
          logging = false;
        }
      }
      effort += visited / 4 + 1;
      if (tracing && trace.back().second != best) trace.emplace_back(effort, best);
    }
    if (logging) fold();
    if (opts_.invariants) {  // the cached counters and scores agree with a recomputation
      std::vector<int64_t> check(num_vars_, 0);
      uint64_t total = 0;
      for (uint32_t c = 0; c < nclauses; ++c) {
        uint32_t n = 0, x = 0;
        for_lits(c, [&](Lit l) {
          if (value[l]) {
            ++n;
            x ^= l;
          }
        });
        if (n != ds[c].sat || (n == 1 && x != ds[c].true_xor) || ((n == 0) != (unsat_pos[c] != UINT32_MAX))) {
          std::fprintf(stderr, "c DEBUG walk: clause %u counters wrong\n", c);
          std::abort();
        }
        if (!n) for_lits(c, [&](Lit l) { check[var_of(l)] += ds[c].weight; });
        if (n == 1) check[var_of(x)] -= ds[c].weight;
        total += ds[c].weight;
      }
      bool ok = total == uint64_t{kInit} * nclauses;
      for (Var v = 0; v < num_vars_; ++v) ok = ok && check[v] == dv[v].score && (dv[v].score > 0) == (dv[v].pos != UINT32_MAX);
      // the lazily kept best assignment has `best` unsatisfied clauses, and the logged flips lead
      // from it to the current one
      size_t unsat_best = 0;
      for (uint32_t c = 0; c < nclauses; ++c) {
        bool sat = false;
        for_lits(c, [&](Lit l) { sat = sat || best_value[l]; });
        unsat_best += !sat;
      }
      ok = ok && unsat_best == best;
      if (logging) {
        std::vector<int8_t> replay(best_value);
        for (const Var u : flipped) {
          replay[make_lit(u, false)] ^= 1;
          replay[make_lit(u, true)] ^= 1;
        }
        ok = ok && replay == value;
      }
      if (!ok) {
        std::fprintf(stderr, "c DEBUG walk: scores or weights wrong\n");
        std::abort();
      }
    }
  };
  if (opts_.walkmode == 1 || opts_.walkmode == 2) {
    ddfw(opts_.walkmode == 2);
  } else {
    // ProbSAT. (eight spare entries after the variables' break values: see the flips)
    state.assign(nclauses, ClauseState{});
    std::vector<uint32_t> breaks(num_vars_ + 8, 0);
    for (uint32_t c = 0; c < nclauses; ++c) {
      ClauseState& cs = state[c];
      for_lits(c, [&](Lit l) {
        if (value[l]) {
          ++cs.sat;
          cs.true_xor ^= l;
        }
      });
      if (!cs.sat) {
        make_unsat(c);
      } else if (cs.sat == 1) {
        ++breaks[var_of(cs.true_xor)];
      }
    }
    double avg = static_cast<double>(nlits) / nclauses;
    const double cb = avg <= 3 ? 2.06 : avg <= 4 ? 3.0 : avg <= 5 ? 3.7 : avg <= 6 ? 5.1 : 5.4;
    std::vector<double> table(64);
    for (size_t b = 0; b < table.size(); ++b) table[b] = std::pow(cb, -static_cast<double>(b));

    best = unsat.size();
    best_value = value;
    if (tracing) trace.emplace_back(effort, best);
    std::vector<double> prob;
    std::vector<Lit> cand;
    while (!unsat.empty() && effort < limit && !stop_requested()) {
      const uint32_t c = unsat[rng.next() % unsat.size()];
      cand.clear();
      prob.clear();
      double sum = 0;
      for_lits(c, [&](Lit l) {  // false now; flipping makes it true and its negation false
        const double p = table[std::min<size_t>(breaks[var_of(l)], table.size() - 1)];
        cand.push_back(l);
        prob.push_back(p);
        sum += p;
      });
      effort += cand.size() / 4 + 1;
      double r = rng.uniform() * sum;
      size_t pick = 0;
      while (pick + 1 < cand.size() && r >= prob[pick]) r -= prob[pick++];
      const Lit f = cand[pick], t = negate(f);
      value[f] = 1;
      value[t] = 0;
      const Var fv = var_of(f);
      // Becoming unsatisfied or satisfied is rare and branches; the break update of the single
      // true literal (one or two true literals before / after) is frequent and unpredictable on
      // short clauses, so it is done without a branch: with any other count it adds 0 to one of
      // the eight spare entries (several of them: one would chain every update through memory,
      // which cost a fifth of the walk on formulas where the branch is predictable).
      uint32_t* const br = breaks.data();
      ClauseState* const st = state.data();
      const uint32_t* const oc = occ.data();
      for (uint32_t o = occ_start[f], oe = occ_start[f + 1]; o < oe; ++o) {
        const uint32_t d = oc[o];
        ClauseState& cs = st[d];
        const uint32_t before = cs.sat++;
        if (before == 0) {
          ++br[fv];  // f is the only true literal of d now
          make_sat(d);
        } else {
          const uint32_t one = before == 1 ? 1u : 0u;  // its single true literal is no longer critical
          br[one * var_of(cs.true_xor) + (one ^ 1u) * (num_vars_ + (o & 7u))] -= one;
        }
        cs.true_xor ^= f;
      }
      for (uint32_t o = occ_start[t], oe = occ_start[t + 1]; o < oe; ++o) {
        const uint32_t d = oc[o];
        ClauseState& cs = st[d];
        cs.true_xor ^= t;
        const uint32_t after = --cs.sat;
        if (after == 0) {
          --br[fv];  // t was the only true literal
          make_unsat(d);
        } else {
          const uint32_t one = after == 1 ? 1u : 0u;  // the remaining true literal is critical now
          br[one * var_of(cs.true_xor) + (one ^ 1u) * (num_vars_ + (o & 7u))] += one;
        }
      }
      effort += (occ_start[f + 1] - occ_start[f] + occ_start[t + 1] - occ_start[t]) / 4 + 1;
      ++stats_.walk_flips;
      if (unsat.size() < best) {
        best = unsat.size();
        best_value = value;
        effort += num_vars_ / 16;
        if (tracing) trace.emplace_back(effort, best);
      }
    }
    if (opts_.invariants) {  // the cached counters agree with a recomputation
      std::vector<uint32_t> check(num_vars_, 0);
      for (uint32_t c = 0; c < nclauses; ++c) {
        uint32_t n = 0, x = 0;
        for_lits(c, [&](Lit l) {
          if (value[l]) {
            ++n;
            x ^= l;
          }
        });
        if (n != state[c].sat || (n == 1 && x != state[c].true_xor) || ((n == 0) != (unsat_pos[c] != UINT32_MAX))) {
          std::fprintf(stderr, "c DEBUG walk: clause %u counters wrong\n", c);
          std::abort();
        }
        if (n == 1) ++check[var_of(x)];
      }
      if (!std::equal(check.begin(), check.end(), breaks.begin())) {
        std::fprintf(stderr, "c DEBUG walk: break values wrong\n");
        std::abort();
      }
    }
  }
  if (best == 0) ++stats_.walk_models;
  // --walkrecord: a walk that ends above the best earlier walk's minimum found a worse region
  // than one already handed to the search; the search's own phases are kept then.
  const bool adopt = !opts_.walkrecord || best <= walk_record_;
  if (adopt) {
    walk_record_ = best;
    for (Var v = 0; v < num_vars_; ++v) {
      if (!vals_[make_lit(v, false)]) saved_[v] = best_value[make_lit(v, false)] ? 1 : -1;
    }
  } else {
    ++stats_.walks_kept;
  }
  stats_.walk_ticks += effort;
  walk_last_ticks_ = stats_.ticks;
  if (opts_.verbose >= 2) {
    std::printf("c [%.2f s] walk: %u clauses, best %zu unsatisfied%s\n", seconds(), nclauses, best,
                adopt ? "" : " (not adopted)");
  }
  auto print_trace = [&](int mode, double start) {  // the best count within 2^k ticks (k >= 10)
    std::printf("c walk trace (mode %d, %.3f s, %llu ticks):", mode, seconds() - start,
                static_cast<unsigned long long>(effort));
    size_t at = 0;
    for (uint64_t mark = 1024;; mark *= 2) {
      while (at + 1 < trace.size() && trace[at + 1].first <= mark) ++at;
      std::printf(" %llu:%zu", static_cast<unsigned long long>(mark), trace[at].second);
      if (mark >= effort) break;
    }
    std::printf("\n");
  };
  if (tracing) print_trace(opts_.walkmode == 3 ? 0 : static_cast<int>(opts_.walkmode), walk_start);
  // --walkmode=3: the ProbSAT walk has set the phases as with --walkmode=0; the walk of mode 2
  // continues from its best assignment, with the same budget, for a model only (its assignment
  // is dropped otherwise, so the search is the one of --walkmode=0 unless a model is found).
  if (opts_.walkmode == 3 && best != 0) {
    // --walkmodel=1: the model walk is near a model when the ProbSAT walk's minimum or the last
    // model walk's is at most sqrt(clauses) (x walkmodelnear %), else far. Near, it gets the
    // budget above; far, it backs off: after the k-th far model walk in a row the next 2^k - 1
    // calls skip it, and the others get the share of the search ticks only (no floor of 2 x
    // literals; no walk when the share does not pay for the set-up). --walkmodel=2: near walks
    // also get the share only, unless the last model walk ended below every earlier one or the
    // ProbSAT walk did (or no model walk ran yet).
    bool run = true, nearby = true;
    if (opts_.walkmodel) {
      const double scale = std::sqrt(static_cast<double>(nclauses)) * opts_.walkmodelnear / 100.0;
      nearby = static_cast<double>(best) <= scale || static_cast<double>(walk_model_last_) <= scale;
      const bool improved = walk_model_improved_ || best < walk_model_phase_best_;
      walk_model_phase_best_ = std::min(walk_model_phase_best_, best);
      if (nearby) {
        walk_model_far_ = 0;
        walk_model_skip_ = 0;
        if (opts_.walkmodel == 2 && !improved) limit = share;
      } else {
        limit = share;
        if (walk_model_skip_) {
          --walk_model_skip_;
          run = false;
        }
      }
      if (limit <= nlits / 2) run = false;
    }
    if (!run) {
      ++stats_.model_walks_skipped;
      if (opts_.verbose >= 2) std::printf("c [%.2f s] walk for a model skipped (%s)\n", seconds(), nearby ? "near" : "far");
    } else {
      const double start = tracing ? seconds() : 0;
      value = best_value;
      effort = nlits / 4;
      trace.clear();
      ddfw(true);
      ++stats_.model_walks;
      stats_.model_walk_ticks += effort;
      stats_.walk_ticks += effort;
      if (best == 0) ++stats_.walk_models;
      if (opts_.walkmodel) {
        walk_model_last_ = best;
        walk_model_improved_ = best < walk_model_best_;
        walk_model_best_ = std::min(walk_model_best_, best);
        if (!nearby) {
          walk_model_far_ = std::min<uint32_t>(walk_model_far_ + 1, 32);
          walk_model_skip_ = (uint64_t{1} << walk_model_far_) - 1;
        }
      }
      if (opts_.verbose >= 2) {
        std::printf("c [%.2f s] walk for a model: best %zu unsatisfied (%llu ticks of %llu, share %llu, literals %zu)\n",
                    seconds(), best, static_cast<unsigned long long>(effort), static_cast<unsigned long long>(limit),
                    static_cast<unsigned long long>(share), nlits);
      }
      if (tracing) print_trace(2, start);
    }
  }
  if (best != 0 || !opts_.walkmode) return;
  // A model of the walk clauses: decided variable by variable (input order) with propagation, as
  // the lucky pass does. Propagation through a learned clause the model falsifies could force
  // other values, so every walk clause is checked again on the final trail.
  bool ok = true;
  for (Var i = 0; i < num_vars_ && ok; ++i) {
    const Var v = internal_var(i);
    if (eliminated_[v] || vals_[make_lit(v, false)] != 0) continue;
    control_.push_back(static_cast<uint32_t>(trail_.size()));
    assign(make_lit(v, !best_value[make_lit(v, false)]), kNoReason);
    ok = propagate_vivify(kNoReason);
  }
  ok = ok && trail_.size() + inactive_ == num_vars_;
  for (uint32_t c = 0; c < nlong && ok; ++c) {
    const Clause& cl = clause(refs[c]);
    ok = std::any_of(cl.lits(), cl.lits() + cl.size, [&](Lit l) { return vals_[l] > 0; });
  }
  for (size_t k = 0; k < bins.size() && ok; k += 2) ok = vals_[bins[k]] > 0 || (bins[k + 1] != kNoLit && vals_[bins[k + 1]] > 0);
  if (opts_.verbose) std::printf("c [%.2f s] walk found a model%s\n", seconds(), ok ? "" : " (propagation disagrees: kept as phases)");
  if (!ok) backtrack(0);
}

}  // namespace psat
