// Local search for phases ("walk" rephasing, as in Kissat): a ProbSAT walk (Balint & Schoening
// 2012) over the irredundant clauses, root-simplified, starting from the saved phases. The
// assignment with the fewest unsatisfied clauses seen becomes the saved phases. Effort is a share
// of the search ticks since the last walk, counted in occurrences visited.
//
// ProbSAT: pick a random unsatisfied clause, flip one of its variables chosen with probability
// proportional to cb^-break, where break is the number of clauses that would become unsatisfied
// and cb depends on the average clause length (2.06 for 3-SAT, larger for longer clauses).

#include <algorithm>
#include <cmath>

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
  ++stats_.walks;
  if (level() > 0) backtrack(0);
  // Root-simplified irredundant clauses in CSR form.
  std::vector<uint32_t> start;
  std::vector<Lit> lits;
  start.push_back(0);
  auto add = [&](const Lit* cl, uint32_t n) {
    const size_t before = lits.size();
    for (uint32_t k = 0; k < n; ++k) {
      const int8_t v = vals_[cl[k]];
      if (v > 0) {
        lits.resize(before);
        return;
      }
      if (v == 0) lits.push_back(cl[k]);
    }
    if (lits.size() == before) return;  // falsified at the root: cannot happen after propagation
    start.push_back(static_cast<uint32_t>(lits.size()));
  };
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant) add(c.lits(), c.size);
  }
  for (Lit l = 0; l < 2 * num_vars_; ++l) {
    for (const Watch& w : watches_[l]) {
      if (w.binary() && !w.redundant_binary() && l < w.blit) {
        const Lit b[2] = {l, w.blit};
        add(b, 2);
      }
    }
  }
  const uint32_t nclauses = static_cast<uint32_t>(start.size() - 1);
  if (!nclauses) return;
  // Occurrence lists (CSR).
  const size_t nlits = 2 * size_t{num_vars_};
  std::vector<uint32_t> occ_start(nlits + 1, 0), occ(lits.size());
  for (const Lit l : lits) ++occ_start[l + 1];
  for (size_t l = 0; l < nlits; ++l) occ_start[l + 1] += occ_start[l];
  {
    std::vector<uint32_t> fill(occ_start.begin(), occ_start.end() - 1);
    for (uint32_t c = 0; c < nclauses; ++c) {
      for (uint32_t k = start[c]; k < start[c + 1]; ++k) occ[fill[lits[k]]++] = c;
    }
  }
  // Assignment from the saved phases (root values for fixed variables).
  std::vector<int8_t> value(nlits, 0);  // per literal: 1 true, 0 false
  for (Var v = 0; v < num_vars_; ++v) {
    const int8_t root = vals_[make_lit(v, false)];
    const bool pos = root ? root > 0 : saved_[v] > 0;
    value[make_lit(v, false)] = pos;
    value[make_lit(v, true)] = !pos;
  }
  std::vector<uint32_t> sat(nclauses, 0), unsat, unsat_pos(nclauses, UINT32_MAX);
  for (uint32_t c = 0; c < nclauses; ++c) {
    for (uint32_t k = start[c]; k < start[c + 1]; ++k) sat[c] += value[lits[k]];
    if (!sat[c]) {
      unsat_pos[c] = static_cast<uint32_t>(unsat.size());
      unsat.push_back(c);
    }
  }
  double avg = static_cast<double>(lits.size()) / nclauses;
  const double cb = avg <= 3 ? 2.06 : avg <= 4 ? 3.0 : avg <= 5 ? 3.7 : avg <= 6 ? 5.1 : 5.4;
  std::vector<double> table(64);
  for (size_t b = 0; b < table.size(); ++b) table[b] = std::pow(cb, -static_cast<double>(b));

  const uint64_t search = stats_.ticks - walk_last_ticks_;
  const uint64_t limit = std::max<uint64_t>(static_cast<uint64_t>(static_cast<double>(search) * opts_.walkeffort / 1000.0),
                                            2 * lits.size());
  uint64_t effort = lits.size() / 4;
  size_t best = unsat.size();
  std::vector<int8_t> best_value(value);
  Rng rng{static_cast<uint64_t>(opts_.seed) * 0x9E3779B97F4A7C15ull + stats_.walks + 1};
  std::vector<double> prob;
  std::vector<Lit> cand;
  while (!unsat.empty() && effort < limit) {
    const uint32_t c = unsat[rng.next() % unsat.size()];
    cand.clear();
    prob.clear();
    double sum = 0;
    for (uint32_t k = start[c]; k < start[c + 1]; ++k) {
      const Lit l = lits[k];  // false now; flipping makes it true and its negation false
      const Lit t = negate(l);
      uint32_t brk = 0;
      for (uint32_t o = occ_start[t]; o < occ_start[t + 1]; ++o) brk += sat[occ[o]] == 1;
      effort += (occ_start[t + 1] - occ_start[t]) / 4 + 1;
      const double p = table[std::min<size_t>(brk, table.size() - 1)];
      cand.push_back(l);
      prob.push_back(p);
      sum += p;
    }
    double r = rng.uniform() * sum;
    size_t pick = 0;
    while (pick + 1 < cand.size() && r >= prob[pick]) r -= prob[pick++];
    const Lit f = cand[pick], t = negate(f);
    value[f] = 1;
    value[t] = 0;
    for (uint32_t o = occ_start[f]; o < occ_start[f + 1]; ++o) {
      const uint32_t d = occ[o];
      if (sat[d]++ == 0) {
        const uint32_t pos = unsat_pos[d], last = unsat.back();
        unsat[pos] = last;
        unsat_pos[last] = pos;
        unsat.pop_back();
        unsat_pos[d] = UINT32_MAX;
      }
    }
    for (uint32_t o = occ_start[t]; o < occ_start[t + 1]; ++o) {
      const uint32_t d = occ[o];
      if (--sat[d] == 0) {
        unsat_pos[d] = static_cast<uint32_t>(unsat.size());
        unsat.push_back(d);
      }
    }
    effort += (occ_start[f + 1] - occ_start[f] + occ_start[t + 1] - occ_start[t]) / 4 + 1;
    ++stats_.walk_flips;
    if (unsat.size() < best) {
      best = unsat.size();
      best_value = value;
      effort += num_vars_ / 16;
    }
  }
  for (Var v = 0; v < num_vars_; ++v) {
    if (!vals_[make_lit(v, false)]) saved_[v] = best_value[make_lit(v, false)] ? 1 : -1;
  }
  stats_.walk_ticks += effort;
  walk_last_ticks_ = stats_.ticks;
  if (opts_.verbose >= 2) {
    std::printf("c [%.2f s] walk: %u clauses, best %zu unsatisfied\n", seconds(), nclauses, best);
  }
}

}  // namespace psat
