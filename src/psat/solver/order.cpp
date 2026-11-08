// Initial focused-mode decision order (--queueorder).
//
// The focused-mode queue picks the most recently enqueued variable, so by default the highest
// input index is decided first. Circuit encodings number the inputs first and the gate outputs
// after them; deciding the inputs first propagates through the circuit (asconhash: 1.0 decision
// and 26k propagations per conflict focused-only, against 10.7 and 250). --queueorder=1 turns the
// initial order around for every formula. On sc2026 at 300 s that gained asconhash and lost
// about as many satisfiable instances as it gained (two runs, 79 = 79 and 79 against 81).
//
// The other values apply the lowest-first order only where the formula says that it fits, or
// only for part of the search:
//   2  AND gates o = AND(x1..xk) found in the input (binary clauses (-o v xi) and the base clause
//      (o v -x1 v .. v -xk)): lowest first if enough of the variables are gate outputs and most
//      outputs have a higher input index than all their inputs (gates_forward()). The choice is
//      made before the search: the search is exactly that of 0 or that of 1. On the two sc2026
//      box pairs (300 s) it keeps asconhash and changes nothing outside its 42 instances: 80 and
//      80 against 79 and 81 (PLAN.md, branch order3).
//   3  as 2, lowest first in the first focused phase only (as 4);
//   4  lowest first in the first focused phase; from the second focused phase on, the variables
//      not bumped by then get the default order back (queue_default_order_unbumped()).
//      asconhash keeps the gain of 1: the first phase sets it. A later switch to lowest first
//      does not: after 300 conflicts in the default order, asconhash was no longer refuted.

#include <algorithm>

#include "psat/solver/solver.hpp"

namespace psat {

void Solver::initial_queue_order() {
  queue_ordered_ = true;
  const int64_t q = opts_.queueorder;
  const bool lowest = q == 2 || q == 3 ? gates_forward() : true;
  if (!lowest) return;
  queue_lowest_first();
  order_stamp_ = queue_stamp_;
  order_revert_ = q == 3 || q == 4;
}

// Rebuilds the queue in input index order, lowest index decided first (by input index: the same
// order after a renumbering).
void Solver::queue_lowest_first() {
  std::vector<Var> order;
  order.reserve(num_vars_);
  for (Var v = queue_first_; v != UINT32_MAX; v = links_[v].next) order.push_back(v);
  std::sort(order.begin(), order.end(),
            [this](Var a, Var b) { return external_lit(make_lit(a, false)) > external_lit(make_lit(b, false)); });
  for (const Var v : order) queue_dequeue(v);
  for (const Var v : order) queue_enqueue_last(v);
  queue_search_ = queue_last_;
}

// AND definitions in the irredundant clauses and the direction of their numbering. For each long
// clause C and each literal o of C, C is the base clause of o = AND(-y for y in C, y != o) when
// every (-o v -y) is a binary clause. Each (clause, output literal) pair counts once; forward:
// the output's input index is above all of its inputs', backward: below all of them. The binary
// clauses are sorted per literal and looked up by bisection, from the clause's literals (a
// literal fails on its first missing binary clause); the scan stops after `budget` steps.
Solver::GateDirection Solver::gate_direction(uint64_t budget) {
  GateDirection d;
  const size_t nlits = 2 * size_t{num_vars_};
  std::vector<uint32_t> start(nlits + 1, 0);
  std::vector<Lit> bin;
  for (Lit a = 0; a < nlits; ++a) {
    for (const Watch& w : watches_[a]) start[a + 1] += w.binary() && !w.redundant_binary();
  }
  for (size_t l = 0; l < nlits; ++l) start[l + 1] += start[l];
  bin.resize(start[nlits]);
  for (Lit a = 0; a < nlits; ++a) {
    uint32_t k = start[a];
    for (const Watch& w : watches_[a]) {
      if (w.binary() && !w.redundant_binary()) bin[k++] = w.blit;
    }
    std::sort(bin.begin() + start[a], bin.begin() + start[a + 1]);
  }
  d.work = bin.size();
  std::vector<uint8_t> output(num_vars_, 0);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    const Lit* l = c.lits();
    for (uint32_t k = 0; k < c.size; ++k) {
      const Lit no = negate(l[k]);  // output l[k]: binary clauses (-l[k] v -l[m]) for the others
      if (start[no + 1] - start[no] + 1 < c.size) continue;
      const auto first = bin.begin() + start[no], last = bin.begin() + start[no + 1];
      bool gate = true;
      for (uint32_t m = 0; m < c.size && gate; ++m) {
        ++d.work;
        gate = m == k || std::binary_search(first, last, negate(l[m]));
      }
      if (!gate) continue;
      ++d.gates;
      output[var_of(no)] = 1;
      const Lit out = external_lit(l[k]) >> 1;
      Lit lo = UINT32_MAX, hi = 0;
      for (uint32_t m = 0; m < c.size; ++m) {
        if (m == k) continue;
        const Lit in = external_lit(l[m]) >> 1;
        lo = std::min(lo, in);
        hi = std::max(hi, in);
      }
      if (out > hi) ++d.forward;
      if (out < lo) ++d.backward;
    }
    if (d.work > budget) {
      d.complete = false;
      break;
    }
  }
  for (Var v = 0; v < num_vars_; ++v) d.outputs += output[v];
  return d;
}

// --queueorder=2 / 3: at least --queueordergates per mille of the variables are AND gate outputs
// and at least --queueorderforward per mille of the gates have their output numbered after all of
// their inputs. (sc2026: 42 of 168 instances; asconhash 12% / 100%, korf 90% / 95%; antibandwidth
// 24% with 98% backward; cyclic antibandwidth 96% with 61% / 39%; exactly-one groups are AND
// gates both ways. The scan takes at most 0.11 s, on T90's 3.1M variables.)
bool Solver::gates_forward() {
  const double start = seconds();
  const GateDirection d = gate_direction(20 * (arena_.size() + num_vars_) + 1000000);
  const bool forward = d.complete && d.gates &&
                       d.outputs * 1000 >= static_cast<uint64_t>(opts_.queueordergates) * num_vars_ &&
                       d.forward * 1000 >= static_cast<uint64_t>(opts_.queueorderforward) * d.gates;
  if (opts_.verbose) {
    std::printf("c queueorder: %llu AND gates (%llu outputs, %.1f%% of %u variables), forward %llu, backward %llu, work %llu%s, %.3f s: %s\n",
                static_cast<unsigned long long>(d.gates), static_cast<unsigned long long>(d.outputs),
                100.0 * static_cast<double>(d.outputs) / std::max(1u, num_vars_), num_vars_,
                static_cast<unsigned long long>(d.forward), static_cast<unsigned long long>(d.backward),
                static_cast<unsigned long long>(d.work), d.complete ? "" : " (incomplete)", seconds() - start,
                forward ? "lowest index first" : "highest index first");
  }
  return forward;
}

// --queueorder=3 / 4, at the start of the second focused phase: the variables not bumped since
// the lowest-first order was set get the default order back (the highest index decided first), in
// front of the bumped ones, which keep their order.
void Solver::queue_default_order_unbumped() {
  std::vector<Var> unbumped, bumped;
  for (Var v = queue_first_; v != UINT32_MAX; v = links_[v].next) {
    (bumped_[v] > order_stamp_ ? bumped : unbumped).push_back(v);
  }
  std::sort(unbumped.begin(), unbumped.end(), [this](Var a, Var b) {
    return external_lit(make_lit(a, false)) < external_lit(make_lit(b, false));  // (the last enqueued is decided first)
  });
  for (Var v = queue_first_; v != UINT32_MAX;) {
    const Var next = links_[v].next;
    queue_dequeue(v);
    v = next;
  }
  for (const Var v : unbumped) queue_enqueue_last(v);
  for (const Var v : bumped) queue_enqueue_last(v);
  queue_search_ = queue_last_;
}

}  // namespace psat
