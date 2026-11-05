// "Lucky" assignments before search (as in Kissat): many formulas are satisfied by a trivial
// pattern. Each attempt decides the variables in a fixed order and polarity, propagating after
// every decision, without learning; a conflict abandons the attempt (backtrack to the root).
// Patterns: forward / backward variable order with all-false / all-true decisions. A success
// leaves a complete assignment on the trail, and search() reports SAT right away.

#include "psat/solver/solver.hpp"

namespace psat {

bool Solver::lucky() {
  const PassTimer pass_timer(*this, kPassLucky);
  if (inconsistent_ || level() > 0) return false;
  if (!propagate_vivify(kNoReason)) return false;  // root conflicts are left to search
  for (int attempt = 0; attempt < 4; ++attempt) {
    const bool backward = attempt & 1;
    const bool negative = attempt < 2;
    bool ok = true;
    for (Var i = 0; i < num_vars_ && ok; ++i) {
      const Var v = backward ? num_vars_ - 1 - i : i;
      if (eliminated_[v] || vals_[make_lit(v, false)] != 0) continue;
      control_.push_back(static_cast<uint32_t>(trail_.size()));
      assign(make_lit(v, negative), kNoReason);
      ok = propagate_vivify(kNoReason);
      if (stats_.vivify_ticks > lucky_limit_) ok = false;
    }
    if (ok && trail_.size() + inactive_ == num_vars_) {
      ++stats_.lucky;
      return true;
    }
    backtrack(0);
  }
  return false;
}

}  // namespace psat
