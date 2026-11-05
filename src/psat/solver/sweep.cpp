// Sweeping (as in Kissat): for a variable v, the environment (clauses within --sweepdepth steps of
// v, at most --sweepvars variables and --sweepclauses clauses) is solved by Kitten. A literal true
// in every model of the environment is implied by the formula (a backbone literal); two literals
// equal in every model are equivalent. Candidates come from the models found and are confirmed by
// Kitten under assumptions; equivalences are added as binary clauses, which substitution merges
// in the next elimination round, and backbone literals as units.
//
// Proofs: the environment consists of irredundant clauses of the formula, so Kitten's learned
// clauses are RUP; they are emitted (in derivation order) before a unit or binary clause derived
// from them, and deleted again when the variable is done.

#include <algorithm>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {
constexpr uint32_t kNotLocal = UINT32_MAX;
constexpr uint64_t kSolveTicks = 20000;  // Kitten ticks per solve
constexpr size_t kBackboneCandidates = 16;
constexpr size_t kEquivalenceCandidates = 8;
constexpr uint64_t kVariableTicks = 500000;  // Kitten ticks per swept variable (sweepclasses)
}  // namespace

void Solver::sweep(uint64_t min_budget) {
  const PassTimer pass_timer(*this, kPassSweep);
  if (inconsistent_ || !opts_.sweep) return;
  const uint64_t search = stats_.ticks - sweep_last_ticks_;
  const uint64_t budget =
      std::max<uint64_t>(static_cast<uint64_t>(static_cast<double>(search) * opts_.sweepeffort / 1000.0), min_budget);
  // The occurrence lists cost about a quarter of the arena: wait until the budget covers twice
  // that (search effort accumulates meanwhile), so that huge formulas are not scanned for nothing.
  if (budget < arena_.size() / 2) return;
  // Sweeps that find nothing double the number of later sweeps skipped (whose search effort is
  // forfeited, so the next sweep is not inflated): on DivS (855k clauses of 11 literals) sweeping
  // found nothing but took as many ticks as the search.
  if (sweep_skip_) {
    --sweep_skip_;
    sweep_last_ticks_ = stats_.ticks;
    return;
  }
  ++stats_.sweeps;
  sweep_last_ticks_ = stats_.ticks;
  const uint64_t found_before = stats_.sweep_units + stats_.sweep_equivalences;
  if (!backtrack_to_root()) return;
  if (sweep_local_.size() < num_vars_) sweep_local_.resize(num_vars_, kNotLocal);
  if (sweep_merged_.size() < num_vars_) sweep_merged_.resize(num_vars_, 0);
  // Occurrence lists (CSR) of the live irredundant long clauses.
  const size_t nlits = 2 * size_t{num_vars_};
  std::vector<uint32_t> start(nlits + 1, 0), occ;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    for (uint32_t k = 0; k < c.size; ++k) ++start[c.lits()[k] + 1];
  }
  for (size_t l = 0; l < nlits; ++l) start[l + 1] += start[l];
  occ.resize(start[nlits]);
  {
    std::vector<uint32_t> fill(start.begin(), start.end() - 1);
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) occ[fill[c.lits()[k]]++] = ref;
    }
  }
  sweep_stamp_.clear();
  sweep_stamp_now_ = 0;
  // Environment limits: with --sweepgrow they grow one step after a full cycle over the
  // variables that found less than one unit or equivalence per 100 swept variables (twice the
  // variables and clauses, one more level of depth up to 3).
  {
    const uint32_t g = opts_.sweepgrow ? sweep_growth_ : 0;
    sweep_lim_vars_ = static_cast<uint32_t>(std::min<uint64_t>(uint64_t{static_cast<uint32_t>(opts_.sweepvars)} << g, 8192));
    sweep_lim_clauses_ =
        static_cast<uint32_t>(std::min<uint64_t>(uint64_t{static_cast<uint32_t>(opts_.sweepclauses)} << g, 32768));
    const uint32_t base_depth = static_cast<uint32_t>(opts_.sweepdepth);
    sweep_lim_depth_ = base_depth >= 3 ? base_depth : std::min<uint32_t>(base_depth + g, 3);
  }
  uint64_t ticks = occ.size() / 4;
  for (uint32_t scanned = 0; scanned < num_vars_ && ticks < budget && !inconsistent_; ++scanned) {
    const Var v = sweep_cursor_++ % num_vars_;
    if (sweep_cursor_ % num_vars_ == 0) {  // a full cycle over the variables ends
      const uint64_t found = stats_.sweep_units + stats_.sweep_equivalences - sweep_cycle_found_;
      if (100 * found < sweep_cycle_swept_ && sweep_growth_ < static_cast<uint32_t>(opts_.sweepgrowmax)) ++sweep_growth_;
      sweep_cycle_found_ = stats_.sweep_units + stats_.sweep_equivalences;
      sweep_cycle_swept_ = 0;
    }
    if (eliminated_[v] || vals_[make_lit(v, false)] != 0) continue;
    const Lit p = make_lit(v, false), n = make_lit(v, true);
    if (start[p + 1] == start[p] && start[n + 1] == start[n]) continue;  // only binary occurrences
    ++stats_.swept_vars;
    ++sweep_cycle_swept_;
    if (!sweep_variable(v, start, occ, ticks)) break;
  }
  stats_.sweep_ticks += ticks;
  const bool productive = stats_.sweep_units + stats_.sweep_equivalences != found_before;
  sweep_delay_ = productive ? 0 : std::min<uint32_t>(2 * sweep_delay_ + 1, 64);
  sweep_skip_ = sweep_delay_;
}

// Emits Kitten's new learned clauses to the proof.
void Solver::sweep_emit_learned() {
  for (; sweep_emitted_ < kitten_.num_learned(); ++sweep_emitted_) {
    const uint32_t size = kitten_.learned_size(sweep_emitted_);
    const Kitten::KLit* kl = kitten_.learned_lits(sweep_emitted_);
    const size_t at = sweep_emitted_lits_.size();
    sweep_emitted_lits_.push_back(size);
    for (uint32_t i = 0; i < size; ++i) {
      sweep_emitted_lits_.push_back(make_lit(sweep_env_[kl[i] >> 1], (kl[i] & 1u) != 0));
    }
    if (proof_) proof_->add(sweep_emitted_lits_.data() + at + 1, size);
  }
}

// Adds a clause implied by the formula (after its Kitten derivation was emitted): units are
// assigned and propagated at the root, binary clauses added as irredundant. False on a conflict.
bool Solver::sweep_add(const Lit* lits, uint32_t size) {
  if (size == 0) {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return false;
  }
  if (size == 1) {
    const Lit u = lits[0];
    if (vals_[u] > 0) return true;
    if (vals_[u] < 0) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
      return false;
    }
    ++stats_.sweep_units;
    assign(u, kNoReason);  // logged to the proof by on_root_fixed
    if (!propagate()) {
      inconsistent_ = true;
      if (proof_) proof_->add_empty();
      return false;
    }
    return true;
  }
  // Binary (the only other case): skip it when satisfied at the root.
  if (vals_[lits[0]] > 0 || vals_[lits[1]] > 0) return true;
  if (vals_[lits[0]] < 0) return sweep_add(lits + 1, 1);
  if (vals_[lits[1]] < 0) return sweep_add(lits, 1);
  if (proof_) proof_->add(lits, 2);
  add_binary(lits[0], lits[1], false);
  sweep_added_.push_back(std::min(lits[0], lits[1]));
  sweep_added_.push_back(std::max(lits[0], lits[1]));
  return true;
}

bool Solver::sweep_variable(Var v, const std::vector<uint32_t>& start, const std::vector<uint32_t>& occ,
                            uint64_t& ticks) {
  // --- environment (breadth first from v) ---
  if (sweep_stamp_.empty()) sweep_stamp_.assign(arena_.size() / 4 + 1, 0);  // indexed by ref / 4
  if (++sweep_stamp_now_ == 0) {
    std::fill(sweep_stamp_.begin(), sweep_stamp_.end(), 0);
    sweep_stamp_now_ = 1;
  }
  sweep_env_.clear();
  std::vector<uint32_t> depth;
  std::vector<Lit> flat;        // environment clauses: size, literals...
  uint32_t nclauses = 0;
  auto local = [&](Var u, uint32_t d) -> bool {
    if (sweep_local_[u] != kNotLocal) return true;
    if (sweep_env_.size() >= sweep_lim_vars_) return false;
    sweep_local_[u] = static_cast<uint32_t>(sweep_env_.size());
    sweep_env_.push_back(u);
    depth.push_back(d);
    return true;
  };
  local(v, 0);
  for (size_t i = 0; i < sweep_env_.size() && nclauses < sweep_lim_clauses_; ++i) {
    const Var u = sweep_env_[i];
    const uint32_t d = depth[i];
    if (d >= sweep_lim_depth_) continue;
    for (int sign = 0; sign < 2; ++sign) {
      const Lit l = make_lit(u, sign != 0);
      // Binary clauses (l v b): added when b's variable has not been expanded before (else the
      // clause came in then).
      for (const Watch& w : watches_[l]) {
        ++ticks;
        if (!w.binary() || w.redundant_binary()) continue;
        const Lit b = w.blit;
        if (vals_[b] != 0 || vals_[l] != 0) continue;
        const uint32_t lb = sweep_local_[var_of(b)];
        if (lb != kNotLocal && lb < i && depth[lb] < sweep_lim_depth_) continue;
        if (!local(var_of(b), d + 1)) continue;
        if (nclauses >= sweep_lim_clauses_) break;
        flat.push_back(2);
        flat.push_back(l);
        flat.push_back(b);
        ++nclauses;
      }
      for (uint32_t o = start[l]; o < start[l + 1] && nclauses < sweep_lim_clauses_; ++o) {
        const uint32_t ref = occ[o];
        uint32_t& stamp = sweep_stamp_[ref / 4];
        if (stamp == sweep_stamp_now_) continue;
        stamp = sweep_stamp_now_;
        const Clause& c = clause(ref);
        ticks += 1 + c.size / 4;
        if (c.garbage) continue;
        bool sat = false, fits = true;
        for (uint32_t k = 0; k < c.size && !sat; ++k) sat = vals_[c.lits()[k]] > 0;
        if (sat) continue;
        for (uint32_t k = 0; k < c.size && fits; ++k) {
          if (vals_[c.lits()[k]] == 0) fits = local(var_of(c.lits()[k]), d + 1);
        }
        if (!fits) continue;
        const size_t at = flat.size();
        flat.push_back(0);
        for (uint32_t k = 0; k < c.size; ++k) {
          if (vals_[c.lits()[k]] == 0) flat.push_back(c.lits()[k]);
        }
        flat[at] = static_cast<Lit>(flat.size() - at - 1);
        ++nclauses;
      }
    }
  }
  auto klit = [&](Lit l) -> Kitten::KLit { return 2 * sweep_local_[var_of(l)] + (is_negative(l) ? 1u : 0u); };
  auto glit = [&](Kitten::KLit k) -> Lit { return make_lit(sweep_env_[k >> 1], (k & 1u) != 0); };
  kitten_.clear();
  kitten_.resize(static_cast<uint32_t>(sweep_env_.size()));
  {
    std::vector<Kitten::KLit> kc;
    for (size_t at = 0; at < flat.size(); at += flat[at] + 1) {
      kc.clear();
      for (uint32_t k = 1; k <= flat[at]; ++k) kc.push_back(klit(flat[at + k]));
      kitten_.add_clause(kc.data(), static_cast<uint32_t>(kc.size()));
    }
  }
  ticks += flat.size() / 4;
  sweep_emitted_ = 0;
  sweep_emitted_lits_.clear();
  sweep_added_.clear();
  bool ok = true;
  const uint64_t kitten_start = kitten_.ticks();
  const uint32_t n = static_cast<uint32_t>(sweep_env_.size());
  int r = kitten_.solve(kSolveTicks);
  if (r == Kitten::kUnsat) {  // the environment, hence the formula, is unsatisfiable
    sweep_emit_learned();
    ok = sweep_add(nullptr, 0);
  } else if (r == Kitten::kSat && opts_.sweepclasses) {
    ok = sweep_classes(n);
  } else if (r == Kitten::kSat) {
    // first: the first model; backbone candidates keep their value in every model, equivalence
    // candidates (for v, local 0) keep their relation to v.
    std::vector<int8_t> first(n), backbone(n), equal(n);
    for (uint32_t i = 0; i < n; ++i) {
      first[i] = kitten_.value(2 * i);
      backbone[i] = first[i] != 0;
      equal[i] = i > 0 && first[i] != 0 && first[0] != 0;
    }
    auto refine = [&]() {
      const int8_t m0 = kitten_.value(0);
      for (uint32_t i = 0; i < n; ++i) {
        const int8_t m = kitten_.value(2 * i);
        if (m != first[i]) backbone[i] = 0;
        if (equal[i] && m * m0 != first[i] * first[0]) equal[i] = 0;
      }
    };
    auto true_lit = [&](uint32_t i) -> Kitten::KLit { return 2 * i + (first[i] > 0 ? 0u : 1u); };
    // Backbone literals: l is implied if the environment with -l is unsatisfiable.
    size_t checks = 0;
    for (uint32_t i = 0; i < n && ok && checks < kBackboneCandidates; ++i) {
      if (!backbone[i]) continue;
      if (vals_[make_lit(sweep_env_[i], false)] != 0) continue;  // fixed meanwhile
      ++checks;
      const Kitten::KLit l = true_lit(i);
      kitten_.assume(l ^ 1u);
      r = kitten_.solve(kSolveTicks);
      if (r == Kitten::kUnknown) break;
      if (r == Kitten::kSat) {
        refine();
        continue;
      }
      sweep_emit_learned();
      if (kitten_.inconsistent()) {
        ok = sweep_add(nullptr, 0);
        break;
      }
      const Lit u = glit(l);
      ok = sweep_add(&u, 1);
      kitten_.add_clause(&l, 1);
    }
    // Equivalences x = y for v (x its literal true in the first model, y likewise for a
    // candidate): both (x & -y) and (-x & y) must be unsatisfiable.
    checks = 0;
    for (uint32_t i = 1; i < n && ok && checks < kEquivalenceCandidates; ++i) {
      if (!equal[i] || vals_[make_lit(v, false)] != 0) continue;
      if (vals_[make_lit(sweep_env_[i], false)] != 0) continue;
      ++checks;
      const Kitten::KLit x = true_lit(0), y = true_lit(i);
      std::vector<Lit> implied[2];
      bool proved = true;
      for (int dir = 0; dir < 2 && proved; ++dir) {
        kitten_.assume(dir == 0 ? x : x ^ 1u);
        kitten_.assume(dir == 0 ? y ^ 1u : y);
        r = kitten_.solve(kSolveTicks);
        if (r != Kitten::kUnsat) {
          if (r == Kitten::kSat) refine();
          proved = false;
          break;
        }
        for (const Kitten::KLit k : kitten_.final_clause()) implied[dir].push_back(glit(k));
        if (kitten_.inconsistent()) implied[dir].clear();
      }
      if (r == Kitten::kUnknown) break;
      if (!proved) continue;
      sweep_emit_learned();
      for (int dir = 0; dir < 2 && ok; ++dir) {
        ok = sweep_add(implied[dir].data(), static_cast<uint32_t>(implied[dir].size()));
      }
      if (ok && implied[0].size() == 2 && implied[1].size() == 2) {
        ++stats_.sweep_equivalences;
        break;
      }
    }
    if (ok) {
      // Kitten's learned units are implied by the formula: backbone literals for free.
      sweep_emit_learned();
      for (size_t i = 0; i < kitten_.num_learned() && ok; ++i) {
        if (kitten_.learned_size(i) != 1) continue;
        const Lit u = glit(kitten_.learned_lits(i)[0]);
        ok = sweep_add(&u, 1);
      }
    }
  }
  ticks += kitten_.ticks() - kitten_start;
  // The emitted learned clauses were only needed to derive the added ones: delete them again
  // (except units, and copies of the binary clauses now in the formula).
  if (proof_) {
    for (size_t at = 0; at < sweep_emitted_lits_.size(); at += sweep_emitted_lits_[at] + 1) {
      const uint32_t size = sweep_emitted_lits_[at];
      const Lit* lits = sweep_emitted_lits_.data() + at + 1;
      if (size < 2) continue;
      bool kept = false;
      if (size == 2) {
        const Lit a = std::min(lits[0], lits[1]), b = std::max(lits[0], lits[1]);
        for (size_t k = 0; k < sweep_added_.size() && !kept; k += 2) {
          kept = sweep_added_[k] == a && sweep_added_[k + 1] == b;
        }
      }
      if (!kept) proof_->del(lits, size);
    }
  }
  for (const Var u : sweep_env_) sweep_local_[u] = kNotLocal;
  return ok;
}

// Candidates as in Kissat's sweeping (--sweepclasses): backbone candidates are the literals true
// in the first model, equivalence candidates a partition of them into classes whose literals had
// equal values in every model so far. Every model, from a Kitten call or from flipping a literal
// of the current one, refines both. Equivalences are checked for two literals of the last class
// (two Kitten calls), so they are found between any two variables of the environment, not only
// with the swept one; the second literal then leaves its class. Kitten decides with random
// phases: diverse models split classes faster. False on a conflict at the root.
bool Solver::sweep_classes(uint32_t n) {
  using KLit = Kitten::KLit;
  constexpr KLit kSep = UINT32_MAX;
  auto glit = [&](KLit k) -> Lit { return make_lit(sweep_env_[k >> 1], (k & 1u) != 0); };
  auto fixed = [&](KLit k) { return vals_[glit(k)] != 0; };
  auto solve = [&]() {
    kitten_.randomize_phases(rng_);
    return kitten_.solve(kSolveTicks);
  };
  const uint64_t limit = kitten_.ticks() + kVariableTicks;
  std::vector<KLit>& backbone = sweep_backbone_;
  std::vector<KLit>& part = sweep_partition_;  // classes, each closed by kSep
  std::vector<KLit>& next = sweep_next_;
  backbone.clear();
  part.clear();
  for (uint32_t i = 0; i < n; ++i) {
    const int8_t val = kitten_.value(2 * i);
    if (!val) continue;
    const KLit l = 2 * i + (val > 0 ? 0u : 1u);
    if (fixed(l)) continue;
    // Equivalent to another literal since this round started: proven already (the binary
    // clauses are in the formula, substitution removes the variable after the round).
    if (sweep_merged_[sweep_env_[i]] == stats_.sweeps) continue;
    backbone.push_back(l);
    part.push_back(l);
  }
  part.push_back(kSep);
  if (part.size() < 3) part.clear();
  // The current assignment is a model: candidates false in it are refuted.
  auto refine = [&]() {
    size_t j = 0;
    for (const KLit l : backbone) {
      if (!fixed(l) && kitten_.value(l) > 0) backbone[j++] = l;
    }
    backbone.resize(j);
    next.clear();
    for (size_t p = 0; p < part.size();) {
      size_t q = p;
      while (part[q] != kSep) ++q;
      for (int polarity = 1; polarity >= -1; polarity -= 2) {
        const size_t mark = next.size();
        for (size_t k = p; k < q; ++k) {
          if (!fixed(part[k]) && kitten_.value(part[k]) == polarity) next.push_back(part[k]);
        }
        if (next.size() - mark >= 2) {
          next.push_back(kSep);
        } else {
          next.resize(mark);
        }
      }
      p = q + 1;
    }
    part.swap(next);
  };
  // Flipping a candidate in the current model (when every clause stays satisfied) is a model
  // too; one round over all candidates, then one refinement.
  auto flip_candidates = [&](const std::vector<KLit>& cands) {
    bool flipped = false;
    for (const KLit l : cands) {
      if (l == kSep || kitten_.value(l) <= 0) continue;
      if (kitten_.flip(l)) {
        ++stats_.sweep_flips;
        flipped = true;
      }
    }
    if (flipped) refine();
  };
  auto last_class_start = [&]() {
    size_t start = part.size() - 1;
    while (start > 0 && part[start - 1] != kSep) --start;
    return start;
  };
  bool ok = true;
  // Backbone literals: l is implied if the environment with -l is unsatisfiable.
  while (ok && !backbone.empty() && kitten_.ticks() <= limit) {
    flip_candidates(backbone);
    if (backbone.empty()) break;
    const KLit l = backbone.back();
    backbone.pop_back();
    if (fixed(l)) continue;
    kitten_.assume(l ^ 1u);
    const int r = solve();
    if (r == Kitten::kUnknown) return ok;
    if (r == Kitten::kSat) {
      refine();
      continue;
    }
    sweep_emit_learned();
    if (kitten_.inconsistent()) return sweep_add(nullptr, 0);
    const Lit u = glit(l);
    ok = sweep_add(&u, 1);
    kitten_.add_clause(&l, 1);
  }
  // Equivalences x = y for two literals of the last class: (-x & y) and (x & -y) unsatisfiable.
  std::vector<Lit> implied[2];
  while (ok && !part.empty() && kitten_.ticks() <= limit) {
    {  // fixed literals leave the last class
      const size_t start = last_class_start();
      size_t j = start;
      for (size_t k = start; k + 1 < part.size(); ++k) {
        if (!fixed(part[k])) part[j++] = part[k];
      }
      part.resize(j);
      if (j - start >= 2) {
        part.push_back(kSep);
      } else {
        part.resize(start);
        continue;
      }
    }
    flip_candidates(part);
    if (part.empty()) break;
    const size_t end = part.size();
    if (end < 3 || part[end - 1] != kSep || part[end - 2] == kSep || part[end - 3] == kSep) {
      part.clear();  // (cannot happen: classes have two literals or more)
      break;
    }
    const KLit x = part[end - 3], y = part[end - 2];
    bool proved = true;
    int r = Kitten::kUnsat;
    for (int dir = 0; dir < 2 && proved; ++dir) {
      kitten_.assume(dir == 0 ? x ^ 1u : x);
      kitten_.assume(dir == 0 ? y : y ^ 1u);
      r = solve();
      if (r != Kitten::kUnsat) {
        proved = false;
        break;
      }
      implied[dir].clear();
      for (const KLit k : kitten_.final_clause()) implied[dir].push_back(glit(k));
      if (kitten_.inconsistent()) implied[dir].clear();
    }
    if (r == Kitten::kUnknown) break;
    if (!proved) {
      refine();  // x and y differ in the model
      continue;
    }
    sweep_emit_learned();
    for (int dir = 0; dir < 2 && ok; ++dir) {
      ok = sweep_add(implied[dir].data(), static_cast<uint32_t>(implied[dir].size()));
    }
    if (!ok) break;
    if (implied[0].size() == 2 && implied[1].size() == 2) {
      ++stats_.sweep_equivalences;
      const KLit b1[2] = {x, y ^ 1u}, b2[2] = {x ^ 1u, y};
      kitten_.add_clause(b1, 2);
      kitten_.add_clause(b2, 2);
      sweep_merged_[sweep_env_[y >> 1]] = static_cast<uint32_t>(stats_.sweeps);
    }
    // y leaves its class (x represents it); a class of one literal is dropped.
    part.erase(part.begin() + static_cast<std::ptrdiff_t>(end - 2));
    const size_t start = last_class_start();
    if (part.size() - 1 - start < 2) part.resize(start);
  }
  if (ok) {
    // Kitten's learned units are implied by the formula: backbone literals for free.
    sweep_emit_learned();
    for (size_t i = 0; i < kitten_.num_learned() && ok; ++i) {
      if (kitten_.learned_size(i) != 1) continue;
      const Lit u = glit(kitten_.learned_lits(i)[0]);
      ok = sweep_add(&u, 1);
    }
  }
  return ok;
}

}  // namespace psat
