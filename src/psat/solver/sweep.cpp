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
//
// Cost (measured on minandmaxor128, see PLAN.md 2026-11-07 sweep2): almost every Kitten call is
// satisfiable (97%); the calls go to backbone checks (a third) and to equivalence checks whose
// first direction is satisfiable (96%), i.e. to models that split candidate classes. Options
// (the first three on by default):
// --sweepphase gives Kitten phases that split the classes (and refute backbone candidates),
// --sweepqueue decides from a queue instead of the score heap (most calls have no conflict),
// --sweepknown skips equivalences already in the formula (2: and keeps proved ones out of later
// candidates until substitution), --sweepouter=0 skips pairs of two outermost literals,
// --sweepgrowcheck grows the environments after a window of swept variables instead of a full
// cycle, --sweepfollow and --sweepdirty change the order of the swept variables.

#include <algorithm>
#include <cstdio>
#include <utility>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {
constexpr uint32_t kNotLocal = UINT32_MAX;
constexpr uint64_t kSolveTicks = 20000;  // Kitten ticks per solve
constexpr size_t kBackboneCandidates = 16;
constexpr size_t kEquivalenceCandidates = 8;
constexpr uint64_t kVariableTicks = 500000;  // Kitten ticks per swept variable (sweepclasses)
constexpr uint32_t kEnvPrefetch = 4;  // occurrences ahead whose clause is prefetched (environment)
}  // namespace

void Solver::sweep(uint64_t min_budget) {
  const PassTimer pass_timer(*this, kPassSweep);
  if (inconsistent_ || !opts_.sweep || stop_requested()) return;
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
  const uint64_t r_vars = stats_.swept_vars, r_units = stats_.sweep_units, r_eqs = stats_.sweep_equivalences,
                 r_known = stats_.sweep_eq_known, r_solves = stats_.sweep_solves;
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
  // variables (--sweepgrowcheck: after that many swept variables) that found less than one unit
  // or equivalence per 100 swept variables (twice the variables and clauses, one more level of
  // depth up to 3).
  auto set_limits = [&]() {
    const uint32_t g = opts_.sweepgrow ? sweep_growth_ : 0;
    sweep_lim_vars_ = static_cast<uint32_t>(std::min<uint64_t>(uint64_t{static_cast<uint32_t>(opts_.sweepvars)} << g, 8192));
    sweep_lim_clauses_ =
        static_cast<uint32_t>(std::min<uint64_t>(uint64_t{static_cast<uint32_t>(opts_.sweepclauses)} << g, 32768));
    const uint32_t base_depth = static_cast<uint32_t>(opts_.sweepdepth);
    sweep_lim_depth_ = base_depth >= 3 ? base_depth : std::min<uint32_t>(base_depth + g, 3);
  };
  set_limits();
  // --sweepdirty: while variables whose clauses changed since they were swept (or never swept)
  // remain, the others are skipped; growth makes every variable dirty again.
  if (sweep_dirty_.size() < num_vars_) sweep_dirty_.resize(num_vars_, 1);
  uint64_t dirty = 0;
  if (opts_.sweepdirty) {
    for (Var u = 0; u < num_vars_; ++u) dirty += sweep_dirty_[u] && !eliminated_[u] && !vals_[make_lit(u, false)];
  }
  auto check_growth = [&]() {
    const uint64_t found = stats_.sweep_units + stats_.sweep_equivalences - sweep_cycle_found_;
    if (100 * found < sweep_cycle_swept_ && sweep_growth_ < static_cast<uint32_t>(opts_.sweepgrowmax)) {
      ++sweep_growth_;
      if (opts_.sweepdirty) {
        std::fill(sweep_dirty_.begin(), sweep_dirty_.end(), 1);
        dirty = num_vars_;
      }
    }
    sweep_cycle_found_ = stats_.sweep_units + stats_.sweep_equivalences;
    sweep_cycle_swept_ = 0;
  };
  const uint64_t window = static_cast<uint64_t>(opts_.sweepgrowcheck);
  uint64_t ticks = occ.size() / 4;
  if (sweep_queued_.size() < num_vars_) sweep_queued_.resize(num_vars_, 0);
  // --sweeporder: the cursor walks this permutation of the variables instead of the indices.
  std::vector<Var> order;
  if (opts_.sweeporder == 1) {
    order.resize(num_vars_);
    for (Var u = 0; u < num_vars_; ++u) order[u] = num_vars_ - 1 - u;
  } else if (opts_.sweeporder >= 2) {
    order.resize(num_vars_);
    for (Var u = 0; u < num_vars_; ++u) order[u] = u;
    auto occs = [&](Var u) {
      const Lit p = make_lit(u, false), n = make_lit(u, true);
      return (start[p + 1] - start[p]) + (start[n + 1] - start[n]);
    };
    if (opts_.sweeporder == 2) {
      std::stable_sort(order.begin(), order.end(), [&](Var a, Var b) { return occs(a) > occs(b); });
    } else {
      // 3: fewest occurrences first; variables with a polarity in more long clauses than an
      // environment may hold go last (their environments would be cut off).
      const uint32_t lim = sweep_lim_clauses_;
      auto rank = [&](Var u) -> uint64_t {
        const Lit p = make_lit(u, false), n = make_lit(u, true);
        const uint32_t a = start[p + 1] - start[p], b = start[n + 1] - start[n];
        return (a > lim || b > lim ? uint64_t{1} << 32 : 0) + a + b;
      };
      std::stable_sort(order.begin(), order.end(), [&](Var a, Var b) { return rank(a) < rank(b); });
    }
    ticks += num_vars_;
  }
  size_t followed = 0;  // --sweepfollow: variables taken from sweep_follow_ (FIFO)
  for (uint32_t scanned = 0; scanned < num_vars_ && ticks < budget && !inconsistent_; ++scanned) {
    Var v;
    if (followed < sweep_follow_.size()) {
      v = sweep_follow_[followed++];
      sweep_queued_[v] = 0;
      ++stats_.sweep_followed;
    } else {
      v = sweep_cursor_++ % num_vars_;
      if (!order.empty()) v = order[v];
      if (!window && sweep_cursor_ % num_vars_ == 0) check_growth();  // a full cycle over the variables ends
    }
    if (eliminated_[v] || vals_[make_lit(v, false)] != 0) continue;
    if (opts_.sweepdirty) {
      if (!sweep_dirty_[v] && dirty > 0) {
        ++stats_.sweep_clean_skipped;
        continue;
      }
      if (sweep_dirty_[v]) {
        sweep_dirty_[v] = 0;
        if (dirty) --dirty;
      }
    }
    // --sweepknown=2: proved equivalent to a variable still in the formula (substitution removes
    // one of them): its environment is taken as the other's.
    if (opts_.sweepknown >= 2 && sweep_merged_[v] == substitute_epoch_ + 1) continue;
    const Lit p = make_lit(v, false), n = make_lit(v, true);
    if (start[p + 1] == start[p] && start[n + 1] == start[n]) continue;  // only binary occurrences
    if (stop_requested()) break;
    ++stats_.swept_vars;
    ++sweep_cycle_swept_;
    if (!sweep_variable(v, start, occ, ticks)) break;
    if (window && sweep_cycle_swept_ >= window) {
      check_growth();
      set_limits();
    }
  }
  sweep_follow_.erase(sweep_follow_.begin(), sweep_follow_.begin() + static_cast<std::ptrdiff_t>(followed));
  stats_.sweep_ticks += ticks;
  if (opts_.verbose >= 2) {
    std::printf("c [%.2f s] sweep %llu: %llu variables, %llu units, %llu equivalences (%llu known), %llu Kitten calls, "
                "budget %llu ticks %llu, limits %u/%u/%u, cursor %u\n",
                seconds(), static_cast<unsigned long long>(stats_.sweeps),
                static_cast<unsigned long long>(stats_.swept_vars - r_vars), static_cast<unsigned long long>(stats_.sweep_units - r_units),
                static_cast<unsigned long long>(stats_.sweep_equivalences - r_eqs),
                static_cast<unsigned long long>(stats_.sweep_eq_known - r_known),
                static_cast<unsigned long long>(stats_.sweep_solves - r_solves), static_cast<unsigned long long>(budget),
                static_cast<unsigned long long>(ticks), sweep_lim_vars_, sweep_lim_clauses_, sweep_lim_depth_,
                num_vars_ ? sweep_cursor_ % num_vars_ : 0);
  }
  const bool productive = stats_.sweep_units + stats_.sweep_equivalences != found_before;
  sweep_delay_ = productive ? 0 : std::min<uint32_t>(2 * sweep_delay_ + 1, 64);
  sweep_skip_ = sweep_delay_;
}

// Emits Kitten's learned clauses that the refutations so far depend on (Kitten marks them, see
// Kitten::track_cores) and that are not in the proof yet, in derivation order.
void Solver::sweep_emit_learned() {
  if (!proof_) return;
  if (sweep_emitted_.size() < kitten_.num_learned()) sweep_emitted_.resize(kitten_.num_learned(), 0);
  for (size_t i = 0; i < kitten_.num_learned(); ++i) {
    if (sweep_emitted_[i] || !kitten_.needed(i)) continue;
    sweep_emitted_[i] = 1;
    const uint32_t size = kitten_.learned_size(i);
    const Kitten::KLit* kl = kitten_.learned_lits(i);
    const size_t at = sweep_emitted_lits_.size();
    sweep_emitted_lits_.push_back(size);
    for (uint32_t k = 0; k < size; ++k) {
      sweep_emitted_lits_.push_back(make_lit(sweep_env_[kl[k] >> 1], (kl[k] & 1u) != 0));
    }
    proof_->add(sweep_emitted_lits_.data() + at + 1, size);
  }
}

// Marks Kitten's learned units that sweep_add would use (not yet true in the formula), so that
// their derivations are emitted.
void Solver::sweep_mark_learned_units() {
  if (!proof_) return;
  for (size_t i = 0; i < kitten_.num_learned(); ++i) {
    if (kitten_.learned_size(i) != 1) continue;
    const Kitten::KLit k = kitten_.learned_lits(i)[0];
    if (vals_[make_lit(sweep_env_[k >> 1], (k & 1u) != 0)] <= 0) kitten_.mark_learned(i);
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
  if (proof_) {
    // Kitten's derivation often ends with this very clause: then it is in the proof already (and
    // sweep_retire_learned keeps that copy).
    bool emitted = false;
    for (size_t at = 0; at < sweep_emitted_lits_.size() && !emitted; at += sweep_emitted_lits_[at] + 1) {
      if (sweep_emitted_lits_[at] != 2) continue;
      const Lit* e = sweep_emitted_lits_.data() + at + 1;
      emitted = (e[0] == lits[0] && e[1] == lits[1]) || (e[0] == lits[1] && e[1] == lits[0]);
    }
    if (!emitted) proof_->add(lits, 2);
  }
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
  std::vector<uint32_t>& depth = sweep_depth_;
  depth.clear();
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
      // The clauses are scattered over the arena (and their stamps over sweep_stamp_): both are
      // prefetched a few occurrences ahead, which changes nothing else.
      const uint32_t* const occs = occ.data();
      const uint32_t end = start[l + 1];
      for (uint32_t o = start[l]; o < end && nclauses < sweep_lim_clauses_; ++o) {
        if (o + kEnvPrefetch < end) {
          const uint32_t ahead = occs[o + kEnvPrefetch];
          PSAT_PREFETCH(sweep_stamp_.data() + ahead / 4);
          PSAT_PREFETCH(arena_.data() + ahead);
        }
        const uint32_t ref = occs[o];
        uint32_t& stamp = sweep_stamp_[ref / 4];
        if (stamp == sweep_stamp_now_) continue;
        stamp = sweep_stamp_now_;
        const Clause& c = clause(ref);
        ticks += 1 + c.size / 4;
        if (c.garbage) continue;
        const Lit* const lits = c.lits();
        const uint32_t size = c.size;
        if (sweep_env_.size() >= sweep_lim_vars_) {
          // A full environment takes no variable any more (local() only answers): the clause is
          // skipped at its first true literal or unassigned literal outside the environment,
          // whichever comes first, in one pass (most clauses met then are skipped).
          bool skip = false;
          for (uint32_t k = 0; k < size; ++k) {
            const int8_t x = vals_[lits[k]];
            if (x > 0 || (x == 0 && sweep_local_[var_of(lits[k])] == kNotLocal)) {
              skip = true;
              break;
            }
          }
          if (skip) continue;
        } else {
          bool sat = false, fits = true;
          for (uint32_t k = 0; k < size && !sat; ++k) sat = vals_[lits[k]] > 0;
          if (sat) continue;
          for (uint32_t k = 0; k < size && fits; ++k) {
            if (vals_[lits[k]] == 0) fits = local(var_of(lits[k]), d + 1);
          }
          if (!fits) continue;
        }
        const size_t at = flat.size();
        flat.push_back(0);
        for (uint32_t k = 0; k < size; ++k) {
          if (vals_[lits[k]] == 0) flat.push_back(lits[k]);
        }
        flat[at] = static_cast<Lit>(flat.size() - at - 1);
        ++nclauses;
      }
    }
  }
  auto klit = [&](Lit l) -> Kitten::KLit { return 2 * sweep_local_[var_of(l)] + (is_negative(l) ? 1u : 0u); };
  auto glit = [&](Kitten::KLit k) -> Lit { return make_lit(sweep_env_[k >> 1], (k & 1u) != 0); };
  stats_.sweep_env_vars += sweep_env_.size();
  stats_.sweep_env_clauses += nclauses;
  kitten_.clear();
  kitten_.use_queue(opts_.sweepqueue != 0);
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
  kitten_.track_cores(proof_ != nullptr);
  sweep_emitted_.clear();
  sweep_emitted_lits_.clear();
  sweep_added_.clear();
  bool ok = true;
  const uint64_t kitten_start = kitten_.ticks();
  const uint32_t n = static_cast<uint32_t>(sweep_env_.size());
  int r = (++stats_.sweep_solves, ++stats_.sweep_env_solves, kitten_.solve(kSolveTicks));
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
    for (uint32_t i = 0; i < n && ok && checks < kBackboneCandidates && !stop_requested(); ++i) {
      if (!backbone[i]) continue;
      if (vals_[make_lit(sweep_env_[i], false)] != 0) continue;  // fixed meanwhile
      ++checks;
      const Kitten::KLit l = true_lit(i);
      kitten_.assume(l ^ 1u);
      r = (++stats_.sweep_solves, kitten_.solve(kSolveTicks));
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
    for (uint32_t i = 1; i < n && ok && checks < kEquivalenceCandidates && !stop_requested(); ++i) {
      if (!equal[i] || vals_[make_lit(v, false)] != 0) continue;
      if (vals_[make_lit(sweep_env_[i], false)] != 0) continue;
      ++checks;
      const Kitten::KLit x = true_lit(0), y = true_lit(i);
      std::vector<Lit> implied[2];
      bool proved = true;
      for (int dir = 0; dir < 2 && proved; ++dir) {
        kitten_.assume(dir == 0 ? x : x ^ 1u);
        kitten_.assume(dir == 0 ? y ^ 1u : y);
        r = (++stats_.sweep_solves, kitten_.solve(kSolveTicks));
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
      sweep_mark_learned_units();
      sweep_emit_learned();
      for (size_t i = 0; i < kitten_.num_learned() && ok; ++i) {
        if (kitten_.learned_size(i) != 1) continue;
        const Lit u = glit(kitten_.learned_lits(i)[0]);
        ok = sweep_add(&u, 1);
      }
    }
  }
  ticks += kitten_.ticks() - kitten_start;
  stats_.sweep_kitten_ticks += kitten_.ticks() - kitten_start;
  sweep_retire_learned();
  for (const Var u : sweep_env_) sweep_local_[u] = kNotLocal;
  return ok;
}

// The emitted learned clauses were only needed to derive the added ones: deletes them from the
// proof again (except units, and copies of the binary clauses now in the formula).
void Solver::sweep_retire_learned() {
  if (!proof_) return;
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
  // --sweepphase: phases that split what the models so far did not: backbone candidates false,
  // the literals of each class alternately true and false (others random).
  auto solve = [&]() {
    kitten_.randomize_phases(rng_);
    if (opts_.sweepphase) {
      uint64_t bits = 0;
      int left = 0;
      bool first = true, want = true;
      for (const KLit l : sweep_partition_) {
        if (first) {  // the first member's value: random per class
          if (left == 0) {
            rng_ ^= rng_ << 13;
            rng_ ^= rng_ >> 7;
            rng_ ^= rng_ << 17;
            bits = rng_;
            left = 64;
          }
          want = (bits & 1u) != 0;
          bits >>= 1;
          --left;
        }
        first = l == kSep;
        if (first) continue;
        kitten_.prefer(want ? l : l ^ 1u);
        want = !want;
      }
      for (const KLit l : sweep_backbone_) kitten_.prefer(l ^ 1u);
    }
    return (++stats_.sweep_solves, kitten_.solve(kSolveTicks));
  };
  const uint64_t limit = kitten_.ticks() + kVariableTicks;
  std::vector<KLit>& backbone = sweep_backbone_;
  std::vector<KLit>& part = sweep_partition_;  // classes, each closed by kSep
  std::vector<KLit>& next = sweep_next_;
  backbone.clear();
  part.clear();
  const uint32_t merged_key = opts_.sweepknown >= 2 ? substitute_epoch_ + 1 : static_cast<uint32_t>(stats_.sweeps);
  for (uint32_t i = 0; i < n; ++i) {
    const int8_t val = kitten_.value(2 * i);
    if (!val) continue;
    const KLit l = 2 * i + (val > 0 ? 0u : 1u);
    if (fixed(l)) continue;
    // Equivalent to another literal since this round started (--sweepknown=2: since the last
    // substitution): proven already (the binary clauses are in the formula, substitution removes
    // the variable).
    if (sweep_merged_[sweep_env_[i]] == merged_key) continue;
    backbone.push_back(l);
    part.push_back(l);
  }
  part.push_back(kSep);
  if (part.size() < 3) part.clear();
  if (!opts_.sweepbackbone) backbone.clear();  // backbone literals only from Kitten's learned units
  stats_.sweep_bb_cands += backbone.size();
  stats_.sweep_eq_cands += part.empty() ? 0 : part.size() - 1;
  // The current assignment is a model: candidates false in it are refuted. Returns the
  // backbone candidates and the class literals (statistics) refuted.
  auto refine = [&]() {
    size_t j = 0;
    for (const KLit l : backbone) {
      if (!fixed(l) && kitten_.value(l) > 0) backbone[j++] = l;
    }
    const size_t bb_refuted = backbone.size() - j;
    backbone.resize(j);
    next.clear();
    size_t lits = 0, seps = 0;
    for (size_t p = 0; p < part.size();) {
      size_t q = p;
      while (part[q] != kSep) ++q;
      lits += q - p;
      for (int polarity = 1; polarity >= -1; polarity -= 2) {
        const size_t mark = next.size();
        for (size_t k = p; k < q; ++k) {
          if (!fixed(part[k]) && kitten_.value(part[k]) == polarity) next.push_back(part[k]);
        }
        if (next.size() - mark >= 2) {
          next.push_back(kSep);
          ++seps;
        } else {
          next.resize(mark);
        }
      }
      p = q + 1;
    }
    part.swap(next);
    return std::pair<size_t, size_t>(bb_refuted, lits - (part.size() - seps));
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
    if (flipped) {
      const auto [b, e] = refine();
      stats_.sweep_bb_by_flip += b;
      stats_.sweep_eq_by_flip += e;
    }
  };
  auto refine_model = [&]() {
    const auto [b, e] = refine();
    stats_.sweep_bb_by_model += b;
    stats_.sweep_eq_by_model += e;
  };
  auto last_class_start = [&]() {
    size_t start = part.size() - 1;
    while (start > 0 && part[start - 1] != kSep) --start;
    return start;
  };
  bool ok = true;
  // Backbone literals: l is implied if the environment with -l is unsatisfiable.
  while (ok && !backbone.empty() && kitten_.ticks() <= limit && !stop_requested()) {
    flip_candidates(backbone);
    if (backbone.empty()) break;
    const KLit l = backbone.back();
    backbone.pop_back();
    if (fixed(l)) continue;
    kitten_.assume(l ^ 1u);
    const int r = solve();
    ++stats_.sweep_bb_solves;
    if (r == Kitten::kUnknown) {
      ++stats_.sweep_bb_unknown;
      return ok;
    }
    if (r == Kitten::kSat) {
      ++stats_.sweep_bb_sat;
      refine_model();
      continue;
    }
    ++stats_.sweep_bb_unsat;
    sweep_emit_learned();
    if (kitten_.inconsistent()) return sweep_add(nullptr, 0);
    const Lit u = glit(l);
    ok = sweep_add(&u, 1);
    kitten_.add_clause(&l, 1);
  }
  // Equivalences x = y for two literals of the last class: (-x & y) and (x & -y) unsatisfiable.
  std::vector<Lit> implied[2];
  while (ok && !part.empty() && kitten_.ticks() <= limit && !stop_requested()) {
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
    if (!opts_.sweepouter) {
      // --sweepouter=0: pairs of two outermost literals (at the depth limit, with part of their
      // clauses outside the environment) are not checked: x is an inner literal of the class, a
      // class without one is dropped.
      const size_t start = last_class_start();
      size_t inner = end;
      for (size_t k = start; k + 1 < end; ++k) {
        if (sweep_depth_[part[k] >> 1] < sweep_lim_depth_) {
          inner = k;
          break;
        }
      }
      if (inner == end) {
        stats_.sweep_outer_dropped += end - 1 - start;
        part.resize(start);
        continue;
      }
      std::swap(part[inner], part[end - 3]);
    }
    const KLit x = part[end - 3], y = part[end - 2];
    ++stats_.sweep_eq_checks;
    if (opts_.sweepknown) {
      auto has_bin = [&](Lit a, Lit b) {
        for (const Watch& w : watches_[a]) {
          if (w.binary() && w.blit == b && !w.redundant_binary()) return true;
        }
        return false;
      };
      const Lit gx = glit(x), gy = glit(y);
      if (has_bin(gx, negate(gy)) && has_bin(negate(gx), gy)) {
        // Both binary clauses are in the formula already (proved by simulation, congruence or a
        // sweep before the last substitution): Kitten gets them (formula clauses), y leaves its
        // class, nothing is counted.
        ++stats_.sweep_eq_known;
        const KLit b1[2] = {x, y ^ 1u}, b2[2] = {x ^ 1u, y};
        kitten_.add_clause(b1, 2);
        kitten_.add_clause(b2, 2);
        sweep_merged_[sweep_env_[y >> 1]] = merged_key;
        part.erase(part.begin() + static_cast<std::ptrdiff_t>(end - 2));
        const size_t start = last_class_start();
        if (part.size() - 1 - start < 2) part.resize(start);
        continue;
      }
    }
    bool proved = true;
    int r = Kitten::kUnsat;
    for (int dir = 0; dir < 2 && proved; ++dir) {
      kitten_.assume(dir == 0 ? x ^ 1u : x);
      kitten_.assume(dir == 0 ? y : y ^ 1u);
      r = solve();
      ++stats_.sweep_eq_solves;
      if (r == Kitten::kSat) ++stats_.sweep_eq_sat;
      if (r == Kitten::kUnsat) ++stats_.sweep_eq_unsat;
      if (r == Kitten::kUnknown) ++stats_.sweep_eq_unknown;
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
      refine_model();  // x and y differ in the model
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
      sweep_merged_[sweep_env_[y >> 1]] = merged_key;
      // --sweepfollow: x is swept again soon (its environment now reaches y's clauses through the
      // binary clauses: gates on x and y may be equivalent next). --sweepdirty: x is dirty.
      const Var fx = sweep_env_[x >> 1];
      sweep_dirty_[fx] = 1;
      if (opts_.sweepfollow && !sweep_queued_[fx]) {
        sweep_queued_[fx] = 1;
        sweep_follow_.push_back(fx);
      }
    }
    // y leaves its class (x represents it); a class of one literal is dropped.
    part.erase(part.begin() + static_cast<std::ptrdiff_t>(end - 2));
    const size_t start = last_class_start();
    if (part.size() - 1 - start < 2) part.resize(start);
  }
  if (ok) {
    // Kitten's learned units are implied by the formula: backbone literals for free.
    sweep_mark_learned_units();
    sweep_emit_learned();
    for (size_t i = 0; i < kitten_.num_learned() && ok; ++i) {
      if (kitten_.learned_size(i) != 1) continue;
      const Lit u = glit(kitten_.learned_lits(i)[0]);
      ok = sweep_add(&u, 1);
    }
  }
  if (kitten_.ticks() > limit) ++stats_.sweep_var_limit;
  return ok;
}

}  // namespace psat
