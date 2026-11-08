// Linear equations modulo a prime on one-hot domains (--linmod, off by default).
//
// Structure:
// - A domain is an "exactly one" group: a clause l_0 v ... v l_{p-1} (p = 3, 5 or 7) with every
//   binary clause -l_i v -l_j. It encodes a variable over Z_p: value i <=> l_i true, the values
//   numbered by input variable index. No variable is in two domains.
// - A constraint over k domains is the set of clauses that consist of one negated domain literal
//   of each of the k domains (each clause forbids one tuple of values). If the allowed tuples are
//   exactly the solutions of one equation c_1 x_1 + ... + c_k x_k = r (mod p), all c_i nonzero
//   (p^(k-1) allowed of p^k), the constraint is that equation. For p = 3 every relabelling of a
//   domain is affine (x -> a x + b), so the value numbering does not matter; for p = 5 or 7 a
//   constraint that is not affine under the input numbering stays a set of clauses.
// - Resolution needs exponentially long refutations of such systems (as for XORs, p = 2), and
//   CDCL does not find solutions either: the sc2026 linear-equations family (400 domains of 3
//   values, 360 equations of 4 terms, 21,040 clauses) is unsolved by us and by Kissat 4.0.4 at
//   1000 s.
//
// Use (before search, after counting, before Gauss-Jordan on XORs):
// - Gaussian elimination over GF(p) per prime (dense rows, reduced row echelon form).
// - A consistent system gives a solution (free variables 0). It is tried as an assignment: each
//   domain's value literal is decided and propagated, then every other variable is decided with
//   its saved phase, as the lucky pass does. If nothing conflicts, the assignment satisfies the
//   formula and is the model (checked against the input like every model). Otherwise the solver
//   backtracks to the root and the assignment stays as the saved phases.
// - An inconsistent system refutes the formula, but there is no DRAT proof for that yet: it is
//   only counted, and search goes on as usual.
// - A conflict at the root (a clause falsified by the root units, also one that an earlier
//   propagation found and left to search, as the lucky pass does) ends the solve with the empty
//   clause, RUP from the root units in the proof: the decisions must not start from it.
// The pass runs only if the domains and equations cover --linmodmin per mille of the clauses. It
// changes nothing in the formula; with --linmod=0 the search is the same as without the pass.

#include <algorithm>
#include <chrono>
#include <cstdio>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

uint64_t mix_group(uint64_t h, uint64_t g) {
  h ^= g + 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2);
  h = (h ^ (h >> 30)) * 0xBF58476D1CE4E5B9ull;
  return h ^ (h >> 31);
}

}  // namespace

bool Solver::linmod() {
  const auto t0 = std::chrono::steady_clock::now();
  LinmodStats& ls = linmod_stats_;
  ++ls.runs;
  auto finish = [&](bool result) {
    ls.seconds += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return result;
  };
  if (inconsistent_ || level() > 0) return finish(false);
  // A conflict at the root (in this propagation, or one an earlier pass found and left behind,
  // as the lucky pass does): the formula is unsatisfiable. The root units are in the proof, so the
  // empty clause is RUP. (Search would find it too, but the decisions below must not start from
  // a falsified clause.)
  auto root_conflict = [&]() {
    inconsistent_ = true;
    if (proof_) proof_->add_empty();
    return finish(false);
  };
  if (!propagate_vivify(kNoReason)) return root_conflict();

  // The clauses: live irredundant long clauses (ids 0..L-1), then the irredundant binary clauses.
  std::vector<uint32_t> longs;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant) longs.push_back(ref);
  }
  std::vector<Lit> bins;
  for (Lit a = 0; a < 2 * num_vars_; ++a) {
    for (const Watch& w : watches_[a]) {
      if (w.binary() && !w.redundant_binary() && a < w.blit) {
        bins.push_back(a);
        bins.push_back(w.blit);
      }
    }
  }
  const uint32_t nlong = static_cast<uint32_t>(longs.size());
  const uint32_t nclauses = nlong + static_cast<uint32_t>(bins.size() / 2);
  ls.clauses = nclauses;
  auto lits_of = [&](uint32_t id, uint32_t& n) -> const Lit* {
    if (id < nlong) {
      const Clause& c = clause(longs[id]);
      n = c.size;
      return c.lits();
    }
    n = 2;
    return bins.data() + 2 * size_t{id - nlong};
  };
  // A clause false under the current assignment.
  auto falsified = [&]() {
    for (uint32_t id = 0; id < nclauses; ++id) {
      uint32_t n;
      const Lit* l = lits_of(id, n);
      bool sat = false;
      for (uint32_t k = 0; k < n && !sat; ++k) sat = vals_[l[k]] >= 0;
      if (!sat) return true;
    }
    return false;
  };
  if (falsified()) return root_conflict();
  // Candidate domain clauses (3, 5 or 7 unassigned literals); the binary clauses between negations
  // of their literals, sorted for lookup.
  std::vector<uint8_t> cand_lit(2 * size_t{num_vars_}, 0);
  uint32_t ncand = 0;
  for (uint32_t id = 0; id < nlong; ++id) {
    uint32_t n;
    const Lit* l = lits_of(id, n);
    if (n != 3 && n != 5 && n != 7) continue;
    bool ok = true;
    for (uint32_t k = 0; k < n && ok; ++k) ok = !vals_[l[k]];
    if (!ok) continue;
    ++ncand;
    for (uint32_t k = 0; k < n; ++k) cand_lit[negate(l[k])] = 1;
  }
  if (!ncand) return finish(false);
  std::vector<uint64_t> binkeys;
  for (size_t i = 0; i < bins.size(); i += 2) {
    if (cand_lit[bins[i]] && cand_lit[bins[i + 1]]) binkeys.push_back((uint64_t{bins[i]} << 32) | bins[i + 1]);
  }
  std::sort(binkeys.begin(), binkeys.end());
  auto has_binary = [&](Lit a, Lit b) {
    if (a > b) std::swap(a, b);
    return std::binary_search(binkeys.begin(), binkeys.end(), (uint64_t{a} << 32) | b);
  };

  // Domains.
  constexpr uint32_t kNone = UINT32_MAX;
  std::vector<uint32_t> lit_group(2 * size_t{num_vars_}, kNone);
  std::vector<uint8_t> lit_value(2 * size_t{num_vars_}, 0);
  std::vector<uint8_t> var_used(num_vars_, 0);
  std::vector<uint32_t> group_start{0};
  std::vector<Lit> group_lits;
  uint64_t covered = 0;
  Lit buf[8];
  for (uint32_t id = 0; id < nlong; ++id) {
    uint32_t n;
    const Lit* l = lits_of(id, n);
    if (n != 3 && n != 5 && n != 7) continue;
    bool ok = true;
    for (uint32_t k = 0; k < n && ok; ++k) {
      buf[k] = l[k];
      ok = !vals_[l[k]] && !var_used[var_of(l[k])];
    }
    if (!ok) continue;
    for (uint32_t i = 1; i < n; ++i) {  // (input order; insertion sort: std::sort on a local
      const Lit x = buf[i];               // array trips a gcc false positive, -Warray-bounds)
      uint32_t j = i;
      for (; j > 0 && external_lit(x) < external_lit(buf[j - 1]); --j) buf[j] = buf[j - 1];
      buf[j] = x;
    }
    for (uint32_t i = 0; i < n && ok; ++i) {
      ok = i == 0 || var_of(buf[i]) != var_of(buf[i - 1]);
      for (uint32_t j = i + 1; j < n && ok; ++j) ok = has_binary(negate(buf[i]), negate(buf[j]));
    }
    if (!ok) continue;
    const uint32_t g = static_cast<uint32_t>(group_start.size() - 1);
    for (uint32_t i = 0; i < n; ++i) {
      lit_group[buf[i]] = g;
      lit_value[buf[i]] = static_cast<uint8_t>(i);
      var_used[var_of(buf[i])] = 1;
      group_lits.push_back(buf[i]);
    }
    group_start.push_back(static_cast<uint32_t>(group_lits.size()));
    ++ls.group_sizes[n];
    covered += 1 + n * (n - 1) / 2;
  }
  const uint32_t ngroups = static_cast<uint32_t>(group_start.size() - 1);
  ls.groups = ngroups;
  auto group_size = [&](uint32_t g) { return group_start[g + 1] - group_start[g]; };
  if (!ngroups) return finish(false);

  // Candidate constraint clauses: every literal the negation of a domain literal, one per domain.
  struct Rec {
    uint64_t hash;
    uint32_t start, k;
  };
  std::vector<uint32_t> gv;  // (domain << 3) | value, sorted by domain within a clause
  std::vector<Rec> recs;
  for (uint32_t id = 0; id < nclauses; ++id) {
    uint32_t n;
    const Lit* l = lits_of(id, n);
    if (n > 8) continue;
    bool ok = true;
    for (uint32_t k = 0; k < n && ok; ++k) ok = !vals_[l[k]] && lit_group[negate(l[k])] != kNone;
    if (!ok) continue;
    const uint32_t start = static_cast<uint32_t>(gv.size());
    for (uint32_t k = 0; k < n; ++k) {
      const Lit m = negate(l[k]);
      gv.push_back((lit_group[m] << 3) | lit_value[m]);
    }
    std::sort(gv.begin() + start, gv.end());
    uint64_t h = n;
    for (uint32_t k = 0; k < n && ok; ++k) {
      ok = k == 0 || (gv[start + k] >> 3) != (gv[start + k - 1] >> 3);
      h = mix_group(h, gv[start + k] >> 3);
    }
    if (!ok) {  // (an at-most-one clause of a domain, or implied by one)
      gv.resize(start);
      continue;
    }
    recs.push_back({h, start, n});
  }
  auto same_key = [&](const Rec& a, const Rec& b) {
    if (a.k != b.k || a.hash != b.hash) return false;
    for (uint32_t t = 0; t < a.k; ++t) {
      if ((gv[a.start + t] >> 3) != (gv[b.start + t] >> 3)) return false;
    }
    return true;
  };
  std::sort(recs.begin(), recs.end(), [&](const Rec& a, const Rec& b) {
    if (a.k != b.k) return a.k < b.k;
    if (a.hash != b.hash) return a.hash < b.hash;
    for (uint32_t t = 0; t < a.k; ++t) {
      const uint32_t x = gv[a.start + t] >> 3, y = gv[b.start + t] >> 3;
      if (x != y) return x < y;
    }
    return a.start < b.start;
  });

  // Equations: the allowed tuples of each constraint must be one affine hyperplane over GF(p).
  struct Equation {
    uint32_t start, k, p;  // domains eq_groups[start .. start + k), coefficients eq_coefs[...]
    uint8_t rhs;
  };
  std::vector<Equation> eqs;
  std::vector<uint32_t> eq_groups;
  std::vector<uint8_t> eq_coefs;
  constexpr uint32_t kMaxTable = 4096;
  std::vector<uint8_t> forbidden;
  std::vector<uint32_t> allowed;
  uint32_t coef[8], digit[8];
  for (size_t i = 0; i < recs.size();) {
    size_t j = i + 1;
    while (j < recs.size() && same_key(recs[i], recs[j])) ++j;
    const Rec& r0 = recs[i];
    const uint32_t k = r0.k, p = group_size(gv[r0.start] >> 3);
    bool ok = k >= 2;
    uint32_t total = 1;
    for (uint32_t t = 0; t < k && ok; ++t) {
      ok = group_size(gv[r0.start + t] >> 3) == p;
      total *= p;
      ok = ok && total <= kMaxTable;
    }
    if (ok) {
      forbidden.assign(total, 0);
      uint32_t distinct = 0;
      for (size_t x = i; x < j; ++x) {
        uint32_t idx = 0;
        for (uint32_t t = k; t-- > 0;) idx = idx * p + (gv[recs[x].start + t] & 7u);
        distinct += !forbidden[idx];
        forbidden[idx] = 1;
      }
      ok = distinct == total - total / p;
    }
    if (ok) {
      allowed.clear();
      for (uint32_t idx = 0; idx < total; ++idx) {
        if (!forbidden[idx]) allowed.push_back(idx);
      }
      // Coefficients c_0 = 1, c_t in 1..p-1 (an affine hyperplane has all of them nonzero here:
      // a zero coefficient would make the constraint independent of that domain, and then its
      // clauses would not mention it).
      for (uint32_t t = 0; t < k; ++t) coef[t] = 1;
      bool found = false;
      uint32_t rhs = 0;
      for (;;) {
        bool all = true;
        for (size_t a = 0; a < allowed.size() && all; ++a) {
          uint32_t idx = allowed[a], s = 0;
          for (uint32_t t = 0; t < k; ++t) {
            digit[t] = idx % p;
            idx /= p;
            s += coef[t] * digit[t];
          }
          s %= p;
          if (a == 0) rhs = s;
          all = s == rhs;
        }
        if (all) {
          found = true;
          break;
        }
        uint32_t t = 1;  // next coefficient vector (odometer over c_1 .. c_{k-1})
        while (t < k && coef[t] == p - 1) coef[t++] = 1;
        if (t == k) break;
        ++coef[t];
      }
      ok = found;
      if (found) {
        eqs.push_back({static_cast<uint32_t>(eq_groups.size()), k, p, static_cast<uint8_t>(rhs)});
        for (uint32_t t = 0; t < k; ++t) {
          eq_groups.push_back(gv[r0.start + t] >> 3);
          eq_coefs.push_back(static_cast<uint8_t>(coef[t]));
        }
        covered += j - i;
      }
    }
    if (!ok) ++ls.nonlinear;
    i = j;
  }
  ls.equations = eqs.size();
  ls.covered = covered;
  if (eqs.empty() || covered * 1000 < static_cast<uint64_t>(opts_.linmodmin) * nclauses) {
    if (opts_.verbose) {
      std::printf("c linmod: %u domains, %zu equations covering %.1f%% of %u clauses: not used\n", ngroups,
                  eqs.size(), nclauses ? 100.0 * static_cast<double>(covered) / nclauses : 0.0, nclauses);
    }
    return finish(false);
  }

  // Gaussian elimination per prime (dense, reduced row echelon form).
  std::vector<int> value(ngroups, -1);  // solution per domain (-1: in no equation)
  std::vector<uint32_t> col_of(ngroups, kNone);
  std::vector<uint32_t> cols;
  std::vector<uint8_t> m;
  bool inconsistent = false;
  for (const uint32_t p : {3u, 5u, 7u}) {
    cols.clear();
    uint32_t nrows = 0;
    for (const Equation& e : eqs) {
      if (e.p != p) continue;
      ++nrows;
      for (uint32_t t = 0; t < e.k; ++t) {
        const uint32_t g = eq_groups[e.start + t];
        if (col_of[g] == kNone) {
          col_of[g] = static_cast<uint32_t>(cols.size());
          cols.push_back(g);
        }
      }
    }
    if (!nrows) continue;
    const uint32_t ncols = static_cast<uint32_t>(cols.size()), width = ncols + 1;
    // Work bound: rows x columns x min(rows, columns) cell operations.
    const double work = static_cast<double>(nrows) * width * std::min(nrows, ncols);
    if (work > 4e9) {
      ++ls.skipped;
      for (const uint32_t g : cols) col_of[g] = kNone;
      continue;
    }
    ++ls.systems;
    ls.rows += nrows;
    ls.columns += ncols;
    m.assign(size_t{nrows} * width, 0);
    {
      uint32_t r = 0;
      for (const Equation& e : eqs) {
        if (e.p != p) continue;
        uint8_t* row = m.data() + size_t{r} * width;
        for (uint32_t t = 0; t < e.k; ++t) {
          uint8_t& x = row[col_of[eq_groups[e.start + t]]];
          x = static_cast<uint8_t>((x + eq_coefs[e.start + t]) % p);
        }
        row[ncols] = e.rhs;
        ++r;
      }
    }
    uint8_t inv[8] = {0};
    for (uint32_t a = 1; a < p; ++a) {
      for (uint32_t b = 1; b < p; ++b) {
        if (a * b % p == 1) inv[a] = static_cast<uint8_t>(b);
      }
    }
    std::vector<uint32_t> pivot_col;
    uint32_t rank = 0;
    for (uint32_t c = 0; c < ncols && rank < nrows; ++c) {
      uint32_t sel = rank;
      while (sel < nrows && !m[size_t{sel} * width + c]) ++sel;
      if (sel == nrows) continue;
      uint8_t* pr = m.data() + size_t{rank} * width;
      if (sel != rank) std::swap_ranges(pr, pr + width, m.data() + size_t{sel} * width);
      const uint32_t f = inv[pr[c]];
      for (uint32_t x = c; x < width; ++x) pr[x] = static_cast<uint8_t>(pr[x] * f % p);
      for (uint32_t r = 0; r < nrows; ++r) {
        uint8_t* row = m.data() + size_t{r} * width;
        if (r == rank || !row[c]) continue;
        const uint32_t g = p - row[c];  // row += g * pivot row
        for (uint32_t x = c; x < width; ++x) {
          if (pr[x]) row[x] = static_cast<uint8_t>((row[x] + g * pr[x]) % p);
        }
      }
      pivot_col.push_back(c);
      ++rank;
    }
    ls.rank += rank;
    for (uint32_t r = rank; r < nrows; ++r) inconsistent = inconsistent || m[size_t{r} * width + ncols];
    if (inconsistent) break;
    for (uint32_t c = 0; c < ncols; ++c) value[cols[c]] = 0;  // free variables 0
    for (uint32_t r = 0; r < rank; ++r) value[cols[pivot_col[r]]] = m[size_t{r} * width + ncols];
    for (const uint32_t g : cols) col_of[g] = kNone;
  }
  if (inconsistent) {
    ++ls.inconsistent;
    if (opts_.verbose) {
      std::printf("c linmod: %u domains, %zu equations covering %.1f%% of %u clauses: inconsistent (no proof: ignored)\n",
                  ngroups, eqs.size(), 100.0 * static_cast<double>(covered) / nclauses, nclauses);
    }
    return finish(false);
  }
  if (!ls.systems) return finish(false);

  // Try the solution as an assignment (decisions with propagation, as the lucky pass does).
  ++ls.attempts;
  bool ok = true;
  for (uint32_t g = 0; g < ngroups && ok; ++g) {
    if (value[g] < 0) continue;
    const Lit l = group_lits[group_start[g] + static_cast<uint32_t>(value[g])];
    if (vals_[l] > 0) continue;
    if (vals_[l] < 0) {
      ok = false;
      break;
    }
    control_.push_back(static_cast<uint32_t>(trail_.size()));
    assign(l, kNoReason);
    ok = propagate_vivify(kNoReason);
  }
  for (Var i = 0; i < num_vars_ && ok; ++i) {
    const Var v = internal_var(i);  // (input order)
    if (eliminated_[v] || vals_[make_lit(v, false)] != 0) continue;
    control_.push_back(static_cast<uint32_t>(trail_.size()));
    assign(make_lit(v, saved_[v] < 0), kNoReason);
    ok = propagate_vivify(kNoReason);
  }
  // (every clause is checked again: a model of the irredundant clauses is a model of the formula)
  const bool model = ok && trail_.size() + inactive_ == num_vars_ && !falsified();
  if (opts_.verbose) {
    std::printf("c linmod: %u domains, %zu equations covering %.1f%% of %u clauses, %llu systems (%llu x %llu, rank %llu): %s\n",
                ngroups, eqs.size(), 100.0 * static_cast<double>(covered) / nclauses, nclauses,
                static_cast<unsigned long long>(ls.systems), static_cast<unsigned long long>(ls.rows),
                static_cast<unsigned long long>(ls.columns), static_cast<unsigned long long>(ls.rank),
                model ? "model" : "the solution conflicts with the other clauses (kept as phases)");
  }
  if (model) {
    ++ls.models;
    extend_model();
    return finish(true);
  }
  ++ls.conflicts;
  backtrack(0);
  return finish(false);
}

}  // namespace psat
