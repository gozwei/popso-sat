// Gauss-Jordan elimination on XOR constraints (--gauss).
//
// XOR constraints x1 + ... + xn = p (n <= gaussmaxsize) are recognized from complete clause
// encodings: all 2^(n-1) clauses over the n variables whose number of negative literals has the
// parity 1 - p (each excludes one assignment of the wrong parity). Binary clauses count
// (equivalences are XORs of two variables); chunked long XORs (auxiliary variables linking short
// XORs) need nothing special, the auxiliary variables are columns like any other.
//
// Soundness design. Gauss-Jordan reasoning is not written to the DRAT proof (yet). It runs in a
// detached solver: a second Solver object, built from a copy of the main solver's irredundant
// clauses and root units, with Gauss-Jordan propagation on, no proof, and none of the
// simplifications that would remove XOR variables (elimination, BVA, sweeping). The main solver
// gives it a share of its search effort in rounds. If it finds a model, that model satisfies the
// copied formula; the main solver extends it with its reconstruction stack as it was at the time
// of the copy (empty when the copy is made before preprocessing, as it is now) and answers SAT;
// the command line checks the model against the input formula as usual. Nothing else ever flows
// back: no clause, unit, phase or score of the detached solver reaches the main solver's clause
// database or the proof, so UNSAT answers stay fully proof-producing. An UNSAT result of the
// detached solver is not trusted for the answer (it has no proof); it just ends the rounds.
//
// Propagation (in the detached solver) runs at the fixpoint of unit propagation, over the trail
// literals not yet in the matrices' "view" (gauss_qhead_), following Han & Jiang (CAV 2012):
// each matrix is kept in reduced row echelon form over one basic column per row; an open row has
// its basic column and a watched non-basic column unassigned in the view. Assigning the basic
// column of a row that has another unassigned column makes that column basic (pivot: eliminated
// from every other row); a row with one unassigned column propagates it (the reason is the row as
// a clause, copied into gauss_reasons_), a row with none is satisfied or a conflict. A row closed
// this way keeps two columns assigned on the current level as its basic and watched columns, so
// backtracking below the level reopens it with valid watches; rows closed without two such
// columns are checked again from a stack when their level is backtracked. Row operations only
// add rows, so the matrices stay equivalent to the XORs and need no undo.

#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdio>

#include "psat/core/small_sort.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

constexpr uint32_t kNone = GaussMatrix::kNone;

uint64_t mix64(uint64_t h) {
  h ^= h >> 33;
  h *= 0xFF51AFD7ED558CCDull;
  h ^= h >> 33;
  h *= 0xC4CEB9FE1A85EC53ull;
  h ^= h >> 33;
  return h;
}

// Saturating 8-bit counters indexed by a hash: count(h) >= the number of add(h) calls. Filters
// the clauses whose variable set occurs often enough to be an XOR encoding before the exact pass.
class SetFilter {
 public:
  explicit SetFilter(size_t keys) {
    size_t n = 1024;
    while (n < 2 * keys && n < (size_t{1} << 26)) n <<= 1;
    counts_.assign(n, 0);
    mask_ = n - 1;
  }
  void add(uint64_t h) {
    uint8_t& c = counts_[mix64(h) & mask_];
    if (c < 255) ++c;
  }
  uint32_t count(uint64_t h) const { return counts_[mix64(h) & mask_]; }

 private:
  std::vector<uint8_t> counts_;
  uint64_t mask_ = 0;
};

// Connected components of the XORs (union-find over variables). comp[i]: the component index of
// XOR i (dense, 0..count-1); variables assigned in `assigned` (if given) do not connect XORs.
uint32_t xor_components(const XorList& xors, uint32_t nvars, std::vector<uint32_t>& comp,
                        const std::vector<int8_t>* vals) {
  std::vector<uint32_t> parent(nvars);
  for (uint32_t v = 0; v < nvars; ++v) parent[v] = v;
  auto find = [&](uint32_t v) {
    while (parent[v] != v) {
      parent[v] = parent[parent[v]];
      v = parent[v];
    }
    return v;
  };
  auto active = [&](Var v) { return !vals || (*vals)[make_lit(v, false)] == 0; };
  for (size_t i = 0; i < xors.size(); ++i) {
    Var first = kNone;
    for (uint32_t k = xors.start[i]; k < xors.start[i + 1]; ++k) {
      const Var v = xors.vars[k];
      if (!active(v)) continue;
      if (first == kNone) {
        first = v;
      } else {
        const uint32_t a = find(first), b = find(v);
        if (a != b) parent[a] = b;
      }
    }
  }
  std::vector<uint32_t> index(nvars, kNone);
  uint32_t count = 0;
  comp.assign(xors.size(), kNone);
  for (size_t i = 0; i < xors.size(); ++i) {
    for (uint32_t k = xors.start[i]; k < xors.start[i + 1]; ++k) {
      const Var v = xors.vars[k];
      if (!active(v)) continue;
      const uint32_t root = find(v);
      if (index[root] == kNone) index[root] = count++;
      comp[i] = index[root];
      break;
    }
  }
  return count;
}

}  // namespace

// --- XOR extraction -------------------------------------------------------------------------

void Solver::extract_xors(XorList& out, uint64_t max_size) {
  if (max_size > 8) max_size = 8;
  struct Row {
    Var vars[8];
    uint64_t hash;
    uint8_t n, mask;
  };
  // Clauses as they are at the root: satisfied ones skipped, false literals removed (an XOR with
  // a root-assigned variable is an XOR over the others, encoded by the reduced clauses).
  auto make_row = [&](const Lit* lits, uint32_t size, Row& r) -> bool {
    Lit tmp[8];
    uint32_t n = 0;
    for (uint32_t k = 0; k < size; ++k) {
      const int8_t x = vals_[lits[k]];
      if (x > 0) return false;
      if (x < 0) continue;
      if (n == max_size) return false;
      tmp[n++] = lits[k];
    }
    if (n < 2) return false;
    small_sort(tmp, n);
    r.n = static_cast<uint8_t>(n);
    r.mask = 0;
    uint64_t h = 0x9E3779B97F4A7C15ull * n;
    for (uint32_t k = 0; k < n; ++k) {
      if (k && var_of(tmp[k]) == var_of(tmp[k - 1])) return false;
      r.vars[k] = var_of(tmp[k]);
      if (is_negative(tmp[k])) r.mask = static_cast<uint8_t>(r.mask | (1u << k));
      h = (h ^ r.vars[k]) * 0x100000001B3ull;
    }
    r.hash = h;
    return true;
  };
  // Candidates: irredundant binary clauses (once, from the smaller literal's watch list) and
  // irredundant long clauses with at most max_size unassigned literals (see make_row).
  auto for_each_candidate = [&](auto&& f) {
    for (Lit a = 0; a < 2 * num_vars_; ++a) {
      for (const Watch& w : watches_[a]) {
        if (!w.binary() || w.redundant_binary() || w.blit < a) continue;
        const Lit c[2] = {a, w.blit};
        f(c, 2u);
      }
    }
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant || c.size > 2 * max_size) continue;
      f(c.lits(), c.size);
    }
  };
  size_t candidates = 0;
  for_each_candidate([&](const Lit*, uint32_t) { ++candidates; });
  if (candidates < 2) return;
  SetFilter filter(candidates);
  for_each_candidate([&](const Lit* lits, uint32_t n) {
    Row r;
    if (make_row(lits, n, r)) filter.add(r.hash);
  });
  std::vector<Row> rows;
  // (an encoding of n >= 3 variables may lack up to a quarter of its clauses: see below)
  for_each_candidate([&](const Lit* lits, uint32_t n) {
    Row r;
    if (make_row(lits, n, r) && filter.count(r.hash) >= (r.n >= 3 ? 3u << (r.n - 3) : 2u)) rows.push_back(r);
  });
  // An encoding clause may be missing because a binary clause over two of its literals subsumes
  // it (the XOR is still implied, clause by clause, which is all that propagation and the RUP
  // steps of a refutation need). At most a quarter of the encoding: with more missing, the
  // "XOR" is mostly binary clauses (exactly-one constraints over three variables are XORs too)
  // and not the structure Gauss-Jordan is for.
  uint64_t lookups = 0;
  auto binary_present = [&](Lit a, Lit b) {
    const std::vector<Watch>& ws = watches_[a].size() <= watches_[b].size() ? watches_[a] : watches_[b];
    const Lit other = watches_[a].size() <= watches_[b].size() ? b : a;
    lookups += ws.size() / 8 + 1;
    for (const Watch& w : ws) {
      if (w.binary() && w.blit == other) return true;
    }
    return false;
  };
  std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
    if (a.n != b.n) return a.n < b.n;
    if (a.hash != b.hash) return a.hash < b.hash;
    for (int k = 0; k < a.n; ++k) {
      if (a.vars[k] != b.vars[k]) return a.vars[k] < b.vars[k];
    }
    return a.mask < b.mask;
  });
  for (size_t i = 0; i < rows.size();) {
    size_t j = i;
    while (j < rows.size() && rows[j].n == rows[i].n && rows[j].hash == rows[i].hash &&
           std::equal(rows[i].vars, rows[i].vars + rows[i].n, rows[j].vars)) {
      ++j;
    }
    const uint32_t n = rows[i].n;
    const uint32_t need = 1u << (n - 1);
    uint32_t count[2] = {0, 0};
    int last = -1;
    for (size_t k = i; k < j; ++k) {
      if (rows[k].mask == last) continue;  // duplicate clause
      last = rows[k].mask;
      ++count[std::popcount(static_cast<unsigned>(rows[k].mask)) & 1];
    }
    for (int q = 0; q < 2; ++q) {
      if (count[q] == need) {
        out.push(rows[i].vars, n, static_cast<uint8_t>(1 - q));
        out.covered += need;
        continue;
      }
      if (n < 3 || 4 * count[q] < 3 * need || lookups > 64 * candidates) continue;
      uint64_t present[4] = {0, 0, 0, 0};  // masks of parity class q present
      for (size_t k = i; k < j; ++k) {
        const uint32_t mk = rows[k].mask;
        if ((std::popcount(mk) & 1u) == static_cast<uint32_t>(q)) present[mk >> 6] |= uint64_t{1} << (mk & 63);
      }
      bool complete = true;
      for (uint32_t mk = 0; mk < (1u << n) && complete; ++mk) {
        if ((std::popcount(mk) & 1u) != static_cast<uint32_t>(q) || ((present[mk >> 6] >> (mk & 63)) & 1u)) continue;
        bool subsumed = false;
        for (uint32_t a = 0; a < n && !subsumed; ++a) {
          for (uint32_t b = a + 1; b < n && !subsumed; ++b) {
            subsumed = binary_present(make_lit(rows[i].vars[a], (mk >> a) & 1u), make_lit(rows[i].vars[b], (mk >> b) & 1u));
          }
        }
        complete = subsumed;
      }
      if (!complete) continue;
      out.push(rows[i].vars, n, static_cast<uint8_t>(1 - q));
      out.covered += count[q];
      ++out.subsumed;
    }
    i = j;
  }
}

// --- Main solver: the detached Gauss-Jordan solver ------------------------------------------

bool Solver::gauss_start() {
  const PassTimer pass_timer(*this, kPassGauss);
  const auto t0 = std::chrono::steady_clock::now();
  GaussStats& gs = gauss_stats_;
  XorList xors;
  extract_xors(xors, static_cast<uint64_t>(opts_.gaussmaxsize));
  gs.xors = xors.size();
  for (size_t i = 0; i < xors.size(); ++i) ++gs.xor_sizes[xors.start[i + 1] - xors.start[i]];
  gs.covered = xors.covered;
  gs.subsumed = xors.subsumed;
  gs.clauses = irredundant_ + binaries_irredundant_;
  std::vector<uint32_t> comp;
  const uint32_t ncomp = xor_components(xors, num_vars_, comp, nullptr);
  std::vector<uint32_t> comp_rows(ncomp, 0);
  for (const uint32_t c : comp) {
    if (c != kNone) ++comp_rows[c];
  }
  uint64_t largest = 0;
  for (const uint32_t r : comp_rows) {
    if (r >= 2) ++gs.components;
    largest = std::max<uint64_t>(largest, r);
  }
  gs.detect_seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  gs.gated = gs.xors >= static_cast<uint64_t>(opts_.gaussxors) &&
             gs.covered * 1000 >= static_cast<uint64_t>(opts_.gaussmin) * std::max<uint64_t>(gs.clauses, 1) &&
             arena_.size() + 2 * gs.clauses <= static_cast<uint64_t>(opts_.gausswords) << 20;
  if (opts_.verbose) {
    std::printf("c gauss: %llu xors (", static_cast<unsigned long long>(gs.xors));
    bool first = true;
    for (int k = 2; k <= 8; ++k) {
      if (!gs.xor_sizes[k]) continue;
      std::printf("%s%d: %llu", first ? "" : ", ", k, static_cast<unsigned long long>(gs.xor_sizes[k]));
      first = false;
    }
    if (gs.subsumed) std::printf("; %llu with subsumed clauses", static_cast<unsigned long long>(gs.subsumed));
    std::printf(") covering %llu of %llu clauses (%.1f%%), %llu components (largest %llu xors), %.3f s: %s\n",
                static_cast<unsigned long long>(gs.covered), static_cast<unsigned long long>(gs.clauses),
                gs.clauses ? 100.0 * static_cast<double>(gs.covered) / static_cast<double>(gs.clauses) : 0.0,
                static_cast<unsigned long long>(gs.components), static_cast<unsigned long long>(largest),
                gs.detect_seconds, gs.gated ? "detached solver" : "skipped");
    std::fflush(stdout);
  }
  // An inconsistent XOR system is refuted right away, with a proof (gauss_proof.cpp).
  if (opts_.gaussproof && gs.components && gauss_refute(xors)) return false;
  if (!gs.gated) return false;

  Options so = opts_;
  so.gauss = 0;
  so.eliminate = 0;  // (also BVA, congruence and substitution, which run inside elimination rounds)
  so.sweep = 0;
  so.chrono = 0;
  so.cardinality = 0;
  so.lucky = 0;
  so.walk = 0;  // (local search on XOR encodings: wasted)
  so.verbose = opts_.verbose >= 3 ? opts_.verbose : 0;
  auto sub = std::make_unique<Solver>(so);
  sub->start_ = start_;
  sub->reserve(static_cast<int>(num_vars_));
  std::vector<int> cl;
  for (const Lit l : trail_) {
    const int u = to_dimacs(l);
    sub->add_clause(&u, 1);
  }
  for (Lit a = 0; a < 2 * num_vars_; ++a) {
    for (const Watch& w : watches_[a]) {
      if (!w.binary() || w.redundant_binary() || w.blit < a) continue;
      const int c2[2] = {to_dimacs(a), to_dimacs(w.blit)};
      sub->add_clause(c2, 2);
    }
  }
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    cl.clear();
    for (uint32_t k = 0; k < c.size; ++k) cl.push_back(to_dimacs(c.lits()[k]));
    sub->add_clause(cl.data(), cl.size());
  }
  gauss_sub_vars_ = num_vars_;
  gauss_ext_size_ = extension_.size();
  gs.started = true;
  sub->gauss_on_ = true;
  if (sub->inconsistent_ || !sub->gauss_init(xors)) {
    gs.sub_result = kUnsat;
    gs.matrices = sub->gauss_stats_.matrices;
    if (opts_.verbose) std::printf("c gauss: the XORs are inconsistent (detached solver; no proof)\n");
    return false;
  }
  gs.matrices = sub->gauss_stats_.matrices;
  gs.matrix_rows = sub->gauss_stats_.matrix_rows;
  gs.matrix_cols = sub->gauss_stats_.matrix_cols;
  gs.skipped_matrices = sub->gauss_stats_.skipped_matrices;
  gs.rank_deficit = sub->gauss_stats_.rank_deficit;
  gs.root_units = sub->gauss_stats_.root_units;
  if (opts_.verbose) {
    std::printf("c gauss: %llu matrices (%llu rows, %llu columns in all; %llu dependent rows dropped, %llu too large)\n",
                static_cast<unsigned long long>(gs.matrices), static_cast<unsigned long long>(gs.matrix_rows),
                static_cast<unsigned long long>(gs.matrix_cols), static_cast<unsigned long long>(gs.rank_deficit),
                static_cast<unsigned long long>(gs.skipped_matrices));
    std::fflush(stdout);
  }
  if (!gs.matrices) return false;  // nothing to propagate: the detached solver would only repeat the search
  gauss_sub_ = std::move(sub);
  gauss_last_ticks_ = stats_.ticks;
  gauss_next_ticks_ = stats_.ticks + (static_cast<uint64_t>(opts_.gaussint) * 1000);
  const uint64_t max_share = static_cast<uint64_t>(opts_.gausseffort);
  gauss_share_ = opts_.gaussadapt ? std::max<uint64_t>(max_share / 8, 1) : max_share;
  gs.share = gs.max_share = gauss_share_;
  const bool found = gauss_run(static_cast<uint64_t>(opts_.gaussinit) * 1000);
  gauss_granted_ = gauss_used_ = 0;  // (the first run is not part of the share)
  return found;
}

// A round of the detached solver with its share of the search ticks since the last round.
//
// Adaptive share (--gaussadapt): what the detached solver adds is Gauss-Jordan reasoning that unit
// propagation on the XOR clauses does not find, and its Gauss-Jordan conflicts measure it. Over
// at least 64 conflicts (or 4 rounds), at >= gaussgrow per mille of its conflicts the share
// doubles (up to gausseffort), below gaussshrink per mille it halves, and below 1/64 of
// gausseffort the detached solver is stopped. Measured (copy conflicts that are Gauss-Jordan
// conflicts): par32 36-41%, xorshift 17%, sliding-puzzle puzzle32 0.02%, algebra hantzsche_wendt
// 0 (its 414 small matrices never propagate before the clauses do).
bool Solver::gauss_round() {
  const uint64_t spent = stats_.ticks - gauss_last_ticks_;
  gauss_last_ticks_ = stats_.ticks;
  gauss_next_ticks_ = stats_.ticks + static_cast<uint64_t>(opts_.gaussint) * 1000;
  GaussStats& gs = gauss_stats_;
  const uint64_t max_share = static_cast<uint64_t>(opts_.gausseffort);
  if (opts_.gaussadapt) {
    const Solver& s = *gauss_sub_;
    const uint64_t dc = s.stats_.conflicts - gauss_eval_conflicts_;
    const uint64_t dg = s.gauss_stats_.conflicts - gauss_eval_gauss_conflicts_;
    if (dc >= 64 || ++gauss_eval_rounds_ >= 4) {
      const uint64_t old = gauss_share_;
      if (dc >= 64 && dg * 1000 >= static_cast<uint64_t>(opts_.gaussgrow) * dc) {
        gauss_share_ = std::min(2 * gauss_share_, max_share);
        if (gauss_share_ > old) ++gs.grown;
      } else if (dg * 1000 < static_cast<uint64_t>(opts_.gaussshrink) * std::max<uint64_t>(dc, 1)) {
        gauss_share_ /= 2;
        ++gs.shrunk;
      }
      gauss_eval_conflicts_ = s.stats_.conflicts;
      gauss_eval_gauss_conflicts_ = s.gauss_stats_.conflicts;
      gauss_eval_rounds_ = 0;
      gs.share = gauss_share_;
      gs.max_share = std::max(gs.max_share, gauss_share_);
      if (opts_.verbose >= 2 && gauss_share_ != old) {
        std::printf("c [%.2f s] gauss share %llu -> %llu per mille (%llu of %llu conflicts by Gauss-Jordan)\n", seconds(),
                    static_cast<unsigned long long>(old), static_cast<unsigned long long>(gauss_share_),
                    static_cast<unsigned long long>(dg), static_cast<unsigned long long>(dc));
      }
      if (64 * gauss_share_ < max_share) {
        gs.stopped = true;
        if (opts_.verbose) {
          std::printf("c [%.2f s] gauss: detached solver stopped (%llu of %llu conflicts by Gauss-Jordan)\n", seconds(),
                      static_cast<unsigned long long>(dg), static_cast<unsigned long long>(dc));
          std::fflush(stdout);
        }
        gauss_sub_.reset();
        return false;
      }
    }
  }
  gauss_granted_ += spent * gauss_share_ / 1000;
  if (gauss_granted_ <= gauss_used_) return false;  // (paying back an overshoot)
  return gauss_run(gauss_granted_ - gauss_used_);
}

bool Solver::gauss_run(uint64_t ticks) {
  if (!gauss_sub_) return false;
  Solver& s = *gauss_sub_;
  GaussStats& gs = gauss_stats_;
  ++gs.rounds;
  s.ticks_limit_ = s.stats_.ticks + std::max<uint64_t>(ticks, 1);
  s.time_limit_ = time_limit_;
  s.terminate_ = terminate_;
  int res = kUnknown;
  const uint64_t before = s.stats_.ticks;
  {
    const PassTimer pass_timer(*this, kPassGauss);
    res = s.solve();
  }
  gauss_used_ += s.stats_.ticks - before;
  gs.sub_ticks = s.stats_.ticks;
  gs.sub_conflicts = s.stats_.conflicts;
  gs.propagations = s.gauss_stats_.propagations;
  gs.conflicts = s.gauss_stats_.conflicts;
  gs.pivots = s.gauss_stats_.pivots;
  gs.row_checks = s.gauss_stats_.row_checks;
  gs.reopened = s.gauss_stats_.reopened;
  gs.root_units = s.gauss_stats_.root_units;
  gs.sub_result = res;
  if (opts_.verbose >= 2 || (opts_.verbose && res != kUnknown)) {
    std::printf("c [%.2f s] gauss round %llu: %s, %llu conflicts, %llu gauss propagations, %llu gauss conflicts, "
                "%llu propagations, %llu ticks, main ticks %llu\n",
                seconds(), static_cast<unsigned long long>(gs.rounds),
                res == kSat ? "model" : res == kUnsat ? "unsatisfiable (no proof: ignored)" : "unknown",
                static_cast<unsigned long long>(s.stats_.conflicts),
                static_cast<unsigned long long>(s.gauss_stats_.propagations),
                static_cast<unsigned long long>(s.gauss_stats_.conflicts),
                static_cast<unsigned long long>(s.stats_.propagations), static_cast<unsigned long long>(s.stats_.ticks),
                static_cast<unsigned long long>(stats_.ticks));
    std::fflush(stdout);
  }
  if (res == kSat) {
    gauss_import_model();
    gs.model = true;
    gauss_sub_.reset();
    return true;
  }
  if (res == kUnsat) gauss_sub_.reset();
  return false;
}

// The detached solver's model satisfies the formula as it was copied; the main solver's
// reconstruction stack as of the copy extends it to the variables eliminated before.
void Solver::gauss_import_model() {
  model_.assign(num_vars_, -1);
  const uint32_t n = std::min(gauss_sub_vars_, num_vars_);
  for (Var v = 0; v < n; ++v) model_[v] = gauss_sub_->val(static_cast<int>(v) + 1) > 0 ? 1 : -1;
  reconstruct_model(gauss_ext_size_);
  model_valid_ = true;
}

// --- Gauss-Jordan propagation (detached solver) -----------------------------------------------

bool Solver::gauss_init(const XorList& xors) {
  GaussStats& gs = gauss_stats_;
  gauss_mat_.assign(num_vars_, kNone);
  gauss_col_.assign(num_vars_, kNone);
  auto value_of = [&](Var v) -> int { return vals_[make_lit(v, false)]; };
  // XORs over root-assigned variables only: consistency check.
  for (size_t i = 0; i < xors.size(); ++i) {
    bool open = false;
    uint8_t p = xors.rhs[i];
    for (uint32_t k = xors.start[i]; k < xors.start[i + 1]; ++k) {
      const int x = value_of(xors.vars[k]);
      if (!x) open = true;
      if (x > 0) p ^= 1;
    }
    if (!open && p) return false;
  }
  std::vector<uint32_t> comp;
  const uint32_t ncomp = xor_components(xors, num_vars_, comp, &vals_);
  std::vector<std::vector<uint32_t>> members(ncomp);
  for (size_t i = 0; i < xors.size(); ++i) {
    if (comp[i] != kNone) members[comp[i]].push_back(static_cast<uint32_t>(i));
  }
  const uint64_t max_bits = static_cast<uint64_t>(opts_.gaussmatrix) << 20;
  std::vector<uint32_t> col_of(num_vars_, kNone);
  for (uint32_t ci = 0; ci < ncomp; ++ci) {
    const std::vector<uint32_t>& rows = members[ci];
    if (rows.size() < 2) continue;
    std::vector<Var> cols;
    for (const uint32_t i : rows) {
      for (uint32_t k = xors.start[i]; k < xors.start[i + 1]; ++k) {
        const Var v = xors.vars[k];
        if (!value_of(v) && col_of[v] == kNone) {
          col_of[v] = 0;
          cols.push_back(v);
        }
      }
    }
    std::sort(cols.begin(), cols.end());
    for (uint32_t c = 0; c < cols.size(); ++c) col_of[cols[c]] = c;
    const uint64_t nbits = uint64_t{rows.size()} * cols.size();
    if (nbits > max_bits) {
      ++gs.skipped_matrices;
      for (const Var v : cols) col_of[v] = kNone;
      continue;
    }
    GaussMatrix M;
    M.ncols = static_cast<uint32_t>(cols.size());
    M.words = (M.ncols + 63) / 64;
    M.nrows = static_cast<uint32_t>(rows.size());
    M.bits.assign(size_t{M.nrows} * M.words, 0);
    M.rhs.assign(M.nrows, 0);
    for (uint32_t r = 0; r < M.nrows; ++r) {
      const uint32_t i = rows[r];
      uint8_t p = xors.rhs[i];
      uint64_t* R = M.row(r);
      for (uint32_t k = xors.start[i]; k < xors.start[i + 1]; ++k) {
        const Var v = xors.vars[k];
        const int x = value_of(v);
        if (x) {
          if (x > 0) p ^= 1;
          continue;
        }
        const uint32_t c = col_of[v];
        R[c >> 6] ^= uint64_t{1} << (c & 63);
      }
      M.rhs[r] = p;
    }
    // Reduced row echelon form (Gauss-Jordan). Row `rank` is zero left of column c (earlier
    // pivot columns are cleared everywhere else, other earlier columns are zero in rows >= rank).
    std::vector<uint32_t> basic;
    uint32_t rank = 0;
    uint64_t work = 0;
    for (uint32_t c = 0; c < M.ncols && rank < M.nrows; ++c) {
      uint32_t p = rank;
      while (p < M.nrows && !GaussMatrix::test(M.row(p), c)) ++p;
      work += p - rank + 1;
      if (p == M.nrows) continue;
      if (p != rank) {
        std::swap_ranges(M.row(p), M.row(p) + M.words, M.row(rank));
        std::swap(M.rhs[p], M.rhs[rank]);
      }
      const uint64_t* P = M.row(rank);
      const uint32_t w0 = c >> 6;
      for (uint32_t r = 0; r < M.nrows; ++r) {
        if (r == rank) continue;
        uint64_t* R = M.row(r);
        if (!GaussMatrix::test(R, c)) continue;
        for (uint32_t w = w0; w < M.words; ++w) R[w] ^= P[w];
        M.rhs[r] ^= M.rhs[rank];
        work += M.words - w0;
      }
      work += M.nrows;
      basic.push_back(c);
      ++rank;
    }
    stats_.ticks += work / 8;
    for (uint32_t r = rank; r < M.nrows; ++r) {
      if (M.rhs[r]) return false;  // 0 = 1
    }
    gs.rank_deficit += M.nrows - rank;
    if (rank == 0) {
      for (const Var v : cols) col_of[v] = kNone;
      continue;
    }
    M.nrows = rank;
    M.bits.resize(size_t{rank} * M.words);
    M.rhs.resize(rank);
    M.col_var = cols;
    M.basic = basic;
    M.basic_row.assign(M.ncols, kNone);
    for (uint32_t r = 0; r < rank; ++r) M.basic_row[basic[r]] = r;
    M.watch.assign(rank, kNone);
    M.watchers.assign(M.ncols, {});
    M.assigned.assign(M.words, 0);
    M.values.assign(M.words, 0);
    M.queued.assign(rank, 0);
    const uint32_t m = static_cast<uint32_t>(gauss_mats_.size());
    for (uint32_t c = 0; c < M.ncols; ++c) {
      gauss_mat_[cols[c]] = m;
      gauss_col_[cols[c]] = c;
      col_of[cols[c]] = kNone;
    }
    ++gs.matrices;
    gs.matrix_rows += rank;
    gs.matrix_cols += M.ncols;
    gauss_mats_.push_back(std::move(M));
    for (uint32_t r = 0; r < rank; ++r) gauss_enqueue(m, r);
  }
  gauss_qhead_ = 0;
  gauss_free_.clear();
  for (Var v = 0; v < num_vars_; ++v) {
    if (gauss_mat_[v] == kNone && !value_of(v)) gauss_free_.push_back(v);
  }
  if (gauss_free_.size() > 4096) gauss_free_.clear();  // (a linear scan per decision)
  return true;
}

// Decisions on matrix variables are guesses within the linear part, which Gauss-Jordan propagation
// handles completely once the other variables are fixed (a consistent system never conflicts):
// decide the most active variable outside the matrices first, if one is unassigned.
Var Solver::gauss_decision(Var linear) {
  Var best = kNone;
  for (const Var v : gauss_free_) {
    if (vals_[make_lit(v, false)] != 0) continue;
    if (best == kNone || (stable_ ? score_[v] > score_[best] : bumped_[v] > bumped_[best])) best = v;
  }
  stats_.ticks += gauss_free_.size() / 16 + 1;
  return best == kNone ? linear : best;
}

bool Solver::propagate_with_gauss() {
  for (;;) {
    if (!propagate_impl<false>(kNoReason)) return false;
    if (!gauss_propagate()) {
      has_conflict_ = true;
      conflict_ref_ = kGaussConflict;
      // The conflict normally has a literal on the current level (the row was checked when one of
      // its literals entered the view, and literals beyond the view are on the current level);
      // if not, the conflict is analyzed on its highest level.
      uint32_t top = 0;
      for (const Lit l : gauss_conflict_) top = std::max(top, vdata_[var_of(l)].level);
      if (top < level()) backtrack(top);
      return false;
    }
    if (propagated_ == trail_.size()) return true;
  }
}

bool Solver::gauss_propagate() {
  if (!gauss_process_queue()) return false;
  while (gauss_qhead_ < trail_.size()) {
    const Lit lit = trail_[gauss_qhead_++];
    const Var v = var_of(lit);
    const uint32_t m = gauss_mat_[v];
    if (m == kNone) continue;
    GaussMatrix& M = gauss_mats_[m];
    const uint32_t c = gauss_col_[v];
    const uint64_t bit = uint64_t{1} << (c & 63);
    M.assigned[c >> 6] |= bit;
    if (is_negative(lit)) {
      M.values[c >> 6] &= ~bit;
    } else {
      M.values[c >> 6] |= bit;
    }
    if (M.basic_row[c] != kNone) gauss_enqueue(m, M.basic_row[c], c);
    std::vector<uint32_t>& ws = M.watchers[c];
    for (const uint32_t r : ws) {
      if (M.watch[r] == c) gauss_enqueue(m, r, c);
    }
    ws.clear();
    if (!gauss_process_queue()) return false;
  }
  return true;
}

bool Solver::gauss_process_queue() {
  while (!gauss_queue_.empty()) {
    const GaussQueued q = gauss_queue_.back();
    gauss_queue_.pop_back();
    gauss_mats_[q.matrix].queued[q.row] = 0;
    if (!gauss_fix_row(q.matrix, q.row, q.trigger)) return false;
  }
  return true;
}

// The rows changed are checked again; `trigger` (the column being processed, if any) is a
// candidate watch for them if they close.
void Solver::gauss_pivot(uint32_t m, uint32_t r, uint32_t col, uint32_t trigger) {
  GaussMatrix& M = gauss_mats_[m];
  ++gauss_stats_.pivots;
  const uint32_t old = M.basic[r];
  if (old != kNone) M.basic_row[old] = kNone;
  M.basic[r] = col;
  M.basic_row[col] = r;
  const uint64_t* P = M.row(r);
  uint32_t lo = 0, hi = M.words;
  while (lo < hi && !P[lo]) ++lo;
  while (hi > lo && !P[hi - 1]) --hi;
  const uint32_t cw = col >> 6;
  const uint64_t cb = uint64_t{1} << (col & 63);
  uint64_t work = M.nrows;
  for (uint32_t r2 = 0; r2 < M.nrows; ++r2) {
    if (r2 == r) continue;
    uint64_t* R = M.row(r2);
    if (!(R[cw] & cb)) continue;
    for (uint32_t w = lo; w < hi; ++w) R[w] ^= P[w];
    M.rhs[r2] ^= M.rhs[r];
    work += hi - lo;
    gauss_enqueue(m, r2, trigger);
  }
  stats_.ticks += work / 8 + 1;
}

void Solver::gauss_conflict_from_row(uint32_t m, uint32_t r) {
  const GaussMatrix& M = gauss_mats_[m];
  const uint64_t* R = M.row(r);
  gauss_conflict_.clear();
  for (uint32_t w = 0; w < M.words; ++w) {
    for (uint64_t x = R[w]; x; x &= x - 1) {
      const Var v = M.col_var[w * 64 + static_cast<uint32_t>(std::countr_zero(x))];
      gauss_conflict_.push_back(make_lit(v, vals_[make_lit(v, false)] > 0));  // the false literal
    }
  }
  ++gauss_stats_.conflicts;
}

// Checks row r against the view; restores the watches, pivots, propagates or reports a conflict.
// A row left with at most one unassigned column keeps as basic and watched columns two columns
// assigned on the current level (the propagated one and the trigger, or the old watch), so that
// backtracking below this level unassigns both and the row is open again with valid watches
// (Han & Jiang). Without two such columns (a row checked after a pivot or a reopen) it goes on
// the closed stack and is checked again when its level is backtracked.
bool Solver::gauss_fix_row(uint32_t m, uint32_t r, uint32_t trigger) {
  GaussMatrix& M = gauss_mats_[m];
  ++gauss_stats_.row_checks;
  const uint64_t* R = M.row(r);
  uint32_t found[3];
  uint32_t count = 0;
  for (uint32_t w = 0; w < M.words && count < 3; ++w) {
    for (uint64_t x = R[w] & ~M.assigned[w]; x && count < 3; x &= x - 1) {
      found[count++] = w * 64 + static_cast<uint32_t>(std::countr_zero(x));
    }
  }
  stats_.ticks += M.words / 8 + 1;
  uint32_t b = M.basic[r];
  if (count >= 2) {
    if (M.is_assigned(b)) {
      b = found[0];
      gauss_pivot(m, r, b, trigger);
    }
    const uint32_t w = M.watch[r];
    if (w == kNone || w == b || M.is_assigned(w) || !GaussMatrix::test(R, w)) {
      const uint32_t nw = found[0] != b ? found[0] : found[1];
      M.watch[r] = nw;
      M.watchers[nw].push_back(r);
    }
    return true;
  }
  // At most one unassigned column: closed on this level.
  if (count == 1 && found[0] != b) {
    b = found[0];
    gauss_pivot(m, r, b, trigger);
  }
  if (level()) {
    const uint32_t lvl = level();
    auto current = [&](uint32_t c) {
      return c != kNone && c != b && GaussMatrix::test(R, c) && M.is_assigned(c) && vdata_[M.col_var[c]].level == lvl;
    };
    // (the basic column is unassigned in the view here, or assigned on this level when count = 0
    // was reached by its own assignment)
    const bool basic_current = count == 1 || vdata_[M.col_var[b]].level == lvl;
    uint32_t w = kNone;
    if (basic_current) {
      if (current(trigger)) {
        w = trigger;
      } else if (current(M.watch[r])) {
        w = M.watch[r];
      }
    }
    if (w == kNone) {
      gauss_closed_.push_back(GaussClosed{lvl, m, r});
      M.watch[r] = kNone;
    } else {
      // (w is in the view: its watcher list was emptied when it was processed)
      M.watch[r] = w;
      M.watchers[w].push_back(r);
    }
  } else {
    M.watch[r] = kNone;
  }
  uint32_t parity = M.rhs[r];
  for (uint32_t w = 0; w < M.words; ++w) parity ^= std::popcount(R[w] & M.values[w] & M.assigned[w]) & 1u;
  if (count == 0) {
    if (!parity) return true;
    gauss_conflict_from_row(m, r);
    return false;
  }
  const uint32_t u = found[0];
  const Var x = M.col_var[u];
  const Lit lit = make_lit(x, parity == 0);  // x = rhs + the assigned columns
  if (vals_[lit] > 0) return true;
  if (vals_[lit] < 0) {
    gauss_conflict_from_row(m, r);
    return false;
  }
  ++gauss_stats_.propagations;
  if (!level()) {
    ++gauss_stats_.root_units;
    assign(lit, kNoReason);
    return true;
  }
  const size_t offset = gauss_reasons_.size();
  if (offset >= kGaussMask) return true;  // (reason buffer full: skip the propagation)
  gauss_reasons_.push_back(0);
  gauss_reasons_.push_back(lit);
  for (uint32_t w = 0; w < M.words; ++w) {
    for (uint64_t y = R[w]; y; y &= y - 1) {
      const uint32_t c = w * 64 + static_cast<uint32_t>(std::countr_zero(y));
      if (c == u) continue;
      const Var v = M.col_var[c];
      gauss_reasons_.push_back(make_lit(v, vals_[make_lit(v, false)] > 0));
    }
  }
  gauss_reasons_[offset] = static_cast<Lit>(gauss_reasons_.size() - offset - 1);
  assign(lit, kGaussTag | static_cast<uint32_t>(offset));
  return true;
}

// Called by backtrack() before the trail is cut at control_[new_level] (no chronological
// backtracking in the detached solver).
void Solver::gauss_backtrack(uint32_t new_level) {
  const size_t j = control_[new_level];
  const size_t end = std::min(gauss_qhead_, trail_.size());
  for (size_t i = j; i < end; ++i) {
    const Var v = var_of(trail_[i]);
    const uint32_t m = gauss_mat_[v];
    if (m == kNone) continue;
    const uint32_t c = gauss_col_[v];
    gauss_mats_[m].assigned[c >> 6] &= ~(uint64_t{1} << (c & 63));
  }
  if (gauss_qhead_ > j) gauss_qhead_ = j;
  for (size_t i = j; i < trail_.size(); ++i) {
    const uint32_t r = vdata_[var_of(trail_[i])].reason;
    if (r >= kGaussTag && r != kNoReason) {
      gauss_reasons_.resize(r & kGaussMask);
      break;
    }
  }
  while (!gauss_closed_.empty() && gauss_closed_.back().level > new_level) {
    ++gauss_stats_.reopened;
    gauss_enqueue(gauss_closed_.back().matrix, gauss_closed_.back().row);
    gauss_closed_.pop_back();
  }
}

}  // namespace psat
