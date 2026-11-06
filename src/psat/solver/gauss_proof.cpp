// Proof-producing refutation of inconsistent XOR systems (--gauss, --gaussproof).
//
// Before search, Gaussian elimination over each component of the extracted XORs tracks which
// original XORs every row is the sum of. A row that becomes 0 = 1 gives a certificate: a set S of
// XORs whose sum is 0 = 1. The empty clause is then derived in DRAT from the clause encodings of
// S, with extension variables (the idea of Philipp & Rebola-Pardo, JELIA 2016, that XOR sums need
// auxiliary variables to stay polynomial; the derivation below is our own):
//
// - Every parity constraint is a chain over a global variable order: its variables v1 < v2 < ...
//   and prefix variables p1 = v1, pi = p(i-1) + vi (extension variables, each defined by the four
//   clauses of a 3-XOR, RAT on the new variable), and the unit clause "top prefix = rhs".
// - The chain of an XOR of the formula: its definitions, then the XORs "pi + v(i+1) + ... = rhs"
//   for i = 2, 3, ... down to the unit, each clause RUP after a case split on vi (two clauses with
//   vi and -vi, then their resolvent; the helpers are deleted).
// - The sum Q = P + R of two chains: Q shares P's prefix variables before R's first variable;
//   from there, position by position (variable x), Q gets a new prefix variable c' = c + x where x
//   occurs in exactly one of P and R, keeps c where it occurs in both (it cancels), and the
//   relation "c + a + b = 0" between the prefixes of Q, P and R is carried along: its clauses at
//   x are RUP from those before x and the definitions after a case split on x. At the end the
//   units of P's and R's tops give Q's top unit, or the empty clause when Q has no variables left
//   and rhs 1. Clauses that are no longer needed (relations, helpers, definitions not shared
//   with Q) are deleted.
//
// The sum is formed left to right over S in an order that keeps the rebuilt suffixes short
// (greedy), with the global variable order given by first appearance in that sequence. Extension
// variables are numbered above the solver's variables; the solver stops right after the empty
// clause, so they never meet variables it adds later. Without a proof the certificate alone
// decides (UNSAT).

#include <algorithm>
#include <bit>
#include <cstdio>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

constexpr Var kNoVar = UINT32_MAX;

struct Chain {
  std::vector<uint32_t> pos;  // positions in the global order (increasing)
  std::vector<Var> vars, pre;
  uint8_t rhs = 0;
  size_t size() const { return vars.size(); }
};

class XorProof {
 public:
  XorProof(ProofWriter* proof, Var first_ext) : proof_(proof), next_(first_ext) {}
  uint64_t lines = 0, positions = 0;

  Chain from_xor(const std::vector<std::pair<uint32_t, Var>>& pv, uint8_t rhs) {
    Chain ch;
    ch.rhs = rhs;
    for (const auto& [p, v] : pv) {
      ch.pos.push_back(p);
      ch.vars.push_back(v);
    }
    const size_t k = ch.size();
    ch.pre.push_back(ch.vars[0]);
    for (size_t i = 1; i < k; ++i) {
      const Var e = next_++;
      define(e, ch.pre[i - 1], ch.vars[i]);
      ch.pre.push_back(e);
    }
    // T(i): pre[i] + vars[i+1..] = rhs; T(0) is the XOR itself (clauses of the formula).
    std::vector<Var> prev, cur;
    for (size_t i = 1; i < k; ++i) {
      cur.assign(1, ch.pre[i]);
      cur.insert(cur.end(), ch.vars.begin() + static_cast<std::ptrdiff_t>(i) + 1, ch.vars.end());
      derive(cur, rhs, ch.vars[i]);
      if (i >= 2) remove(prev, rhs);
      prev.swap(cur);
    }
    if (k == 1) add_unit(ch.vars[0], rhs);
    positions += k;
    return ch;
  }

  // Q = P + R; P and R are consumed. Sets `empty` when the empty clause was derived.
  Chain merge(const Chain& P, const Chain& R, bool& empty) {
    empty = false;
    if (!P.size()) return R;
    Chain Q;
    Q.rhs = P.rhs ^ R.rhs;
    size_t i = 0, k = 0;
    while (i < P.size() && P.pos[i] < R.pos[0]) {
      Q.pos.push_back(P.pos[i]);
      Q.vars.push_back(P.vars[i]);
      Q.pre.push_back(P.pre[i]);
      ++i;
    }
    const size_t shared = i;
    Var a = i ? P.pre[i - 1] : kNoVar, b = kNoVar, c = a;
    std::vector<Var> rel, next_rel;  // the relation c + a + b = 0 (cancelled)
    while (i < P.size() || k < R.size()) {
      const bool in_p = i < P.size() && (k == R.size() || P.pos[i] <= R.pos[k]);
      const bool in_r = k < R.size() && (i == P.size() || R.pos[k] <= P.pos[i]);
      const Var x = in_p ? P.vars[i] : R.vars[k];
      const Var a2 = in_p ? P.pre[i] : a, b2 = in_r ? R.pre[k] : b;
      Var c2 = c;
      if (in_p != in_r) {
        if (c == kNoVar) {
          c2 = x;
        } else {
          c2 = next_++;
          define(c2, c, x);
        }
        Q.pos.push_back(in_p ? P.pos[i] : R.pos[k]);
        Q.vars.push_back(x);
        Q.pre.push_back(c2);
      }
      cancelled(next_rel, c2, a2, b2);
      derive(next_rel, 0, x);
      remove(rel, 0);
      rel.swap(next_rel);
      a = a2;
      b = b2;
      c = c2;
      if (in_p) ++i;
      if (in_r) ++k;
      ++positions;
    }
    // The units of P's and R's tops give Q's.
    if (c != kNoVar) {
      add_unit(c, Q.rhs);
    } else if (Q.rhs) {
      add(std::vector<Lit>{});
      empty = true;
      return Q;
    }
    remove(rel, 0);  // (the units of P's and R's tops stay: checkers ignore deleted units)
    for (size_t t = std::max<size_t>(shared, 1); t < P.size(); ++t) undefine(P.pre[t], P.pre[t - 1], P.vars[t]);
    for (size_t t = 1; t < R.size(); ++t) undefine(R.pre[t], R.pre[t - 1], R.vars[t]);
    return Q;
  }

 private:
  void add(const std::vector<Lit>& c) {
    if (proof_) proof_->add(c.data(), c.size());
    ++lines;
  }
  void del(const std::vector<Lit>& c) {
    if (proof_) proof_->del(c.data(), c.size());
    ++lines;
  }
  void add_unit(Var v, uint8_t value) { add({make_lit(v, value == 0)}); }
  // The variables of x + y + z (kNoVar: constant 0), pairs cancelled.
  static void cancelled(std::vector<Var>& out, Var x, Var y, Var z) {
    out.clear();
    for (const Var v : {x, y, z}) {
      if (v == kNoVar) continue;
      const auto it = std::find(out.begin(), out.end(), v);
      if (it != out.end()) {
        out.erase(it);
      } else {
        out.push_back(v);
      }
    }
  }
  // The clauses of sum(vars) = parity: one per assignment of the wrong parity.
  void xor_clauses(const std::vector<Var>& vars, uint8_t parity) {
    clauses_.clear();
    const uint32_t k = static_cast<uint32_t>(vars.size());
    for (uint32_t m = 0; m < (1u << k); ++m) {
      if ((std::popcount(m) & 1u) == parity) continue;
      std::vector<Lit> c;
      for (uint32_t j = 0; j < k; ++j) c.push_back(make_lit(vars[j], (m >> j) & 1u));
      clauses_.push_back(std::move(c));
    }
  }
  // e = a + b: the clauses with e first are RAT on e (no clause has -e yet), those with -e are
  // RAT on -e (every resolvent with the first two is a tautology).
  void define(Var e, Var a, Var b) {
    add({make_lit(e, false), make_lit(a, true), make_lit(b, false)});
    add({make_lit(e, false), make_lit(a, false), make_lit(b, true)});
    add({make_lit(e, true), make_lit(a, false), make_lit(b, false)});
    add({make_lit(e, true), make_lit(a, true), make_lit(b, true)});
  }
  void undefine(Var e, Var a, Var b) {
    del({make_lit(e, false), make_lit(a, true), make_lit(b, false)});
    del({make_lit(e, false), make_lit(a, false), make_lit(b, true)});
    del({make_lit(e, true), make_lit(a, false), make_lit(b, false)});
    del({make_lit(e, true), make_lit(a, true), make_lit(b, true)});
  }
  // Adds the clauses of sum(vars) = parity. Each is RUP once x is assigned: directly if x is one
  // of vars, else through the two clauses with x and -x (deleted again).
  void derive(const std::vector<Var>& vars, uint8_t parity, Var x) {
    xor_clauses(vars, parity);
    const bool direct = std::find(vars.begin(), vars.end(), x) != vars.end();
    for (std::vector<Lit>& c : clauses_) {
      if (!direct) {
        c.push_back(make_lit(x, false));
        add(c);
        c.back() = make_lit(x, true);
        add(c);
        c.pop_back();
      }
      add(c);
      if (!direct) {
        c.push_back(make_lit(x, false));
        del(c);
        c.back() = make_lit(x, true);
        del(c);
        c.pop_back();
      }
    }
  }
  void remove(const std::vector<Var>& vars, uint8_t parity) {
    xor_clauses(vars, parity);
    for (const std::vector<Lit>& c : clauses_) del(c);
  }

  ProofWriter* proof_;
  Var next_;
  std::vector<std::vector<Lit>> clauses_;
};

}  // namespace

// The XORs `rows` of `xors` sum to 0 = 1: derives the empty clause (in the proof, if any).
// Returns false (nothing written) if the derivation would exceed the size limit.
bool Solver::gauss_prove(const std::vector<uint32_t>& rows, const XorList& xors) {
  const size_t n = rows.size();
  // Order: greedily the XOR whose sum with the current one rebuilds the fewest chain positions
  // (positions from its earliest variable already in the sum to the end), ties to more cancelled
  // variables; variables are numbered by first appearance.
  std::vector<uint32_t> pos(num_vars_, UINT32_MAX);
  uint32_t next_pos = 0;
  std::vector<uint8_t> in_sum(num_vars_, 0), used(n, 0);
  std::vector<uint32_t> sum_pos;  // positions of the current sum's variables (sorted)
  std::vector<uint32_t> order;
  uint64_t cost_total = 0;
  for (size_t step = 0; step < n; ++step) {
    size_t best = n;
    uint64_t best_cost = UINT64_MAX;
    int best_overlap = -1;
    for (size_t t = 0; t < n; ++t) {
      if (used[t]) continue;
      const uint32_t i = rows[t];
      uint32_t earliest = UINT32_MAX;
      int overlap = 0, fresh = 0;
      for (uint32_t q = xors.start[i]; q < xors.start[i + 1]; ++q) {
        const Var v = xors.vars[q];
        if (in_sum[v]) {
          ++overlap;
          earliest = std::min(earliest, pos[v]);
        } else {
          ++fresh;
        }
      }
      uint64_t cost = static_cast<uint64_t>(fresh);
      if (overlap) {
        cost += static_cast<uint64_t>(sum_pos.end() - std::lower_bound(sum_pos.begin(), sum_pos.end(), earliest));
      } else if (step) {
        cost += 1u << 30;  // disjoint from the sum: postpone
      }
      if (cost < best_cost || (cost == best_cost && overlap > best_overlap)) {
        best = t;
        best_cost = cost;
        best_overlap = overlap;
      }
    }
    used[best] = 1;
    order.push_back(rows[best]);
    const uint32_t i = rows[best];
    for (uint32_t q = xors.start[i]; q < xors.start[i + 1]; ++q) {
      const Var v = xors.vars[q];
      if (pos[v] == UINT32_MAX) pos[v] = next_pos++;
      in_sum[v] ^= 1;
      if (in_sum[v]) {
        sum_pos.insert(std::lower_bound(sum_pos.begin(), sum_pos.end(), pos[v]), pos[v]);
      } else {
        sum_pos.erase(std::lower_bound(sum_pos.begin(), sum_pos.end(), pos[v]));
      }
    }
    cost_total += std::min<uint64_t>(best_cost, 1u << 30);
  }
  if (cost_total > static_cast<uint64_t>(opts_.gaussproofsize) * 1000) {
    if (opts_.verbose) {
      std::printf("c gauss: refutation of %zu xors skipped (about %llu chain positions)\n", n,
                  static_cast<unsigned long long>(cost_total));
    }
    return false;
  }
  XorProof xp(proof_, num_vars_);
  std::vector<std::pair<uint32_t, Var>> pv;
  auto chain_of = [&](uint32_t i) {
    pv.clear();
    for (uint32_t q = xors.start[i]; q < xors.start[i + 1]; ++q) pv.emplace_back(pos[xors.vars[q]], xors.vars[q]);
    std::sort(pv.begin(), pv.end());
    return xp.from_xor(pv, xors.rhs[i]);
  };
  Chain sum = chain_of(order[0]);
  bool empty = false;
  for (size_t t = 1; t < n && !empty; ++t) sum = xp.merge(sum, chain_of(order[t]), empty);
  gauss_stats_.proof_lines += xp.lines;
  gauss_stats_.proof_positions += xp.positions;
  if (opts_.verbose) {
    std::printf("c gauss: refuted %zu xors: %llu chain positions, %llu proof lines\n", n,
                static_cast<unsigned long long>(xp.positions), static_cast<unsigned long long>(xp.lines));
  }
  return empty;
}

// Gaussian elimination per component with the row combinations: true (inconsistent_ set, the
// empty clause in the proof) if some combination of XORs is 0 = 1.
bool Solver::gauss_refute(const XorList& xors) {
  const uint32_t nx = static_cast<uint32_t>(xors.size());
  // Components (union-find over variables).
  std::vector<uint32_t> parent(num_vars_);
  for (Var v = 0; v < num_vars_; ++v) parent[v] = v;
  auto find = [&](uint32_t v) {
    while (parent[v] != v) {
      parent[v] = parent[parent[v]];
      v = parent[v];
    }
    return v;
  };
  for (uint32_t i = 0; i < nx; ++i) {
    for (uint32_t q = xors.start[i] + 1; q < xors.start[i + 1]; ++q) {
      const uint32_t a = find(xors.vars[xors.start[i]]), b = find(xors.vars[q]);
      if (a != b) parent[a] = b;
    }
  }
  std::vector<std::vector<uint32_t>> members;
  std::vector<uint32_t> index(num_vars_, UINT32_MAX);
  for (uint32_t i = 0; i < nx; ++i) {
    const uint32_t r = find(xors.vars[xors.start[i]]);
    if (index[r] == UINT32_MAX) {
      index[r] = static_cast<uint32_t>(members.size());
      members.emplace_back();
    }
    members[index[r]].push_back(i);
  }
  const uint64_t max_bits = static_cast<uint64_t>(opts_.gaussmatrix) << 20;
  // A bounded effort over all components (word operations, about a second): large components
  // with much fill-in are left alone.
  constexpr uint64_t kMaxWork = uint64_t{1} << 31;
  uint64_t work = 0;
  std::vector<uint32_t> col(num_vars_, UINT32_MAX);
  for (const std::vector<uint32_t>& rows : members) {
    if (rows.size() < 2 || work > kMaxWork) continue;
    std::vector<Var> cols;
    for (const uint32_t i : rows) {
      for (uint32_t q = xors.start[i]; q < xors.start[i + 1]; ++q) {
        const Var v = xors.vars[q];
        if (col[v] == UINT32_MAX) {
          col[v] = static_cast<uint32_t>(cols.size());
          cols.push_back(v);
        }
      }
    }
    const uint32_t nr = static_cast<uint32_t>(rows.size()), nc = static_cast<uint32_t>(cols.size());
    const uint32_t wc = (nc + 63) / 64, wr = (nr + 63) / 64, w = wc + wr;
    const bool fits = uint64_t{nr} * 64 * w <= max_bits;
    if (fits) {
      // Row r: wc words of columns, then wr words of the combination.
      std::vector<uint64_t> m(size_t{nr} * w, 0);
      std::vector<uint8_t> rhs(nr, 0), used(nr, 0);
      for (uint32_t r = 0; r < nr; ++r) {
        uint64_t* R = m.data() + size_t{r} * w;
        const uint32_t i = rows[r];
        for (uint32_t q = xors.start[i]; q < xors.start[i + 1]; ++q) {
          const uint32_t c = col[xors.vars[q]];
          R[c >> 6] ^= uint64_t{1} << (c & 63);
        }
        R[wc + (r >> 6)] |= uint64_t{1} << (r & 63);
        rhs[r] = xors.rhs[i];
      }
      for (uint32_t c = 0; c < nc && work <= kMaxWork; ++c) {
        uint32_t p = 0;
        while (p < nr && (used[p] || !((m[size_t{p} * w + (c >> 6)] >> (c & 63)) & 1u))) ++p;
        work += nr;
        if (p == nr) continue;
        used[p] = 1;
        const uint64_t* P = m.data() + size_t{p} * w;
        for (uint32_t r = 0; r < nr; ++r) {
          if (used[r]) continue;
          uint64_t* R = m.data() + size_t{r} * w;
          if (!((R[c >> 6] >> (c & 63)) & 1u)) continue;
          for (uint32_t x = c >> 6; x < w; ++x) R[x] ^= P[x];
          rhs[r] ^= rhs[p];
          work += w - (c >> 6);
        }
      }
      uint32_t best = nr;
      if (work > kMaxWork) {
        ++gauss_stats_.refute_aborted;
        std::fill(rhs.begin(), rhs.end(), 0);  // (rows not fully reduced: no conclusion)
      }
      uint64_t best_size = UINT64_MAX;
      for (uint32_t r = 0; r < nr; ++r) {
        if (used[r] || !rhs[r]) continue;
        uint64_t size = 0;
        for (uint32_t x = wc; x < w; ++x) size += static_cast<uint64_t>(std::popcount(m[size_t{r} * w + x]));
        if (size < best_size) {
          best = r;
          best_size = size;
        }
      }
      if (best != nr) {
        std::vector<uint32_t> cert;
        const uint64_t* B = m.data() + size_t{best} * w + wc;
        for (uint32_t r = 0; r < nr; ++r) {
          if ((B[r >> 6] >> (r & 63)) & 1u) cert.push_back(rows[r]);
        }
        ++gauss_stats_.refutations;
        if (opts_.verbose) {
          std::printf("c gauss: %u xors over %u variables are inconsistent: %zu of them sum to 0 = 1\n", nr, nc,
                      cert.size());
          std::fflush(stdout);
        }
        if (!proof_ || gauss_prove(cert, xors)) {
          for (const Var v : cols) col[v] = UINT32_MAX;
          inconsistent_ = true;
          return true;
        }
      }
    }
    for (const Var v : cols) col[v] = UINT32_MAX;
  }
  return false;
}

}  // namespace psat
