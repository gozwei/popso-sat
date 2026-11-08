// Internal renumbering of the variables for memory locality (--renumber).
//
// The per-variable and per-literal arrays (values, levels and reasons, phases, watch list heads,
// queue links, scores) and the watch pool, whose lists are laid out in literal order when the
// input clauses are connected, are indexed by variable. Propagating a clause reads the values of
// its literals, and assigning them writes their entries: when the variables of a clause have
// distant indices, each of those accesses can be a cache miss. Input numberings range from
// generator orders that keep the variables of a clause close to shuffled ones (variables
// renamed at random: every access lands on a different cache line).
//
// renumber() runs once, at the first solve() before anything else (preprocessing included):
// it computes a new order of the input variables and renames them in the clauses (long clauses
// in the arena keep their literal order, so the same literals are watched), the pending binary
// clauses, the root units on the trail and the per-variable state, which at that point is the
// initial one. The decision queue and the stable-mode heap keep their order (the input order:
// the variables are renamed in place), so that the renumbering changes the memory layout and not
// the decisions; where other code breaks ties by variable index, those ties can now fall
// differently.
//
// The outside world keeps the input numbering: the proof writer maps every literal back
// (renum_ext_), val() maps input variables in (renum_int_), and so do clauses added later.
// Variables added after the renumbering (BVA, XOR substitution, the extension variables of
// Gauss-Jordan proofs) keep their index, above the input's, on both sides.
//
// Orders (--renumber):
//   2  breadth-first on the variable-clause graph: from a variable, its clauses (long clauses
//      in arena order, then binary clauses, as added), and from each clause its new variables;
//      each component from a far variable (the last one a first search from its first variable
//      reaches), components in the order of their first variable in the arena; variables
//      without occurrences last, in index order;
//   1  automatic: 2, only if the input numbering looks random (its clause span, renumber_span(),
//      is at least --renumberrandom per mille of a random numbering's) and 2 has a smaller span;
//   3  random (seeded by --seed; for experiments: the cost of a scattered numbering with the
//      same search).
//
// Measured on the M4 with the same search (PLAN.md, branch loc1): a random numbering costs
// 1.2-2.8x on instances with 100k-3M variables; breadth-first takes back 15-29% on instances
// whose variables and clauses were both shuffled; generator numberings were beaten only once
// (T92, -7%) and broken badly once (cabp: +79%); the order of first occurrence in the input
// never helped.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

// a[order[i]] moves to a[i] (order: new index -> old index).
template <typename T>
void permute(std::vector<T>& a, const std::vector<Var>& order) {
  if (a.size() < order.size()) return;
  std::vector<T> b(a);
  for (size_t i = 0; i < order.size(); ++i) b[i] = a[order[i]];
  a.swap(b);
}

// The same for per-literal arrays.
template <typename T>
void permute_lits(std::vector<T>& a, const std::vector<Var>& order) {
  if (a.size() < 2 * order.size()) return;
  std::vector<T> b(a);
  for (size_t i = 0; i < order.size(); ++i) {
    b[2 * i] = a[2 * size_t{order[i]}];
    b[2 * i + 1] = a[2 * size_t{order[i]} + 1];
  }
  a.swap(b);
}

}  // namespace

void Solver::renumber() {
  renumber_tried_ = true;
  const uint32_t n = num_vars_;
  // Only on the initial state: nothing connected, propagated or decided yet.
  if (n < 2 || inconsistent_ || level() > 0 || propagated_ > 0 || watched_clauses_ > 0 || stats_.decisions > 0 ||
      stats_.conflicts > 0) {
    return;
  }
  const auto t0 = std::chrono::steady_clock::now();
  auto span_of = [this, n](const std::vector<Var>& order) {
    std::vector<Var> to_new(n);
    for (Var i = 0; i < n; ++i) to_new[order[i]] = i;
    return renumber_span(&to_new);
  };
  auto random_order = [this, n]() {
    std::vector<Var> order(n);
    for (Var v = 0; v < n; ++v) order[v] = v;
    uint64_t rng = static_cast<uint64_t>(opts_.seed) * 0x9E3779B97F4A7C15ull + 0x6A09E667F3BCC909ull;
    for (size_t i = n; i > 1; --i) {
      rng ^= rng << 13;
      rng ^= rng >> 7;
      rng ^= rng << 17;
      std::swap(order[i - 1], order[rng % i]);
    }
    return order;
  };
  // Automatic: only an input numbering about as scattered as a random one is replaced (generator
  // numberings were never beaten clearly on the M4, and breaking them cost up to 79%).
  const bool automatic = opts_.renumber == 1;
  const double input = automatic || opts_.verbose ? renumber_span(nullptr) : 0;
  const double random = automatic ? span_of(random_order()) : 0;
  const bool scattered = input >= random * static_cast<double>(opts_.renumberrandom) / 1000.0;
  std::vector<Var> order;  // new index -> old index (empty: the input numbering stays)
  if (opts_.renumber == 2 || (automatic && scattered)) {
    renumber_bfs(order);
    // Variables without occurrences follow in index order.
    std::vector<uint8_t> in(n, 0);
    for (const Var v : order) in[v] = 1;
    for (Var v = 0; v < n; ++v) {
      if (!in[v]) order.push_back(v);
    }
  } else if (opts_.renumber == 3) {
    order = random_order();
  }
  const double bfs = automatic && !order.empty() ? span_of(order) : -1;
  if (automatic && !(bfs < input)) order.clear();
  if (!order.empty()) renumber_apply(order);
  renumber_seconds_ = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  if (opts_.verbose) {
    if (automatic) {
      std::printf("c renumbering: clause span of the input %.3f, of a random numbering %.3f, breadth-first %.3f: %s\n",
                  input, random, bfs, order.empty() ? "input kept" : "renumbered");
    }
    if (!order.empty()) {
      std::printf("c renumbered %u variables (%s order) in %.2f s, clause span %.3f -> %.3f\n", n,
                  opts_.renumber == 3 ? "random" : "breadth-first", renumber_seconds_, input, renumber_span(nullptr));
    }
  }
}

// The locality of a numbering (to_new: input variable -> index; null: the current indices): the
// mean over the clauses of log2(1 + span) / log2(n), span = the largest minus the smallest index
// of the clause's variables (0: consecutive indices; a random numbering of short clauses gives
// about 0.9).
double Solver::renumber_span(const std::vector<Var>* to_new) const {
  auto index = [to_new](Lit l) { return to_new ? (*to_new)[var_of(l)] : var_of(l); };
  const double scale = 1.0 / std::log2(std::max<double>(2, num_vars_));
  double sum = 0;
  size_t count = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    Var lo = UINT32_MAX, hi = 0;
    for (uint32_t k = 0; k < c.size; ++k) {
      lo = std::min(lo, index(c.lits()[k]));
      hi = std::max(hi, index(c.lits()[k]));
    }
    sum += std::log2(1.0 + (hi - lo));
    ++count;
  }
  for (size_t i = 0; i + 1 < pending_binaries_.size(); i += 2) {
    const Var a = index(pending_binaries_[i]), b = index(pending_binaries_[i + 1]);
    sum += std::log2(1.0 + (a > b ? a - b : b - a));
    ++count;
  }
  return count ? sum * scale / static_cast<double>(count) : 0;
}

void Solver::renumber_bfs(std::vector<Var>& order) const {
  const uint32_t n = num_vars_;
  const size_t nlong = clauses_.size(), nbin = pending_binaries_.size() / 2;
  if (nlong + nbin >= UINT32_MAX) return;  // (the rest follows in index order)
  // Occurrences per variable: clause ids (long clauses 0 .. nlong - 1 by position in clauses_,
  // then the binary clauses).
  std::vector<size_t> start(size_t{n} + 1, 0);
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    for (uint32_t k = 0; k < c.size; ++k) ++start[var_of(c.lits()[k]) + 1];
  }
  for (const Lit l : pending_binaries_) ++start[var_of(l) + 1];
  for (size_t v = 1; v <= n; ++v) start[v] += start[v - 1];
  std::vector<uint32_t> occ(start[n]);
  {
    std::vector<size_t> pos(start.begin(), start.end() - 1);
    for (size_t i = 0; i < nlong; ++i) {
      const Clause& c = clause(clauses_[i]);
      for (uint32_t k = 0; k < c.size; ++k) occ[pos[var_of(c.lits()[k])]++] = static_cast<uint32_t>(i);
    }
    for (size_t i = 0; i < nbin; ++i) {
      occ[pos[var_of(pending_binaries_[2 * i])]++] = static_cast<uint32_t>(nlong + i);
      occ[pos[var_of(pending_binaries_[2 * i + 1])]++] = static_cast<uint32_t>(nlong + i);
    }
  }
  std::vector<uint32_t> vstamp(n, 0), cstamp(nlong + nbin, 0);
  uint32_t stamp = 0;
  // Appends the component of root (its unvisited part) to out in breadth-first order.
  auto bfs = [&](Var root, std::vector<Var>& out) {
    ++stamp;
    size_t head = out.size();
    out.push_back(root);
    vstamp[root] = stamp;
    auto reach = [&](Lit l) {
      const Var u = var_of(l);
      if (vstamp[u] == stamp) return;
      vstamp[u] = stamp;
      out.push_back(u);
    };
    while (head < out.size()) {
      const Var v = out[head++];
      for (size_t k = start[v]; k < start[v + 1]; ++k) {
        const uint32_t c = occ[k];
        if (cstamp[c] == stamp) continue;
        cstamp[c] = stamp;
        if (c < nlong) {
          const Clause& cl = clause(clauses_[c]);
          for (uint32_t m = 0; m < cl.size; ++m) reach(cl.lits()[m]);
        } else {
          reach(pending_binaries_[2 * (c - nlong)]);
          reach(pending_binaries_[2 * (c - nlong) + 1]);
        }
      }
    }
  };
  std::vector<uint8_t> done(n, 0);
  std::vector<Var> probe;
  auto component = [&](Var r) {
    if (done[r]) return;
    probe.clear();
    bfs(r, probe);
    const size_t before = order.size();
    bfs(probe.back(), order);
    for (size_t i = before; i < order.size(); ++i) done[order[i]] = 1;
  };
  // Components in the order of their first variable in the arena, then in the binary clauses.
  for (size_t i = 0; i < nlong; ++i) component(var_of(clause(clauses_[i]).lits()[0]));
  for (size_t i = 0; i < nbin; ++i) component(var_of(pending_binaries_[2 * i]));
}

void Solver::renumber_apply(const std::vector<Var>& order) {
  const uint32_t n = num_vars_;
  std::vector<Var> to_new(n);
  for (Var i = 0; i < n; ++i) to_new[order[i]] = i;
  auto map = [&](Lit l) { return make_lit(to_new[var_of(l)], is_negative(l)); };
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    Lit* lits = c.lits();
    for (uint32_t k = 0; k < c.size; ++k) lits[k] = map(lits[k]);
  }
  for (Lit& l : pending_binaries_) l = map(l);
  for (Lit& l : trail_) l = map(l);
  // The initial per-variable state (assigned root units, their phases; the queue and the heap).
  permute_lits(vals_, order);
  permute_lits(marks_, order);
  permute(vdata_, order);
  permute(saved_, order);
  permute(target_, order);
  permute(best_, order);
  permute(flags_, order);
  permute(eliminated_, order);
  permute(touched_, order);
  permute(bumped_, order);
  permute(score_, order);
  permute(links_, order);
  auto map_var = [&](Var v) { return v == UINT32_MAX ? v : to_new[v]; };
  for (Link& k : links_) {
    k.prev = map_var(k.prev);
    k.next = map_var(k.next);
  }
  queue_first_ = map_var(queue_first_);
  queue_last_ = map_var(queue_last_);
  queue_search_ = map_var(queue_search_);
  if (!heap_.empty()) {
    // All scores are still zero: the heap holds the variables in the order they were pushed,
    // which is the queue's (grow_vars()).
    heap_.clear();
    for (Var v = queue_first_; v != UINT32_MAX; v = links_[v].next) heap_.push(v);
  }
  renum_int_ = std::move(to_new);
  renum_ext_.resize(2 * size_t{n});
  for (Var v = 0; v < n; ++v) {
    renum_ext_[make_lit(renum_int_[v], false)] = make_lit(v, false);
    renum_ext_[make_lit(renum_int_[v], true)] = make_lit(v, true);
  }
  if (proof_) proof_->set_map(&renum_ext_);
}

}  // namespace psat
