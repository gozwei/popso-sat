// XOR-substitution reversal (--xorsub): formulas in which every variable x of some formula F was
// replaced by the XOR of a tuple of new variables (x = a + b, or a + b + c) and each clause was
// expanded into CNF (2^(d-1) clauses per substituted literal, a clause with k substituted
// literals becomes 2^(k (d-1)) clauses). Resolution needs exponentially larger proofs for the
// substituted formula than for F (xor_op_n40_d3: the ordering principle on 40 elements, out of
// reach at 300 s, while F itself is refuted in 0.12 s).
//
// Detection is structural (any variable numbering and polarities):
// - The variables of a tuple occur in exactly the same clauses: variables are grouped by their
//   occurrence count and two hashes of their clause indices, then compared exactly. Groups of 2
//   or 3 variables are the candidate tuples.
// - Each clause with a tuple maps to its reduced clause: the tuple's literals become one literal
//   of a new variable x_t, positive iff an even number of them are negative (a + b = 0 is
//   excluded by the clauses (a v b) and (-a v -b)). The clauses with the same reduced clause form
//   a group, which must be the complete expansion: prod 2^(d_t - 1) distinct clauses. Tuples in
//   an incomplete group are dropped, and the grouping is repeated until every group is complete.
// - The pass runs only if the expansions are at least --xorsubmin per mille of the clauses.
//
// Proof (DRAT):
// - x_t = v1 + ... + vd for each tuple: the 2^d clauses of the (d+1)-XOR, those with x_t first,
//   RAT on x_t (no clause has -x_t yet), then those with -x_t, RAT on -x_t (every resolvent
//   with the first ones is a tautology).
// - Each reduced clause D is derived by case splits on the first d-1 variables of each of its
//   tuples (prove_by_cases): every leaf D v s1 v ... v sm is RUP (the last variable of each tuple
//   follows from its definition, and one expanded clause is then falsified), and every inner
//   node is RUP from its two children; only D stays. Then the group's expanded clauses are
//   deleted.
// The definitions stay in the formula (elimination removes the tuple variables later, with the
// usual model reconstruction), so a model of the reduced formula extends to the original one.

#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdio>
#include <unordered_map>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

uint64_t mix_id(uint64_t h) {
  h += 0x9E3779B97F4A7C15ull;
  h = (h ^ (h >> 30)) * 0xBF58476D1CE4E5B9ull;
  h = (h ^ (h >> 27)) * 0x94D049BB133111EBull;
  return h ^ (h >> 31);
}

}  // namespace

void Solver::xor_unsubstitute() {
  const auto t0 = std::chrono::steady_clock::now();
  XorSubStats& xs = xorsub_stats_;
  ++xs.runs;
  // The clauses: live irredundant long clauses (ids 0..L-1, in clauses_ order), then the
  // irredundant binary clauses (from the watches of their smaller literal).
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
  auto lits_of = [&](uint32_t id, uint32_t& n) -> const Lit* {
    if (id < nlong) {
      const Clause& c = clause(longs[id]);
      n = c.size;
      return c.lits();
    }
    n = 2;
    return bins.data() + 2 * size_t{id - nlong};
  };
  // Occurrence signatures.
  std::vector<uint32_t> count(num_vars_, 0);
  std::vector<uint64_t> h1(num_vars_, 0), h2(num_vars_, 0);
  for (uint32_t id = 0; id < nclauses; ++id) {
    uint32_t n;
    const Lit* l = lits_of(id, n);
    const uint64_t a = mix_id(id), b = mix_id(id ^ 0x5555555555ull);
    for (uint32_t k = 0; k < n; ++k) {
      const Var v = var_of(l[k]);
      ++count[v];
      h1[v] += a;
      h2[v] ^= b;
    }
  }
  // Only variables whose signature some other candidate may share can be in a tuple: a first pass
  // counts the signatures (hashed, in saturating 8-bit counters, collisions only raise a count),
  // and only variables with a count of 2 or more are sorted. Every variable of a group of equal
  // signatures is among them, in the same relative order, so the groups found are the same (on
  // large formulas sorting every candidate took most of the pass, which usually finds nothing).
  auto eligible = [&](Var v) { return count[v] >= 2 && !vals_[make_lit(v, false)] && !eliminated_[v]; };
  auto signature = [&](Var v) { return mix_id(mix_id(h1[v] ^ count[v]) ^ h2[v]); };
  size_t eligible_count = 0;
  for (Var v = 0; v < num_vars_; ++v) eligible_count += eligible(v) ? 1 : 0;
  size_t slots = 1024;
  while (slots < 2 * eligible_count) slots <<= 1;
  std::vector<uint8_t> seen(slots, 0);
  for (Var v = 0; v < num_vars_; ++v) {
    if (!eligible(v)) continue;
    uint8_t& s = seen[signature(v) & (slots - 1)];
    if (s < 2) ++s;
  }
  std::vector<Var> cand;
  for (Var v = 0; v < num_vars_; ++v) {
    if (eligible(v) && seen[signature(v) & (slots - 1)] >= 2) cand.push_back(v);
  }
  std::vector<uint8_t>().swap(seen);
  std::sort(cand.begin(), cand.end(), [&](Var a, Var b) {
    if (count[a] != count[b]) return count[a] < count[b];
    if (h1[a] != h1[b]) return h1[a] < h1[b];
    if (h2[a] != h2[b]) return h2[a] < h2[b];
    return a < b;
  });
  // Candidate tuples: 2 or 3 variables with equal signatures (verified exactly below).
  std::vector<std::vector<Var>> tuples;
  for (size_t i = 0; i < cand.size();) {
    size_t j = i + 1;
    while (j < cand.size() && count[cand[j]] == count[cand[i]] && h1[cand[j]] == h1[cand[i]] &&
           h2[cand[j]] == h2[cand[i]]) {
      ++j;
    }
    if (j - i == 2 || j - i == 3) tuples.emplace_back(cand.begin() + static_cast<std::ptrdiff_t>(i),
                                                     cand.begin() + static_cast<std::ptrdiff_t>(j));
    i = j;
  }
  auto finish = [&]() {
    xs.seconds += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  };
  if (tuples.empty()) {
    finish();
    return;
  }
  // Occurrence lists of the tuple variables (clause ids in increasing order): exact check that a
  // tuple's variables occur in the same clauses.
  constexpr uint32_t kNone = UINT32_MAX;
  std::vector<uint32_t> tuple_of(num_vars_, kNone);
  for (uint32_t t = 0; t < tuples.size(); ++t) {
    for (const Var v : tuples[t]) tuple_of[v] = t;
  }
  std::vector<std::vector<uint32_t>> occ(tuples.size() * 3);  // per tuple member
  auto member = [&](Var v) {
    const std::vector<Var>& tu = tuples[tuple_of[v]];
    return static_cast<uint32_t>(std::find(tu.begin(), tu.end(), v) - tu.begin());
  };
  for (uint32_t id = 0; id < nclauses; ++id) {
    uint32_t n;
    const Lit* l = lits_of(id, n);
    for (uint32_t k = 0; k < n; ++k) {
      const Var v = var_of(l[k]);
      if (tuple_of[v] != kNone) occ[3 * size_t{tuple_of[v]} + member(v)].push_back(id);
    }
  }
  std::vector<uint8_t> alive(tuples.size(), 1);
  for (uint32_t t = 0; t < tuples.size(); ++t) {
    for (uint32_t m = 1; m < tuples[t].size(); ++m) {
      if (occ[3 * size_t{t} + m] != occ[3 * size_t{t}]) alive[t] = 0;
    }
  }
  // The clauses with tuples (union of the occurrence lists).
  std::vector<uint32_t> touched;
  for (uint32_t t = 0; t < tuples.size(); ++t) {
    if (alive[t]) touched.insert(touched.end(), occ[3 * size_t{t}].begin(), occ[3 * size_t{t}].end());
  }
  std::sort(touched.begin(), touched.end());
  touched.erase(std::unique(touched.begin(), touched.end()), touched.end());
  std::vector<std::vector<uint32_t>>().swap(occ);
  // Grouping by reduced clause, until every group is complete. Reduced literals of tuple t use
  // the placeholder variable num_vars_ + t.
  struct Group {
    std::vector<Lit> key;
    std::vector<uint32_t> members;  // clause ids
    uint32_t split = 0;             // sum of (d - 1) over its tuples
  };
  std::vector<Group> groups;
  std::vector<Lit> key, sorted_a, sorted_b;
  std::vector<uint32_t> negs(tuples.size(), 0);
  for (;;) {
    groups.clear();
    std::unordered_map<uint64_t, std::vector<uint32_t>> index;  // key hash -> groups
    for (const uint32_t id : touched) {
      uint32_t n;
      const Lit* l = lits_of(id, n);
      key.clear();
      uint32_t split = 0;
      for (uint32_t k = 0; k < n; ++k) {
        const uint32_t t = tuple_of[var_of(l[k])];
        if (t == kNone || !alive[t]) {
          key.push_back(l[k]);
        } else {
          negs[t] += is_negative(l[k]) ? 1u : 0u;
        }
      }
      for (uint32_t k = 0; k < n; ++k) {
        const uint32_t t = tuple_of[var_of(l[k])];
        if (t == kNone || !alive[t] || var_of(l[k]) != tuples[t][0]) continue;
        key.push_back(make_lit(num_vars_ + t, negs[t] & 1u));
        split += static_cast<uint32_t>(tuples[t].size()) - 1;
      }
      for (uint32_t k = 0; k < n; ++k) {
        const uint32_t t = tuple_of[var_of(l[k])];
        if (t != kNone) negs[t] = 0;
      }
      if (!split) continue;  // (only dropped tuples left in this clause)
      std::sort(key.begin(), key.end());
      uint64_t h = 0x84222325CBF29CE4ull;
      for (const Lit x : key) h = mix_id(h ^ x);
      std::vector<uint32_t>& bucket = index[h];
      uint32_t g = kNone;
      for (const uint32_t c : bucket) {
        if (groups[c].key == key) {
          g = c;
          break;
        }
      }
      if (g == kNone) {
        g = static_cast<uint32_t>(groups.size());
        groups.push_back(Group{key, {}, split});
        bucket.push_back(g);
      }
      groups[g].members.push_back(id);
    }
    // Completeness: 2^split distinct clauses (duplicates of a clause are allowed, and deleted too).
    bool dropped = false;
    for (const Group& g : groups) {
      bool complete = g.split < 31 && g.members.size() >= (size_t{1} << g.split);
      if (complete) {
        std::vector<std::vector<Lit>> distinct;
        for (const uint32_t id : g.members) {
          uint32_t n;
          const Lit* l = lits_of(id, n);
          distinct.emplace_back(l, l + n);
          std::sort(distinct.back().begin(), distinct.back().end());
        }
        std::sort(distinct.begin(), distinct.end());
        distinct.erase(std::unique(distinct.begin(), distinct.end()), distinct.end());
        complete = distinct.size() == (size_t{1} << g.split);
      }
      if (complete) continue;
      for (const Lit x : g.key) {
        if (var_of(x) >= num_vars_ && alive[var_of(x) - num_vars_]) {
          alive[var_of(x) - num_vars_] = 0;
          dropped = true;
        }
      }
    }
    if (!dropped) break;
  }
  uint64_t expansions = 0;
  for (const Group& g : groups) expansions += g.members.size();
  const uint64_t irredundant = irredundant_ + binaries_irredundant_;
  uint32_t live = 0;
  for (uint32_t t = 0; t < tuples.size(); ++t) live += alive[t];
  xs.candidates += tuples.size();
  if (!live || groups.empty() || expansions * 1000 < static_cast<uint64_t>(opts_.xorsubmin) * std::max<uint64_t>(irredundant, 1)) {
    if (opts_.verbose >= 2 && live) {
      std::printf("c xorsub: %u tuples, %llu of %llu clauses expansions: below --xorsubmin\n", live,
                  static_cast<unsigned long long>(expansions), static_cast<unsigned long long>(irredundant));
    }
    finish();
    return;
  }
  // New variables x_t for the live tuples.
  const uint32_t base = num_vars_;
  std::vector<Var> xvar(tuples.size(), kNone);
  uint32_t next = base;
  for (uint32_t t = 0; t < tuples.size(); ++t) {
    if (alive[t]) xvar[t] = next++;
  }
  grow_vars(next);
  auto real = [&](Lit l) { return var_of(l) >= base ? make_lit(xvar[var_of(l) - base], is_negative(l)) : l; };
  // Definitions x = v1 + ... + vd: the clauses excluding the assignments of odd parity over
  // (x, v1, ..., vd); those with x positive (x = 0 excluded) first.
  std::vector<Lit> c;
  for (uint32_t t = 0; t < tuples.size(); ++t) {
    if (!alive[t]) continue;
    const std::vector<Var>& tu = tuples[t];
    const uint32_t d = static_cast<uint32_t>(tu.size());
    for (int xneg = 0; xneg < 2; ++xneg) {
      for (uint32_t m = 0; m < (1u << d); ++m) {
        // excluded assignment: x = xneg, v_i = bit i of m, with odd total parity
        if (((static_cast<uint32_t>(std::popcount(m)) + static_cast<uint32_t>(xneg)) & 1u) == 0) continue;
        c.clear();
        c.push_back(make_lit(xvar[t], xneg != 0));
        for (uint32_t i = 0; i < d; ++i) c.push_back(make_lit(tu[i], ((m >> i) & 1u) != 0));
        if (proof_) proof_->add(c.data(), c.size());
        new_clause(c.data(), static_cast<uint32_t>(c.size()), false, 0);
        ++xs.definition_clauses;
      }
    }
    ++xs.tuples;
    if (d == 3) ++xs.triples;
  }
  // Reduced clauses, then the expansions are deleted.
  std::vector<Var> cases;
  std::vector<Lit> d_lits;
  for (const Group& g : groups) {
    d_lits.clear();
    cases.clear();
    for (const Lit x : g.key) {
      d_lits.push_back(real(x));
      if (var_of(x) >= base) {
        const std::vector<Var>& tu = tuples[var_of(x) - base];
        for (size_t i = 0; i + 1 < tu.size(); ++i) cases.push_back(tu[i]);
      }
    }
    if (proof_) prove_by_cases(d_lits, cases, 0);
    // (the reduced clause cannot contain a false literal at the root that the expansions did not)
    if (d_lits.size() == 1) {
      if (!vals_[d_lits[0]]) assign(d_lits[0], kNoReason);
      else if (vals_[d_lits[0]] < 0) {
        inconsistent_ = true;
        if (proof_) proof_->add_empty();
      }
    } else if (d_lits.size() == 2) {
      add_binary(d_lits[0], d_lits[1], false);
    } else {
      new_clause(d_lits.data(), static_cast<uint32_t>(d_lits.size()), false, 0);
    }
    ++xs.reduced;
    for (const uint32_t id : g.members) {
      if (id < nlong) {
        delete_irredundant(longs[id]);
      } else {
        delete_binary(bins[2 * size_t{id - nlong}], bins[2 * size_t{id - nlong} + 1]);
        --binaries_irredundant_;
      }
      ++xs.removed;
    }
    if (inconsistent_) break;
  }
  finish();
  if (opts_.verbose) {
    std::printf("c xorsub: %llu tuples (%llu of 3 variables), %llu expanded clauses -> %llu reduced clauses + %llu "
                "definition clauses, %.3f s\n",
                static_cast<unsigned long long>(xs.tuples), static_cast<unsigned long long>(xs.triples),
                static_cast<unsigned long long>(xs.removed), static_cast<unsigned long long>(xs.reduced),
                static_cast<unsigned long long>(xs.definition_clauses), xs.seconds);
    std::fflush(stdout);
  }
}

}  // namespace psat
