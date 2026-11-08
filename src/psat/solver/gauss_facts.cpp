// Root-level facts implied by the XOR system (--gaussfacts): units and equivalences that follow
// from the reduced row echelon form of each XOR component.
//
// With the system in reduced row echelon form (one basic column per row, appearing in no other
// row), x = c is implied iff some row is x alone; x + y = c iff some row is exactly x + y (x
// basic, y not), or two rows have the same non-basic part (both basic). Equivalences between two
// non-basic columns cannot be implied. Analysis only for now (statistics, no change to the
// formula): it measures what deriving these facts with proofs could give.

#include <algorithm>
#include <bit>
#include <cstdio>
#include <unordered_map>
#include <unordered_set>

#include "psat/solver/solver.hpp"

namespace psat {

void Solver::gauss_facts(const XorList& xors) {
  GaussStats& gs = gauss_stats_;
  const uint32_t nx = static_cast<uint32_t>(xors.size());
  std::vector<uint32_t> parent(num_vars_);
  for (Var v = 0; v < num_vars_; ++v) parent[v] = v;
  auto find = [&](uint32_t v) {
    while (parent[v] != v) {
      parent[v] = parent[parent[v]];
      v = parent[v];
    }
    return v;
  };
  // Input equivalences (XORs of two variables), not counted as new.
  std::unordered_set<uint64_t> known;
  auto pair_key = [](Var a, Var b) { return a < b ? (uint64_t{a} << 32) | b : (uint64_t{b} << 32) | a; };
  for (uint32_t i = 0; i < nx; ++i) {
    const uint32_t b = xors.start[i], e = xors.start[i + 1];
    if (e - b == 2) known.insert(pair_key(xors.vars[b], xors.vars[b + 1]));
    for (uint32_t q = b + 1; q < e; ++q) {
      const uint32_t x = find(xors.vars[b]), y = find(xors.vars[q]);
      if (x != y) parent[x] = y;
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
  std::vector<uint32_t> col(num_vars_, UINT32_MAX);
  for (const std::vector<uint32_t>& rows : members) {
    if (rows.size() < 2) continue;
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
    const uint32_t w = (nc + 63) / 64;
    if (uint64_t{nr} * 64 * w > max_bits) {
      ++gs.facts_skipped;
      for (const Var v : cols) col[v] = UINT32_MAX;
      continue;
    }
    std::vector<uint64_t> m(size_t{nr} * w, 0);
    std::vector<uint8_t> rhs(nr, 0);
    for (uint32_t r = 0; r < nr; ++r) {
      for (uint32_t q = xors.start[rows[r]]; q < xors.start[rows[r] + 1]; ++q) {
        const uint32_t c = col[xors.vars[q]];
        m[size_t{r} * w + (c >> 6)] ^= uint64_t{1} << (c & 63);
      }
      rhs[r] = xors.rhs[rows[r]];
    }
    // Reduced row echelon form.
    std::vector<uint32_t> basic;
    uint32_t rank = 0;
    for (uint32_t c = 0; c < nc && rank < nr; ++c) {
      uint32_t p = rank;
      while (p < nr && !((m[size_t{p} * w + (c >> 6)] >> (c & 63)) & 1u)) ++p;
      if (p == nr) continue;
      if (p != rank) {
        std::swap_ranges(m.begin() + static_cast<std::ptrdiff_t>(size_t{p} * w),
                         m.begin() + static_cast<std::ptrdiff_t>(size_t{p} * w + w),
                         m.begin() + static_cast<std::ptrdiff_t>(size_t{rank} * w));
        std::swap(rhs[p], rhs[rank]);
      }
      const uint64_t* P = m.data() + size_t{rank} * w;
      for (uint32_t r = 0; r < nr; ++r) {
        if (r == rank) continue;
        uint64_t* R = m.data() + size_t{r} * w;
        if (!((R[c >> 6] >> (c & 63)) & 1u)) continue;
        for (uint32_t x = c >> 6; x < w; ++x) R[x] ^= P[x];
        rhs[r] ^= rhs[rank];
      }
      basic.push_back(c);
      ++rank;
    }
    gs.facts_rank += rank;
    gs.facts_free += nc - rank;
    // Units, equivalences, short rows; rows grouped by their non-basic part. With
    // --gaussfacts=2 and no proof (an experiment: the facts are not justified in DRAT yet), the
    // facts are added to the formula.
    const bool apply = opts_.gaussfacts >= 2 && !proof_;
    auto add_equivalence = [&](Var a, Var b, uint8_t parity) {  // a + b = parity
      if (!apply) return;
      // a = b + parity: (-a v b') and (a v -b') with b' the literal of b xor parity
      const Lit x = make_lit(a, false), y = make_lit(b, parity != 0);
      add_binary(negate(x), y, false);
      add_binary(x, negate(y), false);
      ++gs.facts_applied;
    };
    std::unordered_map<uint64_t, uint32_t> by_free;  // hash of the non-basic part -> row
    for (uint32_t r = 0; r < rank; ++r) {
      const uint64_t* R = m.data() + size_t{r} * w;
      uint32_t weight = 0;
      for (uint32_t x = 0; x < w; ++x) weight += static_cast<uint32_t>(std::popcount(R[x]));
      const Var vb = cols[basic[r]];
      if (weight == 1) {
        ++gs.facts_units;
        if (apply && !vals_[make_lit(vb, false)]) {
          assign(make_lit(vb, rhs[r] == 0), kNoReason);
          ++gs.facts_applied;
        }
        continue;
      }
      if (weight == 2) {
        Var other = 0;
        for (uint32_t x = 0; x < w; ++x) {
          for (uint64_t y = R[x]; y; y &= y - 1) {
            const uint32_t c = x * 64 + static_cast<uint32_t>(std::countr_zero(y));
            if (c != basic[r]) other = cols[c];
          }
        }
        ++gs.facts_equivalences;
        if (!known.count(pair_key(vb, other))) {
          ++gs.facts_new_equivalences;
          add_equivalence(vb, other, rhs[r]);
        }
      } else if (weight <= 4) {
        ++gs.facts_short[weight];
      }
      uint64_t h = 0x9E3779B97F4A7C15ull;
      for (uint32_t x = 0; x < w; ++x) {
        uint64_t y = R[x];
        if (x == (basic[r] >> 6)) y &= ~(uint64_t{1} << (basic[r] & 63));
        h = (h ^ y) * 0x100000001B3ull;
        h ^= h >> 29;
      }
      const auto it = by_free.find(h);
      if (it == by_free.end()) {
        by_free.emplace(h, r);
        continue;
      }
      const uint32_t r2 = it->second;
      const uint64_t* R2 = m.data() + size_t{r2} * w;
      bool same = true;  // (the non-basic parts, exactly: the hash may collide)
      for (uint32_t x = 0; x < w && same; ++x) {
        uint64_t a = R[x], b = R2[x];
        if (x == (basic[r] >> 6)) a &= ~(uint64_t{1} << (basic[r] & 63));
        if (x == (basic[r2] >> 6)) b &= ~(uint64_t{1} << (basic[r2] & 63));
        same = a == b;
      }
      if (!same) continue;
      ++gs.facts_equivalences;
      if (!known.count(pair_key(vb, cols[basic[r2]]))) {
        ++gs.facts_new_equivalences;
        add_equivalence(vb, cols[basic[r2]], static_cast<uint8_t>(rhs[r] ^ rhs[r2]));
      }
    }
    for (const Var v : cols) col[v] = UINT32_MAX;
  }
  if (opts_.verbose) {
    std::printf("c gauss facts: rank %llu, free %llu, units %llu, equivalences %llu (new %llu), rows of 3 / 4 variables "
                "%llu / %llu, components too large %llu\n",
                static_cast<unsigned long long>(gs.facts_rank), static_cast<unsigned long long>(gs.facts_free),
                static_cast<unsigned long long>(gs.facts_units), static_cast<unsigned long long>(gs.facts_equivalences),
                static_cast<unsigned long long>(gs.facts_new_equivalences),
                static_cast<unsigned long long>(gs.facts_short[3]), static_cast<unsigned long long>(gs.facts_short[4]),
                static_cast<unsigned long long>(gs.facts_skipped));
    std::fflush(stdout);
  }
}

}  // namespace psat
