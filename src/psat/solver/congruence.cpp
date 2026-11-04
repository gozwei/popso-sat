// Congruence closure on AND gates (Biere, Fazekas, Fleury & Froleyks, SAT 2024, restricted to
// AND gates for now). Runs inside an elimination round (long watches detached) before
// equivalent literal substitution.
//
// An AND gate lhs = AND(r1..rk) is recognized from the binary clauses (-lhs v ri) and a base clause
// (lhs v -r1 v ... v -rk). Two gates with the same inputs have equivalent outputs; the two
// binary clauses of each such equivalence are added (both are RUP: assuming lhs1 and -lhs2, the
// binaries of lhs1 make every input true and the base clause of lhs2 then forces lhs2), and the
// substitution that follows merges the outputs. After substitution, inputs are renamed and more
// gates may coincide, so the caller iterates congruence + substitution.

#include <algorithm>
#include <array>
#include <bit>

#include "psat/io/proof.hpp"
#include "psat/core/small_sort.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

uint32_t Solver::congruence(uint64_t& budget) {
  const size_t nlits = 2 * size_t{num_vars_};
  // Occurrence lists (CSR) of the live irredundant long clauses.
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
  budget += occ.size() / 4;

  // Extract gates: (sorted inputs, lhs), stored flat.
  struct Gate {
    uint64_t hash;
    uint32_t begin, size;  // inputs in gate_inputs
    Lit lhs;
  };
  std::vector<Gate> gates;
  std::vector<Lit> inputs;
  for (Lit lhs = 0; lhs < nlits; ++lhs) {
    if (vals_[lhs] != 0 || eliminated_[var_of(lhs)]) continue;
    if (start[lhs + 1] == start[lhs]) continue;
    // Candidate inputs: x with a binary clause (-lhs v x).
    uint32_t cands = 0;
    for (const Watch& w : watches_[negate(lhs)]) {
      if (w.binary() && vals_[w.blit] == 0 && !marks_[w.blit]) {
        marks_[w.blit] = 1;
        ++cands;
      }
    }
    budget += watches_[negate(lhs)].size() / 8 + 1;
    if (cands >= 2) {
      for (uint32_t o = start[lhs]; o < start[lhs + 1]; ++o) {
        const Clause& c = clause(occ[o]);
        if (c.size - 1 > cands) continue;
        budget += c.size / 8 + 1;
        bool base = true;
        for (uint32_t k = 0; k < c.size && base; ++k) {
          const Lit y = c.lits()[k];
          if (y != lhs && !marks_[negate(y)]) base = false;
        }
        if (!base) continue;
        const uint32_t begin = static_cast<uint32_t>(inputs.size());
        for (uint32_t k = 0; k < c.size; ++k) {
          if (c.lits()[k] != lhs) inputs.push_back(negate(c.lits()[k]));
        }
        std::sort(inputs.begin() + begin, inputs.end());
        uint64_t h = 0x9E3779B97F4A7C15ull * (inputs.size() - begin);
        for (size_t k = begin; k < inputs.size(); ++k) h = (h ^ inputs[k]) * 0x100000001B3ull;
        gates.push_back(Gate{h, begin, static_cast<uint32_t>(inputs.size() - begin), lhs});
        break;  // one base clause per output
      }
    }
    for (const Watch& w : watches_[negate(lhs)]) {
      if (w.binary()) marks_[w.blit] = 0;
    }
  }
  // The occurrence lists are not needed any more: free them before the XOR and ITE passes build
  // their own structures (peak memory on large formulas).
  std::vector<uint32_t>().swap(occ);
  std::vector<uint32_t>().swap(start);
  uint32_t found = 0;
  if (gates.size() < 2) {
    std::vector<Gate>().swap(gates);
    std::vector<Lit>().swap(inputs);
    found += congruent_xors(budget);
    found += congruent_ites(budget);
    stats_.congruent += found;
    return found;
  }

  // Gates with identical inputs: their outputs are equivalent.
  std::sort(gates.begin(), gates.end(), [&](const Gate& a, const Gate& b) {
    if (a.hash != b.hash) return a.hash < b.hash;
    if (a.size != b.size) return a.size < b.size;
    if (!std::equal(inputs.begin() + a.begin, inputs.begin() + a.begin + a.size, inputs.begin() + b.begin)) {
      return std::lexicographical_compare(inputs.begin() + a.begin, inputs.begin() + a.begin + a.size,
                                          inputs.begin() + b.begin, inputs.begin() + b.begin + b.size);
    }
    return a.lhs < b.lhs;
  });
  budget += gates.size();
  for (size_t i = 0; i < gates.size();) {
    size_t j = i + 1;
    while (j < gates.size() && gates[j].hash == gates[i].hash && gates[j].size == gates[i].size &&
           std::equal(inputs.begin() + gates[i].begin, inputs.begin() + gates[i].begin + gates[i].size,
                      inputs.begin() + gates[j].begin)) {
      ++j;
    }
    const Lit a = gates[i].lhs;
    for (size_t k = i + 1; k < j; ++k) {
      const Lit b = gates[k].lhs;
      if (var_of(a) == var_of(b)) {
        if (a != b) {
          // lhs = AND(R) and -lhs = AND(R): AND(R) is both true and false: unsatisfiable
          // unless R is false; the two units are handled by propagation (rare; skip).
        }
        continue;
      }
      const Lit e1[2] = {negate(a), b};
      const Lit e2[2] = {a, negate(b)};
      if (proof_) {
        proof_->add(e1, 2);
        proof_->add(e2, 2);
      }
      add_binary(e1[0], e1[1], false);
      add_binary(e2[0], e2[1], false);
      ++found;
    }
    i = j;
  }
  std::vector<Gate>().swap(gates);
  std::vector<Lit>().swap(inputs);
  found += congruent_xors(budget);
  found += congruent_ites(budget);
  stats_.congruent += found;
  return found;
}

// Adds (base v s1 v ... v sm) for every sign combination of the case variables (each RUP by the
// XOR clauses), then resolves them back down to base (RUP from its two children at every level,
// added before the children are deleted). Proves an equivalence clause between two XOR outputs
// over the same inputs; leaves only the base clause in the proof. Needs at least one case
// variable (XORs have >= 2 inputs, one of which is left out of the case split).
void Solver::prove_by_cases(std::vector<Lit>& clause, const std::vector<Var>& cases, size_t depth) {
  if (depth == cases.size()) {
    proof_->add(clause.data(), clause.size());
    return;
  }
  clause.push_back(make_lit(cases[depth], false));
  prove_by_cases(clause, cases, depth + 1);
  clause.back() = make_lit(cases[depth], true);
  prove_by_cases(clause, cases, depth + 1);
  clause.pop_back();
  proof_->add(clause.data(), clause.size());  // RUP from its two children (resolution on cases[depth])
  // Delete the two children (the leaves or the previous level's resolvents).
  clause.push_back(make_lit(cases[depth], false));
  proof_->del(clause.data(), clause.size());
  clause.back() = make_lit(cases[depth], true);
  proof_->del(clause.data(), clause.size());
  clause.pop_back();
}

// XOR constraints given by complete sets of 2^(n-1) clauses over n variables (3 <= n <= 5) with the
// same parity of negative literals; two XORs whose variable sets differ in exactly the output
// (y1 + S = p1, y2 + S = p2) give y1 = y2 + p1 + p2.
uint32_t Solver::congruent_xors(uint64_t& budget) {
  struct Row {
    Var vars[5];
    uint8_t n, mask;
  };
  // A clause of size n can only be part of an XOR if 2^(n-1) clauses share its variable set: a
  // first pass collects one hash per candidate clause (8 bytes instead of a 24-byte row for every
  // clause of size 3..5, which cost hundreds of MB on large formulas), the second pass keeps
  // rows only for variable sets that occur often enough.
  auto make_row = [&](const Clause& c, Row& r) -> bool {
    r = Row{};
    r.n = static_cast<uint8_t>(c.size);
    Lit tmp[5];
    std::copy(c.lits(), c.lits() + c.size, tmp);
    small_sort(tmp, c.size);
    for (uint32_t k = 0; k < c.size; ++k) {
      if (vals_[tmp[k]] != 0) return false;
      if (k && var_of(tmp[k]) == var_of(tmp[k - 1])) return false;
      r.vars[k] = var_of(tmp[k]);
      if (is_negative(tmp[k])) r.mask |= static_cast<uint8_t>(1u << k);
    }
    return true;
  };
  auto set_hash = [](const Row& r) {
    uint64_t h = 0x9E3779B97F4A7C15ull * r.n;
    for (int k = 0; k < r.n; ++k) h = (h ^ r.vars[k]) * 0x100000001B3ull;
    return h;
  };
  std::vector<uint64_t> hashes;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size < 3 || c.size > 5) continue;
    Row r;
    if (make_row(c, r)) hashes.push_back(set_hash(r));
  }
  budget += hashes.size();
  std::sort(hashes.begin(), hashes.end());
  std::vector<Row> rows;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size < 3 || c.size > 5) continue;
    Row r;
    if (!make_row(c, r)) continue;
    const auto range = std::equal_range(hashes.begin(), hashes.end(), set_hash(r));
    if (static_cast<size_t>(range.second - range.first) >= (size_t{1} << (r.n - 1))) rows.push_back(r);
  }
  std::vector<uint64_t>().swap(hashes);
  budget += rows.size();
  std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
    if (a.n != b.n) return a.n < b.n;
    for (int k = 0; k < a.n; ++k) {
      if (a.vars[k] != b.vars[k]) return a.vars[k] < b.vars[k];
    }
    return a.mask < b.mask;
  });
  // XOR constraints: variables + parity of the sum (= 1 - parity of the negative-literal count).
  struct Xor {
    Var vars[5];
    uint8_t n, parity;
  };
  std::vector<Xor> xors;
  for (size_t i = 0; i < rows.size();) {
    size_t j = i;
    while (j < rows.size() && rows[j].n == rows[i].n && std::equal(rows[i].vars, rows[i].vars + rows[i].n, rows[j].vars)) ++j;
    const uint32_t need = 1u << (rows[i].n - 1);
    uint32_t count[2] = {0, 0};
    uint8_t last = 0xFF;
    for (size_t k = i; k < j; ++k) {
      if (rows[k].mask == last) continue;
      last = rows[k].mask;
      ++count[std::popcount(static_cast<unsigned>(rows[k].mask)) & 1];
    }
    for (int q = 0; q < 2; ++q) {
      if (count[q] != need) continue;
      Xor x{};
      x.n = rows[i].n;
      std::copy(rows[i].vars, rows[i].vars + x.n, x.vars);
      x.parity = static_cast<uint8_t>(1 - q);
      xors.push_back(x);
    }
    i = j;
  }
  if (xors.size() < 2) return 0;
  // One entry per (XOR, output variable): key = the other variables.
  struct Out {
    uint32_t xi;
    uint8_t out;  // index of the output variable in the XOR
  };
  std::vector<Out> outs;
  for (uint32_t xi = 0; xi < xors.size(); ++xi) {
    for (uint8_t k = 0; k < xors[xi].n; ++k) outs.push_back(Out{xi, k});
  }
  auto key_less = [&](const Out& a, const Out& b) {
    const Xor& xa = xors[a.xi];
    const Xor& xb = xors[b.xi];
    if (xa.n != xb.n) return xa.n < xb.n;
    for (int k = 0, ka = 0, kb = 0; k < xa.n - 1; ++k, ++ka, ++kb) {
      if (ka == a.out) ++ka;
      if (kb == b.out) ++kb;
      if (xa.vars[ka] != xb.vars[kb]) return xa.vars[ka] < xb.vars[kb];
    }
    return false;
  };
  std::sort(outs.begin(), outs.end(), [&](const Out& a, const Out& b) {
    if (key_less(a, b)) return true;
    if (key_less(b, a)) return false;
    return a.xi < b.xi;
  });
  budget += outs.size();
  uint32_t found = 0;
  std::vector<Lit> cl;
  std::vector<Var> cases;
  for (size_t i = 0; i < outs.size();) {
    size_t j = i + 1;
    while (j < outs.size() && !key_less(outs[i], outs[j])) ++j;
    const Xor& xa = xors[outs[i].xi];
    const Var ya = xa.vars[outs[i].out];
    for (size_t k = i + 1; k < j; ++k) {
      const Xor& xb = xors[outs[k].xi];
      const Var yb = xb.vars[outs[k].out];
      if (ya == yb) continue;  // duplicate XOR
      // ya + S = pa, yb + S = pb  =>  ya = yb + pa + pb.
      const bool negated = ((xa.parity ^ xb.parity) & 1) != 0;
      const Lit a = make_lit(ya, false);
      const Lit b = make_lit(yb, negated);
      if (vals_[a] != 0 || vals_[b] != 0) continue;
      const Lit e1[2] = {negate(a), b};
      const Lit e2[2] = {a, negate(b)};
      if (proof_) {
        cases.clear();
        for (int m = 0; m < xa.n; ++m) {
          if (m != outs[i].out) cases.push_back(xa.vars[m]);
        }
        cases.pop_back();  // the last input is forced by the case split
        // Each call ends with the base clause added and all helper clauses deleted.
        cl.assign(e1, e1 + 2);
        prove_by_cases(cl, cases, 0);
        cl.assign(e2, e2 + 2);
        prove_by_cases(cl, cases, 0);
      }
      add_binary(e1[0], e1[1], false);
      add_binary(e2[0], e2[1], false);
      ++found;
    }
    i = j;
  }
  stats_.congruent_xors += found;
  return found;
}

// If-then-else gates o = ITE(c, t, e), given by the ternary clauses (-c -t o) (-c t -o) (c -e o)
// (c e -o). Normalized so that c and t are positive literals (ITE(-c,t,e) = ITE(c,e,t) and
// ITE(c,-t,-e) = -ITE(c,t,e)); two gates with the same (c, t, e) have equivalent outputs. Each
// equivalence clause is proved by a case split on c: (-o1 v o2 v c) and (-o1 v o2 v -c) are RUP
// by the gate clauses, and their resolvent is the binary clause.
uint32_t Solver::congruent_ites(uint64_t& budget) {
  // Live irredundant ternary clauses without assigned literals: a sorted set of sorted triples,
  // and their occurrence lists (CSR).
  using Triple = std::array<Lit, 3>;
  std::vector<Triple> tri;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size != 3) continue;
    Triple t{c.lits()[0], c.lits()[1], c.lits()[2]};
    if (vals_[t[0]] || vals_[t[1]] || vals_[t[2]]) continue;
    small_sort(t.data(), 3);
    tri.push_back(t);
  }
  if (tri.size() < 8) return 0;
  std::sort(tri.begin(), tri.end());
  tri.erase(std::unique(tri.begin(), tri.end()), tri.end());
  budget += tri.size();
  auto has = [&](Lit a, Lit b, Lit d) {
    Triple t{a, b, d};
    small_sort(t.data(), 3);
    return std::binary_search(tri.begin(), tri.end(), t);
  };
  const size_t nlits = 2 * size_t{num_vars_};
  std::vector<uint32_t> start(nlits + 1, 0), occ;
  for (const Triple& t : tri) {
    for (const Lit l : t) ++start[l + 1];
  }
  for (size_t l = 0; l < nlits; ++l) start[l + 1] += start[l];
  occ.resize(start[nlits]);
  {
    std::vector<uint32_t> fill(start.begin(), start.end() - 1);
    for (uint32_t i = 0; i < tri.size(); ++i) {
      for (const Lit l : tri[i]) occ[fill[l]++] = i;
    }
  }
  struct Ite {
    Lit c, t, e, o;
  };
  std::vector<Ite> gates;
  constexpr uint32_t kMaxOcc = 32;  // pairs per literal are quadratic: skip very frequent ones
  for (Lit no = 0; no < nlits; ++no) {  // no = -o: clauses (x y -o)
    const uint32_t b = start[no], n = start[no + 1] - b;
    if (n < 2 || n > kMaxOcc || eliminated_[var_of(no)]) continue;
    const Lit o = negate(no);
    budget += n * n / 2 + 1;
    for (uint32_t i = 0; i < n; ++i) {
      const Triple& t1 = tri[occ[b + i]];
      Lit p[2], m = 0;
      for (const Lit l : t1) {
        if (l != no) p[m++] = l;
      }
      for (uint32_t j = i + 1; j < n; ++j) {
        const Triple& t2 = tri[occ[b + j]];
        Lit q[2], k = 0;
        for (const Lit l : t2) {
          if (l != no) q[k++] = l;
        }
        // (-c v t v -o) and (c v e v -o): one literal of each clause is the condition.
        for (int x = 0; x < 2; ++x) {
          for (int y = 0; y < 2; ++y) {
            if (p[x] != negate(q[y])) continue;
            const Lit c = q[y], t = p[1 - x], e = q[1 - y];
            if (var_of(t) == var_of(e) || var_of(t) == var_of(c) || var_of(e) == var_of(c)) continue;
            if (var_of(o) == var_of(t) || var_of(o) == var_of(e) || var_of(o) == var_of(c)) continue;
            if (!has(negate(c), negate(t), o) || !has(c, negate(e), o)) continue;
            Ite g{c, t, e, o};
            if (is_negative(g.c)) {
              g.c = negate(g.c);
              std::swap(g.t, g.e);
            }
            if (is_negative(g.t)) {
              g.t = negate(g.t);
              g.e = negate(g.e);
              g.o = negate(g.o);
            }
            gates.push_back(g);
          }
        }
      }
    }
  }
  if (gates.size() < 2) return 0;
  std::sort(gates.begin(), gates.end(), [](const Ite& a, const Ite& b) {
    if (a.c != b.c) return a.c < b.c;
    if (a.t != b.t) return a.t < b.t;
    if (a.e != b.e) return a.e < b.e;
    return a.o < b.o;
  });
  budget += gates.size();
  uint32_t found = 0;
  std::vector<Lit> cl;
  std::vector<Var> cases;
  for (size_t i = 0; i < gates.size();) {
    size_t j = i + 1;
    while (j < gates.size() && gates[j].c == gates[i].c && gates[j].t == gates[i].t && gates[j].e == gates[i].e) ++j;
    const Lit a = gates[i].o;
    for (size_t k = i + 1; k < j; ++k) {
      const Lit b = gates[k].o;
      if (var_of(a) == var_of(b)) continue;  // the same gate found from both output phases
      if (vals_[a] != 0 || vals_[b] != 0) continue;
      const Lit e1[2] = {negate(a), b};
      const Lit e2[2] = {a, negate(b)};
      if (proof_) {
        cases.assign(1, var_of(gates[i].c));
        cl.assign(e1, e1 + 2);
        prove_by_cases(cl, cases, 0);
        cl.assign(e2, e2 + 2);
        prove_by_cases(cl, cases, 0);
      }
      add_binary(e1[0], e1[1], false);
      add_binary(e2[0], e2[1], false);
      ++found;
    }
    i = j;
  }
  stats_.congruent_ites += found;
  return found;
}

}  // namespace psat
