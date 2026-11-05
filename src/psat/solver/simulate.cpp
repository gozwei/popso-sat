// Equivalences proposed by random simulation and proven by Kitten on small windows (our pass;
// sweeping only looks for equivalences inside the environment of one variable, congruence
// closure only between gates with identical inputs).
//
// AND gates lhs = AND(r1..rk) are taken from the binary clauses (-lhs v ri) and a base clause
// (lhs v -r1 v ... v -rk), ordered topologically (an input on a cycle keeps a random value) and
// evaluated on 64 * kWords random input vectors. Variables with equal or complementary
// signatures are candidates; each is checked against the lowest member of its class, bottom-up,
// by Kitten on a window: the gate clauses of both fan-in cones down to a depth limit, plus the
// binary clauses of the equivalences proven so far (the cones of two copies of a circuit meet at
// proven nodes, so the windows stay small). Both directions unsatisfiable: the two binary
// clauses Kitten implies are added (its derivation emitted to the proof first, as in sweeping);
// substitution and congruence closure merge them in the elimination round that follows.

#include <algorithm>
#include <array>
#include <bit>
#include <cstdio>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

namespace {

constexpr uint32_t kNone = UINT32_MAX;
constexpr uint32_t kWords = 8;                // 512 simulation vectors
constexpr uint64_t kSimSolveTicks = 200000;   // Kitten ticks per check
constexpr uint32_t kWindowVars = 8192, kWindowClauses = 32768;

}  // namespace

void Solver::simulate_equivalences() {
  const PassTimer pass_timer(*this, kPassSimulate);
  if (inconsistent_ || !backtrack_to_root()) return;
  // Per-variable arrays (about 30 bytes per variable while the pass runs): skipped on huge formulas.
  constexpr Var kMaxVars = Var{1} << 24;
  if (num_vars_ > kMaxVars) return;
  ++stats_.simulations;
  const size_t nlits = 2 * size_t{num_vars_};
  uint64_t ticks = 0;
  const uint64_t limit = static_cast<uint64_t>(opts_.simeqticks) * 1000;

  // --- AND gates (one per output variable) ---
  std::vector<uint8_t> output(nlits, 0);
  for (Lit lhs = 0; lhs < nlits; ++lhs) {
    if (vals_[lhs] != 0 || eliminated_[var_of(lhs)]) continue;
    uint32_t cands = 0;
    for (const Watch& w : watches_[negate(lhs)]) {
      if (w.binary() && !w.redundant_binary() && vals_[w.blit] == 0 && ++cands >= 2) break;
    }
    output[lhs] = cands >= 2;
  }
  std::vector<uint32_t> start(nlits + 1, 0), occ;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant) continue;
    for (uint32_t k = 0; k < c.size; ++k) start[c.lits()[k] + 1] += output[c.lits()[k]];
  }
  for (size_t l = 0; l < nlits; ++l) start[l + 1] += start[l];
  occ.resize(start[nlits]);
  {
    std::vector<uint32_t> fill(start.begin(), start.end() - 1);
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (output[c.lits()[k]]) occ[fill[c.lits()[k]]++] = ref;
      }
    }
  }
  ticks += arena_.size() / 16 + occ.size() / 4;
  // AND: lhs = AND(inputs). XOR: var(lhs) = sign(lhs) xor (xor of the inputs), inputs positive.
  // ITE: lhs = ITE(c, t, e) with inputs (c, t, e).
  enum Kind : uint8_t { kAnd, kXor, kIte };
  struct Gate {
    Lit lhs;
    uint32_t begin, size;
    Kind kind;
  };
  std::vector<Gate> gates;
  std::vector<Lit> ins;
  std::vector<uint32_t> def(num_vars_, kNone);
  for (Lit lhs = 0; lhs < nlits; ++lhs) {
    if (!output[lhs] || def[var_of(lhs)] != kNone || start[lhs + 1] == start[lhs]) continue;
    uint32_t cands = 0;
    for (const Watch& w : watches_[negate(lhs)]) {
      if (w.binary() && !w.redundant_binary() && vals_[w.blit] == 0 && !marks_[w.blit]) {
        marks_[w.blit] = 1;
        ++cands;
      }
    }
    ticks += watches_[negate(lhs)].size() / 8 + 1;
    for (uint32_t o = start[lhs]; o < start[lhs + 1]; ++o) {
      const Clause& c = clause(occ[o]);
      if (c.size - 1 > cands) continue;
      ticks += c.size / 8 + 1;
      bool base = true;
      for (uint32_t k = 0; k < c.size && base; ++k) {
        const Lit y = c.lits()[k];
        if (y != lhs && !marks_[negate(y)]) base = false;
      }
      if (!base) continue;
      const uint32_t begin = static_cast<uint32_t>(ins.size());
      for (uint32_t k = 0; k < c.size; ++k) {
        if (c.lits()[k] != lhs) ins.push_back(negate(c.lits()[k]));
      }
      def[var_of(lhs)] = static_cast<uint32_t>(gates.size());
      gates.push_back(Gate{lhs, begin, static_cast<uint32_t>(ins.size() - begin), kAnd});
      break;
    }
    for (const Watch& w : watches_[negate(lhs)]) {
      if (w.binary()) marks_[w.blit] = 0;
    }
  }
  std::vector<uint8_t>().swap(output);
  std::vector<uint32_t>().swap(occ);
  std::vector<uint32_t>().swap(start);
  // XOR constraints over 3 to 5 variables, given by all 2^(n-1) clauses with the same parity of
  // negative literals; the output is the highest variable not defined by another gate.
  {
    auto mixv = [](uint64_t h) {
      h ^= h >> 33;
      h *= 0xFF51AFD7ED558CCDull;
      h ^= h >> 33;
      return h;
    };
    struct Row {
      uint64_t hash;
      uint32_t ref;
    };
    std::vector<Row> rows;
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant || c.size < 3 || c.size > 5) continue;
      uint64_t s1 = 0, s2 = 0;
      bool assigned = false;
      for (uint32_t k = 0; k < c.size; ++k) {
        assigned |= vals_[c.lits()[k]] != 0;
        const uint64_t m = mixv(var_of(c.lits()[k]) + 1);
        s1 += m;
        s2 ^= m * 0x9E3779B97F4A7C15ull;
      }
      if (!assigned) rows.push_back(Row{s1 ^ (s2 << 1) ^ c.size, ref});
    }
    ticks += clauses_.size() / 4 + rows.size();
    constexpr size_t kXorRows = size_t{1} << 22;
    if (rows.size() <= kXorRows) {
      std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) { return a.hash < b.hash; });
      ticks += rows.size();
      std::vector<Var> vars, other;
      std::vector<uint8_t> seen_mask(32);
      for (size_t i = 0; i < rows.size();) {
        size_t j = i + 1;
        while (j < rows.size() && rows[j].hash == rows[i].hash) ++j;
        const Clause& c0 = clause(rows[i].ref);
        const uint32_t n = c0.size;
        if (j - i >= (size_t{1} << (n - 1))) {
          vars.clear();
          for (uint32_t k = 0; k < n; ++k) vars.push_back(var_of(c0.lits()[k]));
          std::sort(vars.begin(), vars.end());
          std::fill(seen_mask.begin(), seen_mask.end(), 0);
          uint32_t distinct = 0;
          int parity = -1;
          bool ok = true;
          for (size_t r = i; r < j && ok; ++r) {
            const Clause& c = clause(rows[r].ref);
            if (c.size != n) continue;  // (a hash collision)
            uint32_t mask = 0;
            bool same = true;
            for (uint32_t k = 0; k < n && same; ++k) {
              const auto it = std::lower_bound(vars.begin(), vars.end(), var_of(c.lits()[k]));
              if (it == vars.end() || *it != var_of(c.lits()[k])) {
                same = false;
                break;
              }
              if (c.lits()[k] & 1u) mask |= 1u << (it - vars.begin());
            }
            if (!same) continue;
            const int p = std::popcount(mask) & 1;
            if (parity < 0) parity = p;
            if (p != parity) ok = false;
            if (!seen_mask[mask]) {
              seen_mask[mask] = 1;
              ++distinct;
            }
          }
          if (ok && distinct == (1u << (n - 1))) {
            Var out = kNone;
            for (size_t k = n; k-- > 0;) {
              if (def[vars[k]] == kNone) {
                out = vars[k];
                break;
              }
            }
            if (out != kNone) {
              const uint32_t begin = static_cast<uint32_t>(ins.size());
              for (const Var v : vars) {
                if (v != out) ins.push_back(make_lit(v, false));
              }
              const bool q = parity == 0;  // the sum of the variables is 1 - parity (mod 2)
              def[out] = static_cast<uint32_t>(gates.size());
              gates.push_back(Gate{make_lit(out, q), begin, n - 1, kXor});
            }
          }
        }
        ticks += j - i;
        i = j;
      }
    }
  }
  // If-then-else gates o = ITE(c, t, e): the ternary clause pairs (-c v o v -t), (-c v -o v t)
  // say c -> o = t, and (c v o v -e), (c v -o v e) say -c -> o = e (outputs not defined above).
  if (opts_.simeqite) {
    std::vector<std::array<Lit, 3>> tern;
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant || c.size != 3) continue;
      std::array<Lit, 3> t{c.lits()[0], c.lits()[1], c.lits()[2]};
      if (vals_[t[0]] || vals_[t[1]] || vals_[t[2]]) continue;
      std::sort(t.begin(), t.end());
      tern.push_back(t);
    }
    constexpr size_t kIteClauses = size_t{1} << 22;
    if (tern.size() <= kIteClauses) {
      std::sort(tern.begin(), tern.end());
      tern.erase(std::unique(tern.begin(), tern.end()), tern.end());
      ticks += tern.size() * 2;
      auto has = [&](Lit x, Lit y, Lit z) {
        std::array<Lit, 3> t{x, y, z};
        std::sort(t.begin(), t.end());
        ++ticks;
        return std::binary_search(tern.begin(), tern.end(), t);
      };
      struct Rec {
        Var o;
        Lit cond, t;  // cond -> o = t (o positive)
      };
      std::vector<Rec> recs;
      for (const auto& cl : tern) {
        for (int i = 0; i < 3; ++i) {
          const Lit p = cl[i], a = cl[(i + 1) % 3], b = cl[(i + 2) % 3];  // (p v a v b)
          if (!has(p, negate(a), negate(b))) continue;                   // and (p v -a v -b)
          // -p -> a = -b, and symmetrically -p -> b = -a.
          const Lit cond = negate(p);
          recs.push_back(a & 1u ? Rec{var_of(a), cond, b} : Rec{var_of(a), cond, negate(b)});
          recs.push_back(b & 1u ? Rec{var_of(b), cond, a} : Rec{var_of(b), cond, negate(a)});
        }
      }
      std::sort(recs.begin(), recs.end(), [](const Rec& x, const Rec& y) {
        if (x.o != y.o) return x.o < y.o;
        if (x.cond != y.cond) return x.cond < y.cond;
        return x.t < y.t;
      });
      ticks += recs.size();
      for (size_t i = 0; i < recs.size();) {
        size_t j = i + 1;
        while (j < recs.size() && recs[j].o == recs[i].o) ++j;
        const Var o = recs[i].o;
        if (def[o] == kNone) {
          // A pair of records with complementary conditions (neither involving o).
          for (size_t k = i; k < j && def[o] == kNone; ++k) {
            const Lit c = recs[k].cond;
            if (c & 1u || var_of(c) == o || var_of(recs[k].t) == o) continue;  // (c positive)
            for (size_t m = i; m < j; ++m) {
              if (recs[m].cond != negate(c) || var_of(recs[m].t) == o) continue;
              const uint32_t begin = static_cast<uint32_t>(ins.size());
              ins.push_back(c);
              ins.push_back(recs[k].t);
              ins.push_back(recs[m].t);
              def[o] = static_cast<uint32_t>(gates.size());
              gates.push_back(Gate{make_lit(o, false), begin, 3, kIte});
              ++stats_.sim_ites;
              break;
            }
          }
        }
        i = j;
      }
    }
  }
  stats_.sim_gates += gates.size();
  if (gates.size() < 2) return;

  // --- topological order (iterative DFS over the gate inputs) and levels ---
  std::vector<uint8_t> state(num_vars_, 0);  // 1: on the stack, 2: done
  std::vector<uint32_t> level(num_vars_, 0);
  std::vector<Var> order;
  order.reserve(gates.size());
  {
    struct Frame {
      Var v;
      uint32_t next;
    };
    std::vector<Frame> stack;
    for (const Gate& root : gates) {
      const Var r = var_of(root.lhs);
      if (state[r]) continue;
      stack.push_back(Frame{r, 0});
      state[r] = 1;
      while (!stack.empty()) {
        Frame& f = stack.back();
        const Gate& g = gates[def[f.v]];
        if (f.next < g.size) {
          const Var u = var_of(ins[g.begin + f.next++]);
          if (def[u] != kNone && state[u] == 0) {
            state[u] = 1;
            stack.push_back(Frame{u, 0});
          }
          continue;
        }
        uint32_t lv = 0;
        for (uint32_t k = 0; k < g.size; ++k) {
          const Var u = var_of(ins[g.begin + k]);
          if (state[u] == 2) lv = std::max(lv, level[u]);
        }
        level[f.v] = lv + 1;
        state[f.v] = 2;
        order.push_back(f.v);
        stack.pop_back();
      }
    }
    ticks += ins.size() / 2 + gates.size();
  }

  // --- simulation (signatures only for gate outputs and inputs, in a compact index) ---
  std::vector<uint32_t> idx(num_vars_, kNone);
  uint32_t nrel = 0;
  for (const Gate& g : gates) {
    if (idx[var_of(g.lhs)] == kNone) idx[var_of(g.lhs)] = nrel++;
    for (uint32_t k = 0; k < g.size; ++k) {
      if (idx[var_of(ins[g.begin + k])] == kNone) idx[var_of(ins[g.begin + k])] = nrel++;
    }
  }
  std::vector<uint64_t> sig(size_t{nrel} * kWords);
  // Its own generator (from --seed): the pass does not shift the random choices of the others.
  uint64_t rng = 0x9E3779B97F4A7C15ull ^ (static_cast<uint64_t>(opts_.seed) * 0xD1B54A32D192ED03ull);
  auto next_random = [&]() {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
  };
  for (uint64_t& w : sig) w = next_random();
  for (const Var v : order) {
    const Gate& g = gates[def[v]];
    uint64_t* out = &sig[size_t{idx[v]} * kWords];
    uint64_t acc[kWords];
    auto word = [&](Lit r, uint32_t w) {
      return sig[size_t{idx[var_of(r)]} * kWords + w] ^ ((r & 1u) ? ~uint64_t{0} : 0);
    };
    if (g.kind == kIte) {
      const Lit c = ins[g.begin], t = ins[g.begin + 1], e = ins[g.begin + 2];
      for (uint32_t w = 0; w < kWords; ++w) acc[w] = (word(c, w) & word(t, w)) | (~word(c, w) & word(e, w));
    } else {
      for (uint32_t w = 0; w < kWords; ++w) acc[w] = g.kind == kXor ? 0 : ~uint64_t{0};
      for (uint32_t k = 0; k < g.size; ++k) {
        const Lit r = ins[g.begin + k];
        if (g.kind == kXor) {
          for (uint32_t w = 0; w < kWords; ++w) acc[w] ^= word(r, w);
        } else {
          for (uint32_t w = 0; w < kWords; ++w) acc[w] &= word(r, w);
        }
      }
    }
    const uint64_t flip = (g.lhs & 1u) ? ~uint64_t{0} : 0;  // v = -lhs when lhs is negative
    for (uint32_t w = 0; w < kWords; ++w) out[w] = acc[w] ^ flip;
  }
  ticks += order.size() * kWords / 4 + ins.size();

  // --- candidate classes: gate outputs and inputs with equal normalized signatures ---
  std::vector<uint8_t> neg(num_vars_, 0);  // the normalized signature is the complement
  struct Entry {
    uint64_t hash;
    Var v;
  };
  std::vector<Entry> entries;
  std::vector<Var> consts;
  for (Var v = 0; v < num_vars_; ++v) {
    if (idx[v] == kNone || vals_[make_lit(v, false)] != 0 || eliminated_[v]) continue;
    const uint64_t* s = &sig[size_t{idx[v]} * kWords];
    neg[v] = s[0] & 1u;
    const uint64_t flip = neg[v] ? ~uint64_t{0} : 0;
    uint64_t h = 0x9E3779B97F4A7C15ull, any = 0;
    for (uint32_t w = 0; w < kWords; ++w) {
      any |= s[w] ^ flip;
      h = (h ^ (s[w] ^ flip)) * 0x100000001B3ull;
    }
    if (!any) {  // constant under simulation (wide AND gates are nearly always false: mostly wrong)
      if (opts_.simeqconst) consts.push_back(v);
      continue;
    }
    entries.push_back(Entry{h, v});
  }
  auto same_sig = [&](Var a, Var b) {
    const uint64_t fa = neg[a] ? ~uint64_t{0} : 0, fb = neg[b] ? ~uint64_t{0} : 0;
    for (uint32_t w = 0; w < kWords; ++w) {
      if ((sig[size_t{idx[a]} * kWords + w] ^ fa) != (sig[size_t{idx[b]} * kWords + w] ^ fb)) return false;
    }
    return true;
  };
  std::sort(entries.begin(), entries.end(), [&](const Entry& a, const Entry& b) {
    if (a.hash != b.hash) return a.hash < b.hash;
    if (level[a.v] != level[b.v]) return level[a.v] < level[b.v];
    return a.v < b.v;
  });
  ticks += entries.size();
  struct Cand {
    Var m, rep;
    uint32_t lvl;
  };
  std::vector<Cand> cands;
  for (size_t i = 0; i < entries.size();) {
    size_t j = i + 1;
    while (j < entries.size() && entries[j].hash == entries[i].hash) ++j;
    // Within one hash: members equal to the first, the rest (hash collisions) are skipped.
    const Var rep = entries[i].v;
    for (size_t k = i + 1; k < j; ++k) {
      if (same_sig(rep, entries[k].v)) cands.push_back(Cand{entries[k].v, rep, level[entries[k].v]});
    }
    i = j;
  }
  for (const Var v : consts) cands.push_back(Cand{v, kNone, level[v]});  // (rep kNone: a constant)
  std::stable_sort(cands.begin(), cands.end(), [](const Cand& a, const Cand& b) { return a.lvl < b.lvl; });
  stats_.sim_candidates += cands.size();
  std::vector<uint64_t>().swap(sig);
  std::vector<Entry>().swap(entries);

  // --- proofs, bottom-up ---
  std::vector<Lit> rep(num_vars_);  // union-find over literals (as in congruence closure)
  for (Var v = 0; v < num_vars_; ++v) rep[v] = make_lit(v, false);
  auto find = [&](Lit l) {
    Lit r = l;
    for (;;) {
      const Lit p = rep[var_of(r)] ^ (r & 1u);
      if (p == r) break;
      r = p;
    }
    for (Lit x = l; x != r;) {
      const Lit p = rep[var_of(x)] ^ (x & 1u);
      rep[var_of(x)] = r ^ (x & 1u);
      x = p;
    }
    return r;
  };
  // The binary clauses of the proven pairs, per variable: (own literal, partner literal). A window
  // follows these (the clauses in the formula), not shortcuts to the representative.
  struct EqEdge {
    Lit own, partner;
    uint32_t next;
  };
  std::vector<EqEdge> eq_edges;
  std::vector<uint32_t> eq_head(num_vars_, kNone);
  if (sweep_local_.size() < num_vars_) sweep_local_.resize(num_vars_, kNone);
  std::vector<uint32_t> depth;
  std::vector<Kitten::KLit> kc;
  std::vector<Lit> flat;  // window clauses: size, literals...
  std::vector<Lit> implied[2];
  const uint32_t max_depth = static_cast<uint32_t>(opts_.simeqdepth);
  for (const Cand& cd : cands) {
    if (ticks > limit || inconsistent_) break;
    const bool constant = cd.rep == kNone;
    if (vals_[make_lit(cd.m, false)] != 0 || eliminated_[cd.m]) continue;
    if (!constant && (vals_[make_lit(cd.rep, false)] != 0 || eliminated_[cd.rep])) continue;
    const Lit a = make_lit(cd.m, false);
    // A pair: a = b by the signatures. A constant: the unit u (a when it was always true).
    const Lit b = constant ? kNoLit : make_lit(cd.rep, neg[cd.m] != neg[cd.rep]);
    const Lit unit = neg[cd.m] ? a : negate(a);
    if (!constant) {
      const Lit ra = find(a), rb = find(b);
      if (ra == rb || ra == negate(rb)) continue;
    }
    ++stats_.sim_checked;
    // Window: breadth first from both variables through the gate definitions.
    sweep_env_.clear();
    depth.clear();
    flat.clear();
    uint32_t nclauses = 0;
    auto local = [&](Var u, uint32_t d) {
      if (sweep_local_[u] != kNone) return true;
      if (sweep_env_.size() >= kWindowVars) return false;
      sweep_local_[u] = static_cast<uint32_t>(sweep_env_.size());
      sweep_env_.push_back(u);
      depth.push_back(d);
      return true;
    };
    // A clause of the formula restricted to the unassigned literals (skipped when satisfied).
    auto push_clause = [&](const Lit* lits, uint32_t size, uint32_t d) {
      for (uint32_t k = 0; k < size; ++k) {
        if (vals_[lits[k]] > 0) return;
      }
      for (uint32_t k = 0; k < size; ++k) {
        if (vals_[lits[k]] == 0 && !local(var_of(lits[k]), d)) return;
      }
      const size_t at = flat.size();
      flat.push_back(0);
      for (uint32_t k = 0; k < size; ++k) {
        if (vals_[lits[k]] == 0) flat.push_back(lits[k]);
      }
      flat[at] = static_cast<Lit>(flat.size() - at - 1);
      ++nclauses;
    };
    local(cd.m, 0);
    if (!constant) local(cd.rep, 0);
    for (size_t i = 0; i < sweep_env_.size() && nclauses < kWindowClauses; ++i) {
      const Var u = sweep_env_[i];
      const uint32_t d = depth[i];
      const Lit pu = make_lit(u, false);
      ++ticks;
      // Proven equivalent to other variables earlier in this pass: their binary clauses (the
      // partners join the window at the same depth); only a representative expands its gate.
      for (uint32_t e = eq_head[u]; e != kNone; e = eq_edges[e].next) {
        const Lit own = eq_edges[e].own, partner = eq_edges[e].partner;
        const Lit e1[2] = {negate(own), partner}, e2[2] = {own, negate(partner)};
        push_clause(e1, 2, d);
        push_clause(e2, 2, d);
      }
      if (find(pu) != pu) continue;
      if (def[u] == kNone || d >= max_depth) continue;
      const Gate& g = gates[def[u]];
      if (g.kind == kIte) {
        const Lit o = g.lhs, c = ins[g.begin], t = ins[g.begin + 1], e = ins[g.begin + 2];
        const Lit ite[4][3] = {{negate(c), negate(t), o}, {negate(c), t, negate(o)}, {c, negate(e), o}, {c, e, negate(o)}};
        for (const auto& cl : ite) push_clause(cl, 3, d + 1);
        ticks += 4;
        continue;
      }
      if (g.kind == kXor) {
        // The 2^(n-1) clauses: every sign pattern whose number of negative literals differs in
        // parity from the sum (exactly the clauses found in the formula).
        const uint32_t n = g.size + 1;
        const uint32_t want = (g.lhs & 1u) ? 0u : 1u;  // parity of the negative literals
        for (uint32_t mask = 0; mask < (1u << n); ++mask) {
          if ((static_cast<uint32_t>(std::popcount(mask)) & 1u) != want) continue;
          kc.clear();
          kc.push_back(make_lit(var_of(g.lhs), (mask & 1u) != 0));
          for (uint32_t k = 0; k < g.size; ++k) kc.push_back(make_lit(var_of(ins[g.begin + k]), ((mask >> (k + 1)) & 1u) != 0));
          push_clause(kc.data(), n, d + 1);
        }
        ticks += (1u << n);
        continue;
      }
      for (uint32_t k = 0; k < g.size; ++k) {
        const Lit bin[2] = {negate(g.lhs), ins[g.begin + k]};
        push_clause(bin, 2, d + 1);
      }
      kc.clear();  // (reused as a literal buffer for the base clause)
      kc.push_back(g.lhs);
      for (uint32_t k = 0; k < g.size; ++k) kc.push_back(negate(ins[g.begin + k]));
      push_clause(kc.data(), static_cast<uint32_t>(kc.size()), d + 1);
      ticks += g.size + 1;
    }
    kitten_.clear();
    kitten_.resize(static_cast<uint32_t>(sweep_env_.size()));
    auto klit = [&](Lit l) -> Kitten::KLit { return 2 * sweep_local_[var_of(l)] + (l & 1u); };
    for (size_t at = 0; at < flat.size(); at += flat[at] + 1) {
      kc.clear();
      for (uint32_t k = 1; k <= flat[at]; ++k) kc.push_back(klit(flat[at + k]));
      kitten_.add_clause(kc.data(), static_cast<uint32_t>(kc.size()));
    }
    ticks += flat.size() / 4;
    sweep_emitted_ = 0;
    sweep_emitted_lits_.clear();
    sweep_added_.clear();
    const uint64_t kitten_start = kitten_.ticks();
    bool proved = true;
    for (int dir = 0; dir < (constant ? 1 : 2) && proved; ++dir) {
      if (constant) {
        kitten_.assume(klit(unit) ^ 1u);
      } else {
        kitten_.assume(dir == 0 ? klit(a) : klit(a) ^ 1u);
        kitten_.assume(dir == 0 ? klit(b) ^ 1u : klit(b));
      }
      const int r = kitten_.solve(kSimSolveTicks);
      if (r != Kitten::kUnsat) {
        proved = false;
        break;
      }
      implied[dir].clear();
      for (const Kitten::KLit k : kitten_.final_clause()) implied[dir].push_back(make_lit(sweep_env_[k >> 1], (k & 1u) != 0));
      if (kitten_.inconsistent()) implied[dir].clear();
    }
    ticks += kitten_.ticks() - kitten_start;
    if (proved) {
      sweep_emit_learned();
      bool ok = true;
      for (int dir = 0; dir < (constant ? 1 : 2) && ok; ++dir) {
        if (implied[dir].size() == 1) ++stats_.sim_units;
        ok = sweep_add(implied[dir].data(), static_cast<uint32_t>(implied[dir].size()));
      }
      if (ok && !constant && implied[0].size() == 2 && implied[1].size() == 2) {
        ++stats_.sim_equivalences;
        eq_edges.push_back(EqEdge{a, b, eq_head[var_of(a)]});
        eq_head[var_of(a)] = static_cast<uint32_t>(eq_edges.size() - 1);
        eq_edges.push_back(EqEdge{b, a, eq_head[var_of(b)]});
        eq_head[var_of(b)] = static_cast<uint32_t>(eq_edges.size() - 1);
        const Lit fa = find(a), fb = find(b);
        if (fa != fb && fa != negate(fb)) rep[var_of(fb)] = fa ^ (fb & 1u);  // b's class joins a's
      }
    } else {
      ++stats_.sim_failed;
    }
    sweep_retire_learned();
    for (const Var u : sweep_env_) sweep_local_[u] = kNone;
  }
  stats_.sim_ticks += ticks;
  if (opts_.verbose >= 2) {
    std::printf("c [%.2f s] simulation: %zu gates, %zu candidates, %llu checked, %llu equivalences, %llu failed\n",
                seconds(), gates.size(), cands.size(), static_cast<unsigned long long>(stats_.sim_checked),
                static_cast<unsigned long long>(stats_.sim_equivalences),
                static_cast<unsigned long long>(stats_.sim_failed));
    std::fflush(stdout);
  }
}

}  // namespace psat
