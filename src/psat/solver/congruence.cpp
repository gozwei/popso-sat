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

namespace {

constexpr size_t kFilterBlock = 16;  // keys whose filter slots are prefetched together

// Saturating 8-bit counters indexed by a hash of a key: count(h) is at least the number of adds
// of h (collisions only raise it). Filters the clauses that can be part of a gate before the
// exact (sorting) passes: on large formulas with millions of ternary clauses and few or no
// gates, sorting all of them cost seconds per elimination round.
class CountFilter {
 public:
  explicit CountFilter(size_t keys) {
    size_t n = 1024;
    while (n < 2 * keys && n < (size_t{1} << 26)) n <<= 1;
    counts_.assign(n, 0);
    mask_ = n - 1;
  }
  void add(uint64_t h) {
    uint8_t& c = counts_[mix(h) & mask_];
    if (c < 255) ++c;
  }
  uint32_t count(uint64_t h) const { return counts_[mix(h) & mask_]; }
  // The table is large (up to 64 MB) and its slots are hit at random: callers prefetch the slots
  // of a block of keys before adding or counting them.
  void prefetch(uint64_t h) const { PSAT_PREFETCH(counts_.data() + (mix(h) & mask_)); }
  size_t size() const { return counts_.size(); }

 private:
  static uint64_t mix(uint64_t h) {
    h ^= h >> 33;
    h *= 0xFF51AFD7ED558CCDull;
    h ^= h >> 33;
    return h;
  }
  std::vector<uint8_t> counts_;
  uint64_t mask_ = 0;
};

}  // namespace

uint32_t Solver::congruence(uint64_t& budget) {
  const PassTimer pass_timer(*this, kPassCongruence);
  const size_t nlits = 2 * size_t{num_vars_};
  // Possible outputs: literals lhs with binary clauses (-lhs v x) to at least two unassigned
  // literals x. Occurrence lists (CSR) of the live irredundant long clauses are built only for
  // them (on formulas with few binary clauses that skips most of the formula).
  std::vector<uint8_t> output(nlits, 0);
  size_t outputs = 0;
  for (Lit lhs = 0; lhs < nlits; ++lhs) {
    if (vals_[lhs] != 0 || eliminated_[var_of(lhs)]) continue;
    uint32_t cands = 0;
    for (const Watch& w : watches_[negate(lhs)]) {
      if (w.binary() && vals_[w.blit] == 0 && ++cands >= 2) break;
    }
    if (cands >= 2) {
      output[lhs] = 1;
      ++outputs;
    }
  }
  budget += nlits / 8;
  std::vector<uint32_t> start(nlits + 1, 0), occ;
  if (outputs && !stop_requested()) {
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) start[c.lits()[k] + 1] += output[c.lits()[k]];
    }
    for (size_t l = 0; l < nlits; ++l) start[l + 1] += start[l];
    occ.resize(start[nlits]);
    std::vector<uint32_t> fill(start.begin(), start.end() - 1);
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (output[c.lits()[k]]) occ[fill[c.lits()[k]]++] = ref;
      }
    }
    budget += arena_.size() / 16 + occ.size() / 4;
  }
  std::vector<uint8_t>().swap(output);

  // Extract gates: (sorted inputs, lhs), stored flat.
  // kind: AND (inputs sorted), XOR (lhs = XOR of the inputs, positive literals, sorted; one gate
  // per choice of output of an XOR constraint) or ITE (inputs c, t, e with c and t positive);
  // flip: the normalized gate's output is lhs ^ flip (XOR and ITE normalization moves signs).
  enum : uint8_t { kAnd, kXor, kIte };
  struct Gate {
    uint64_t hash;
    uint32_t begin, size;  // inputs in gate_inputs
    Lit lhs;
    uint8_t kind = kAnd, flip = 0;
  };
  std::vector<Gate> gates;
  std::vector<Lit> inputs;
  for (Lit lhs = 0; lhs < nlits; ++lhs) {
    if (vals_[lhs] != 0 || eliminated_[var_of(lhs)]) continue;
    if (start[lhs + 1] == start[lhs]) continue;
    if (stop_requested()) break;  // (the gates so far: every merge below is still justified)
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
        gates.push_back(Gate{h, begin, static_cast<uint32_t>(inputs.size() - begin), lhs, kAnd, 0});
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
  const bool joined = opts_.congruenceclosure && opts_.congruencegates;
  if (joined) {
    // XOR and ITE gates join the closure: an equivalence found through one kind renames the
    // inputs of the others in the same call (BMC unrollings alternate AND levels with XOR and ITE
    // levels: matching them pairwise needed one call plus a substitution per level).
    std::vector<CongruenceXor> xors;
    extract_xor_constraints(xors, budget);
    for (const CongruenceXor& x : xors) {
      for (uint32_t k = 0; k < x.n; ++k) {
        const uint32_t begin = static_cast<uint32_t>(inputs.size());
        for (uint32_t m = 0; m < x.n; ++m) {
          if (m != k) inputs.push_back(make_lit(x.vars[m], false));
        }
        // v_k = parity + XOR(others): the output literal is v_k, negated for an odd parity.
        gates.push_back(Gate{0, begin, static_cast<uint32_t>(x.n - 1), make_lit(x.vars[k], x.parity != 0), kXor, 0});
      }
    }
    std::vector<CongruenceXor>().swap(xors);
    std::vector<CongruenceIte> ites;
    extract_ites(ites, budget);
    for (const CongruenceIte& t : ites) {
      const uint32_t begin = static_cast<uint32_t>(inputs.size());
      inputs.push_back(t.c);
      inputs.push_back(t.t);
      inputs.push_back(t.e);
      gates.push_back(Gate{0, begin, 3, t.o, kIte, 0});
    }
  }
  if (opts_.verbose >= 3) {
    size_t kinds[3] = {0, 0, 0};
    for (const Gate& g : gates) ++kinds[g.kind];
    std::printf("c   congruence gates: and %zu, xor %zu (per output), ite %zu\n", kinds[kAnd], kinds[kXor], kinds[kIte]);
  }
  if (gates.size() < 2) {
    std::vector<Gate>().swap(gates);
    std::vector<Lit>().swap(inputs);
    if (!joined) {
      found += congruent_xors(budget);
      found += congruent_ites(budget);
    }
    stats_.congruent += found;
    return found;
  }

  if (opts_.congruenceclosure) {
    // Congruence closure (AND gates): the outputs of gates with the same inputs are merged in a
    // union-find over literals; after a merge only the gates with an input in the absorbed class
    // are normalized again (inputs replaced by their representatives, sorted, duplicates
    // removed) and looked up again. Chains of gates (two copies of a circuit in a miter)
    // collapse in one call; matching the inputs as they are merged one level per call and
    // substitution in between (manol-pipe: 16 calls in a row, each a pass over the formula).
    // Each equivalence is added as two binary clauses when it is found, RUP given the earlier
    // ones: a class is connected by the binary clauses of its merges, so the inputs of one gate
    // imply those of the other, whose base clause then gives its output. A gate whose inputs
    // collapse to a single literal x gives lhs = x (both binaries RUP the same way); one with
    // complementary inputs or its own output among them is dropped.
    const uint32_t ng = static_cast<uint32_t>(gates.size());
    std::vector<Lit> rep(num_vars_);
    for (Var v = 0; v < num_vars_; ++v) rep[v] = make_lit(v, false);
    auto find = [&](Lit l) {
      Lit r = l;
      for (;;) {
        const Lit p = rep[var_of(r)] ^ (r & 1u);
        if (p == r) break;
        r = p;
      }
      for (Lit x = l; x != r;) {  // path compression
        const Lit p = rep[var_of(x)] ^ (x & 1u);
        rep[var_of(x)] = r ^ (x & 1u);
        x = p;
      }
      return r;
    };
    // Gates with an input in the class of a root variable (lists move to the surviving root):
    // every variable's own gates (increasing) are a run of class_list, and a class is the chain of
    // runs starting at its root, linked through class_next (class_tail: the last run, class_size:
    // the gates in the chain). A join appends the absorbed chain, so a class lists its gates in
    // the order of a list per variable that is appended to (without an allocation per variable).
    std::vector<uint32_t> class_start(size_t{num_vars_} + 1, 0);
    for (uint32_t g = 0; g < ng; ++g) {
      for (uint32_t k = 0; k < gates[g].size; ++k) ++class_start[var_of(inputs[gates[g].begin + k]) + 1];
    }
    for (Var v = 0; v < num_vars_; ++v) class_start[v + 1] += class_start[v];
    std::vector<uint32_t> class_list(class_start[num_vars_]);
    {
      std::vector<uint32_t> fill(class_start.begin(), class_start.end() - 1);
      for (uint32_t g = 0; g < ng; ++g) {
        for (uint32_t k = 0; k < gates[g].size; ++k) class_list[fill[var_of(inputs[gates[g].begin + k])]++] = g;
      }
    }
    constexpr uint32_t kNoRun = UINT32_MAX;
    std::vector<uint32_t> class_next(num_vars_, kNoRun), class_tail(num_vars_), class_size(num_vars_);
    for (Var v = 0; v < num_vars_; ++v) {
      class_tail[v] = v;
      class_size[v] = class_start[v + 1] - class_start[v];
    }
    budget += inputs.size() / 4 + ng;
    std::vector<uint32_t> queue(ng);
    for (uint32_t g = 0; g < ng; ++g) queue[g] = g;
    // A merge of a with b adds (-a v b) and (a v -b). Both are RUP for AND gates and degenerate
    // gates; for XOR and ITE partners they follow from a case split over the inputs (all but one
    // for XOR, the condition for ITE: every leaf is RUP through the earlier equivalences and
    // the two gates' clauses), written by prove_by_cases.
    std::vector<Lit> case_clause;
    std::vector<Var> cases;
    // Classes already complementary (a gate equal to the negation of an equal gate): the two
    // binary clauses are still RUP and make the formula unsatisfiable, which the substitution
    // after this call finds (x equivalent to -x); the classes are not joined.
    auto merge = [&](Lit a, Lit b, const Gate* split = nullptr) {
      Lit ra = find(a), rb = find(b);
      if (ra == rb || var_of(a) == var_of(b)) return false;  // (a gate equal to its own negation: left to search)
      const bool contradiction = ra == negate(rb);
      const Lit e1[2] = {negate(a), b};
      const Lit e2[2] = {a, negate(b)};
      if (proof_ && split) {
        const Lit* in = inputs.data() + split->begin;
        cases.clear();
        if (split->kind == kXor) {
          for (uint32_t k = 0; k + 1 < split->size; ++k) cases.push_back(var_of(in[k]));
        } else {
          cases.push_back(var_of(in[0]));
        }
        case_clause.assign(e1, e1 + 2);
        prove_by_cases(case_clause, cases, 0);
        case_clause.assign(e2, e2 + 2);
        prove_by_cases(case_clause, cases, 0);
      } else if (proof_) {
        proof_->add(e1, 2);
        proof_->add(e2, 2);
      }
      add_binary(e1[0], e1[1], false);
      add_binary(e2[0], e2[1], false);
      if (contradiction) return true;
      if (class_size[var_of(ra)] < class_size[var_of(rb)]) std::swap(ra, rb);
      rep[var_of(rb)] = ra ^ (rb & 1u);  // rb's class joins ra's
      const Var into = var_of(ra), moved = var_of(rb);
      for (uint32_t x = moved; x != kNoRun; x = class_next[x]) {
        queue.insert(queue.end(), class_list.begin() + class_start[x], class_list.begin() + class_start[x + 1]);
      }
      class_next[class_tail[into]] = moved;
      class_tail[into] = class_tail[moved];
      class_size[into] += class_size[moved];
      budget += class_size[moved] + 1;
      class_size[moved] = 0;
      return true;
    };
    // Open addressing on the hash of the normalized inputs; an entry is stale once its gate was
    // normalized to another hash (or dropped).
    auto mix = [](uint64_t h) {
      h ^= h >> 33;
      h *= 0xC4CEB9FE1A85EC53ull;
      h ^= h >> 29;
      return h;
    };
    struct Slot {
      uint64_t hash;
      uint32_t gate;
    };
    constexpr uint32_t kEmpty = UINT32_MAX;
    std::vector<Slot> table(std::bit_ceil(2 * size_t{ng} + 16), Slot{0, kEmpty});
    size_t used = 0;
    auto live = [&](const Slot& s) { return s.gate != kEmpty && gates[s.gate].size && gates[s.gate].hash == s.hash; };
    auto insert = [&](uint64_t h, uint32_t g) {
      if (2 * (used + 1) > table.size()) {
        std::vector<Slot> old;
        old.swap(table);
        table.assign(2 * old.size(), Slot{0, kEmpty});
        used = 0;
        for (const Slot& s : old) {
          if (!live(s)) continue;
          size_t i = mix(s.hash) & (table.size() - 1);
          while (table[i].gate != kEmpty) i = (i + 1) & (table.size() - 1);
          table[i] = s;
          ++used;
        }
        budget += old.size() / 4;
      }
      size_t i = mix(h) & (table.size() - 1);
      while (table[i].gate != kEmpty) i = (i + 1) & (table.size() - 1);
      table[i] = Slot{h, g};
      ++used;
    };
    for (size_t head = 0; head < queue.size() && !stop_requested(); ++head) {
      const uint32_t g = queue[head];
      Gate& G = gates[g];
      if (!G.size) continue;  // dropped
      // Normalize.
      Lit* in = inputs.data() + G.begin;
      uint32_t n = 0;
      bool drop = false;
      const Var out = var_of(find(G.lhs));
      budget += G.size / 4 + 1;
      if (G.kind == kAnd) {
        for (uint32_t k = 0; k < G.size; ++k) in[k] = find(in[k]);
        if (G.size <= 16) {
          small_sort(in, G.size);
        } else {
          std::sort(in, in + G.size);
        }
        for (uint32_t k = 0; k < G.size; ++k) {
          if (n && in[n - 1] == in[k]) continue;
          if ((n && in[n - 1] == negate(in[k])) || var_of(in[k]) == out) drop = true;
          in[n++] = in[k];
        }
        if (drop || n == 1) {
          G.size = 0;
          if (!drop && merge(G.lhs, in[0])) ++found;
          continue;
        }
      } else if (G.kind == kXor) {
        // Representatives with their signs moved into the output; a variable twice (x + x = 0)
        // would need a longer case split: such gates are dropped.
        for (uint32_t k = 0; k < G.size; ++k) {
          const Lit r = find(in[k]);
          G.flip ^= static_cast<uint8_t>(r & 1u);
          in[k] = r & ~1u;
        }
        if (G.size <= 16) {
          small_sort(in, G.size);
        } else {
          std::sort(in, in + G.size);
        }
        n = G.size;
        for (uint32_t k = 0; k < n; ++k) {
          if ((k && in[k - 1] == in[k]) || var_of(in[k]) == out) drop = true;
        }
        if (drop) {
          G.size = 0;
          continue;
        }
      } else {  // ITE: c positive (else swap t and e), t positive (else negate t, e and the output)
        Lit c = find(in[0]), t = find(in[1]), e = find(in[2]);
        if (is_negative(c)) {
          c = negate(c);
          std::swap(t, e);
        }
        if (is_negative(t)) {
          t = negate(t);
          e = negate(e);
          G.flip ^= 1u;
        }
        in[0] = c;
        in[1] = t;
        in[2] = e;
        n = 3;
        if (var_of(c) == out || var_of(t) == out || var_of(e) == out || var_of(c) == var_of(t) ||
            var_of(c) == var_of(e) || t == negate(e)) {
          G.size = 0;
          continue;
        }
        if (t == e) {  // o = ITE(c, t, t) = t
          G.size = 0;
          if (merge(G.lhs ^ G.flip, t)) ++found;
          continue;
        }
      }
      G.size = n;
      uint64_t h = (0x9E3779B97F4A7C15ull + G.kind) * n;
      for (uint32_t k = 0; k < n; ++k) h = (h ^ in[k]) * 0x100000001B3ull;
      G.hash = h;
      // Look up a live gate with the same inputs.
      bool present = false;
      uint32_t partner = kEmpty;
      for (size_t i = mix(h) & (table.size() - 1); table[i].gate != kEmpty; i = (i + 1) & (table.size() - 1)) {
        const Slot& s = table[i];
        ++budget;
        if (s.hash != h || !live(s)) continue;
        if (s.gate == g) {
          present = true;
          continue;
        }
        const Gate& H = gates[s.gate];
        if (H.kind == G.kind && H.size == n && std::equal(in, in + n, inputs.data() + H.begin)) {
          partner = s.gate;
          break;
        }
      }
      if (partner != kEmpty) {
        const Gate& H = gates[partner];
        if (merge(G.lhs ^ G.flip, H.lhs ^ H.flip, G.kind == kAnd ? nullptr : &G)) {
          ++found;
          if (G.kind == kXor) ++stats_.congruent_xors;
          if (G.kind == kIte) ++stats_.congruent_ites;
        }
      } else if (!present) {
        insert(h, g);
      }
    }
    std::vector<Gate>().swap(gates);
    std::vector<Lit>().swap(inputs);
    if (!joined) {
      found += congruent_xors(budget);
      found += congruent_ites(budget);
    }
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
void Solver::extract_xor_constraints(std::vector<CongruenceXor>& xors, uint64_t& budget) {
  xors.clear();
  if (stop_requested()) return;
  struct Row {
    Var vars[5];
    uint8_t n, mask;
  };
  // A clause of size n can only be part of an XOR if 2^(n-1) clauses share its variable set: a
  // first pass counts variable sets (hashed, in a CountFilter), the second keeps rows only for
  // sets that occur often enough (a row for every clause of size 3..5 cost hundreds of MB on
  // large formulas, sorting hashes of all of them seconds).
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
  size_t candidates = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant && c.size >= 3 && c.size <= 5) ++candidates;
  }
  if (candidates < 4) return;
  CountFilter filter(candidates);
  // In blocks: the filter slots of a block are prefetched, then added to / counted in order.
  Row block[kFilterBlock];
  uint64_t hashes[kFilterBlock];
  size_t nb = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size < 3 || c.size > 5) continue;
    Row r;
    if (!make_row(c, r)) continue;
    hashes[nb] = set_hash(r);
    filter.prefetch(hashes[nb]);
    if (++nb == kFilterBlock) {
      for (size_t k = 0; k < nb; ++k) filter.add(hashes[k]);
      nb = 0;
      if (stop_requested()) return;
    }
  }
  for (size_t k = 0; k < nb; ++k) filter.add(hashes[k]);
  nb = 0;
  budget += candidates + filter.size() / 64;
  std::vector<Row> rows;
  auto keep_block = [&]() {
    for (size_t k = 0; k < nb; ++k) {
      if (filter.count(hashes[k]) >= (1u << (block[k].n - 1))) rows.push_back(block[k]);
    }
    nb = 0;
  };
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size < 3 || c.size > 5) continue;
    if (!make_row(c, block[nb])) continue;
    hashes[nb] = set_hash(block[nb]);
    filter.prefetch(hashes[nb]);
    if (++nb == kFilterBlock) {
      keep_block();
      if (stop_requested()) return;
    }
  }
  keep_block();
  budget += candidates;
  budget += rows.size();
  std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
    if (a.n != b.n) return a.n < b.n;
    for (int k = 0; k < a.n; ++k) {
      if (a.vars[k] != b.vars[k]) return a.vars[k] < b.vars[k];
    }
    return a.mask < b.mask;
  });
  // XOR constraints: variables + parity of the sum (= 1 - parity of the negative-literal count).
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
      CongruenceXor x{};
      x.n = rows[i].n;
      std::copy(rows[i].vars, rows[i].vars + x.n, x.vars);
      x.parity = static_cast<uint8_t>(1 - q);
      xors.push_back(x);
    }
    i = j;
  }
}

uint32_t Solver::congruent_xors(uint64_t& budget) {
  using Xor = CongruenceXor;
  std::vector<Xor> xors;
  extract_xor_constraints(xors, budget);
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
  for (size_t i = 0; i < outs.size() && !stop_requested();) {
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
void Solver::extract_ites(std::vector<CongruenceIte>& gates, uint64_t& budget) {
  gates.clear();
  if (stop_requested()) return;
  // Live irredundant ternary clauses without assigned literals: a sorted set of sorted triples,
  // and their occurrence lists (CSR).
  // The four clauses of an ITE gate all contain the condition and the output variable: only
  // ternary clauses with a pair of variables in at least four of them are kept (CountFilter).
  using Triple = std::array<Lit, 3>;
  auto live_triple = [&](const Clause& c, Triple& t) {
    if (c.garbage || c.redundant || c.size != 3) return false;
    t = Triple{c.lits()[0], c.lits()[1], c.lits()[2]};
    return !vals_[t[0]] && !vals_[t[1]] && !vals_[t[2]];
  };
  auto pair_key = [](Lit a, Lit b) {
    const Var x = var_of(a), y = var_of(b);
    return x < y ? (uint64_t{x} << 32) | y : (uint64_t{y} << 32) | x;
  };
  size_t ternary = 0;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (!c.garbage && !c.redundant && c.size == 3) ++ternary;
  }
  if (ternary < 8) return;
  CountFilter pairs(3 * ternary);
  // In blocks: the filter slots of a block are prefetched, then added to / counted in order.
  Triple block[kFilterBlock];
  uint64_t keys[3 * kFilterBlock];
  size_t nb = 0;
  auto block_keys = [&](const Triple& t) {
    keys[3 * nb] = pair_key(t[0], t[1]);
    keys[3 * nb + 1] = pair_key(t[0], t[2]);
    keys[3 * nb + 2] = pair_key(t[1], t[2]);
    for (size_t k = 3 * nb; k < 3 * nb + 3; ++k) pairs.prefetch(keys[k]);
  };
  for (const uint32_t ref : clauses_) {
    Triple t;
    if (!live_triple(clause(ref), t)) continue;
    block_keys(t);
    if (++nb == kFilterBlock) {
      for (size_t k = 0; k < 3 * nb; ++k) pairs.add(keys[k]);
      nb = 0;
      if (stop_requested()) return;
    }
  }
  for (size_t k = 0; k < 3 * nb; ++k) pairs.add(keys[k]);
  nb = 0;
  budget += 2 * ternary + pairs.size() / 64;
  std::vector<Triple> tri;
  auto keep_block = [&]() {
    for (size_t k = 0; k < nb; ++k) {
      if (pairs.count(keys[3 * k]) < 4 && pairs.count(keys[3 * k + 1]) < 4 && pairs.count(keys[3 * k + 2]) < 4) continue;
      small_sort(block[k].data(), 3);
      tri.push_back(block[k]);
    }
    nb = 0;
  };
  for (const uint32_t ref : clauses_) {
    if (!live_triple(clause(ref), block[nb])) continue;
    block_keys(block[nb]);
    if (++nb == kFilterBlock) {
      keep_block();
      if (stop_requested()) return;
    }
  }
  keep_block();
  if (tri.size() < 8) return;
  std::sort(tri.begin(), tri.end());
  tri.erase(std::unique(tri.begin(), tri.end()), tri.end());
  budget += tri.size();
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
  // Membership in the (sorted, unique) triples: a triple with a, b and d is in the occurrence
  // list of each of them, so the shortest of the three lists is scanned (a binary search over
  // millions of triples missed the cache at every step).
  auto has = [&](Lit a, Lit b, Lit d) {
    Triple t{a, b, d};
    small_sort(t.data(), 3);
    Lit x = a;
    if (start[b + 1] - start[b] < start[x + 1] - start[x]) x = b;
    if (start[d + 1] - start[d] < start[x + 1] - start[x]) x = d;
    for (uint32_t o = start[x]; o < start[x + 1]; ++o) {
      if (tri[occ[o]] == t) return true;
    }
    return false;
  };
  using Ite = CongruenceIte;
  constexpr uint32_t kMaxOcc = 32;  // pairs per literal are quadratic: skip very frequent ones
  for (Lit no = 0; no < nlits; ++no) {  // no = -o: clauses (x y -o)
    const uint32_t b = start[no], n = start[no + 1] - b;
    if (n < 2 || n > kMaxOcc || eliminated_[var_of(no)]) continue;
    if (stop_requested()) break;
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
}

uint32_t Solver::congruent_ites(uint64_t& budget) {
  using Ite = CongruenceIte;
  std::vector<Ite> gates;
  extract_ites(gates, budget);
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

// Ternary clause pairs (a b c) (a b -c): their resolvent (a b) subsumes both, and every other
// ternary clause (a b x). Substituting equivalent variables into XOR encodings leaves many such
// pairs (x ^ y ^ a ^ b with x = y becomes a = b, as ternary clauses over x, a and b); the
// binaries then complete AND gates and equivalences for the closure. Each ternary clause gives
// three entries (pair of the other two literals, pivot), sorted so that the clauses of a pair are
// adjacent. Runs inside an elimination round (long watches detached); returns the binaries added.
uint32_t Solver::ternary_binaries(uint64_t& budget) {
  struct Entry {
    uint64_t key;  // pair (a < b), then the pivot variable
    Lit pivot;
    uint32_t ref;
  };
  std::vector<Entry> entries;
  for (const uint32_t ref : clauses_) {
    const Clause& c = clause(ref);
    if (c.garbage || c.redundant || c.size != 3) continue;
    const Lit* l = c.lits();
    if (vals_[l[0]] || vals_[l[1]] || vals_[l[2]]) continue;
    for (int k = 0; k < 3; ++k) {
      Lit a = l[(k + 1) % 3], b = l[(k + 2) % 3];
      if (a > b) std::swap(a, b);
      entries.push_back(Entry{(uint64_t{a} << 32 | b), l[k], ref});
    }
  }
  budget += entries.size();
  if (entries.size() < 6 || stop_requested()) return 0;
  std::sort(entries.begin(), entries.end(), [](const Entry& x, const Entry& y) {
    return x.key != y.key ? x.key < y.key : x.pivot < y.pivot;
  });
  budget += entries.size() * 4;
  uint32_t added = 0;
  for (size_t i = 0; i < entries.size();) {
    size_t j = i + 1;
    while (j < entries.size() && entries[j].key == entries[i].key) ++j;
    bool resolvent = false;
    for (size_t k = i; k + 1 < j && !resolvent; ++k) {
      // Sorted by pivot literal: a variable's two literals are adjacent (2v, 2v + 1).
      resolvent = entries[k + 1].pivot == (entries[k].pivot ^ 1u) && (entries[k].pivot & 1u) == 0;
    }
    if (resolvent) {
      const Lit a = static_cast<Lit>(entries[i].key >> 32), b = static_cast<Lit>(entries[i].key & 0xffffffffu);
      bool present = false;
      for (const Watch& w : watches_[a]) {
        if (w.binary() && w.blit == b && !w.redundant_binary()) {
          present = true;
          break;
        }
      }
      budget += watches_[a].size() / 4 + 1;
      if (!present) {
        const Lit bin[2] = {a, b};
        if (proof_) proof_->add(bin, 2);
        add_binary(a, b, false);
        touch_var(var_of(a));
        touch_var(var_of(b));
        ++added;
      }
      for (size_t k = i; k < j && opts_.congruencetern == 1; ++k) {
        if (clause(entries[k].ref).garbage) continue;
        delete_irredundant(entries[k].ref);
        ++stats_.tern_subsumed;
      }
    }
    i = j;
  }
  stats_.tern_binaries += added;
  return added;
}

}  // namespace psat
