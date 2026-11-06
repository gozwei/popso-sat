// Detection of cardinality constraints in the clause database, for the cardinality study
// (--cardinality). Statistics only: nothing found is used by the search, and the pass reads the
// watch lists and the arena without changing any solver state (watch order, ticks, random state).
//
// 1. At-most-one (AMO) constraints in the pairwise encoding: cliques of the conflict graph, whose
//    vertices are literals and whose edges are the binary clauses (-a v -b), "a and b are not both
//    true". Greedy and edge-covering: every binary clause not yet inside a clique seeds one, grown
//    from the common neighbours of its two literals in the order of their degree inside that
//    common neighbourhood (a sudoku cell is in four cliques; ordering by the inner degree keeps a
//    row seed from drifting into the box). Cliques may overlap, each has an edge of its own.
// 2. Exactly-one (EO) constraints: long clauses whose literals are pairwise exclusive. Either
//    directly (every pair is a binary clause: the clause is a clique) or through paths of binary
//    implications: the ladder / sequential, commander, product and bitwise AMO encodings use
//    auxiliary variables, but only binary clauses.
// 3. At-most-k over auxiliary encodings (sequential counter, totalizer): the inputs of a counter
//    reach its "at least one" output through binary implications, so a sink of the binary
//    implication graph with two or more predecessors is a candidate output and the sources of its
//    backward closure the candidate inputs. Unit propagation (an own counter-based propagator on
//    the irredundant clauses) finds k: inputs are set true one by one until the other inputs are
//    forced false; random k-subsets confirm it. Inputs that are themselves implied by binary
//    clauses (gate outputs) hide the counter: the count is a lower bound.

#include <algorithm>
#include <cstdio>
#include <deque>
#include <map>
#include <memory>
#include <string>
#include <unordered_set>

#include "psat/solver/solver.hpp"

namespace psat {

namespace {

struct LongRef {
  const Lit* lits;
  uint32_t size;
};

// "size:count" for the most frequent sizes (at most four), then the largest size.
std::string size_summary(const std::vector<uint32_t>& sizes) {
  if (sizes.empty()) return "-";
  std::map<uint32_t, uint64_t> hist;
  for (const uint32_t s : sizes) ++hist[s];
  std::vector<std::pair<uint64_t, uint32_t>> byc;
  for (const auto& [s, c] : hist) byc.emplace_back(c, s);
  std::sort(byc.begin(), byc.end(), [](const auto& a, const auto& b) { return a.first != b.first ? a.first > b.first : a.second < b.second; });
  std::string out;
  for (size_t i = 0; i < byc.size() && i < 4; ++i) {
    if (!out.empty()) out += ',';
    out += std::to_string(byc[i].second) + ":" + std::to_string(byc[i].first);
  }
  if (byc.size() > 4) out += ",..";
  out += " max " + std::to_string(hist.rbegin()->first);
  return out;
}

uint64_t hash_lits(const std::vector<Lit>& lits) {
  uint64_t h = 0x9E3779B97F4A7C15ull ^ lits.size();
  for (const Lit l : lits) {
    h ^= l + 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2);
    h *= 0xBF58476D1CE4E5B9ull;
  }
  return h;
}

class Detector {
 public:
  Detector(uint32_t vars, uint64_t budget, CardinalityStats& st)
      : nl_(2 * size_t{vars}), budget_(budget), st_(st), var_flags_(vars, 0), var_amo_(vars, 0) {}

  // Conflict graph: off_[l] .. off_[l] + deg_[l] in adj_ are the literals that cannot be true
  // together with l (sorted, unique).
  std::vector<uint64_t> off_;
  std::vector<uint32_t> deg_;
  std::vector<Lit> adj_;
  std::vector<LongRef> longs_;  // irredundant clauses of size >= 3 without root-assigned literals

  void finish_graph() {
    for (size_t l = 0; l < nl_; ++l) {
      Lit* b = adj_.data() + off_[l];
      Lit* e = adj_.data() + off_[l + 1];
      std::sort(b, e);
      deg_[l] = static_cast<uint32_t>(std::unique(b, e) - b);
      st_.binaries += deg_[l];
      st_.work += static_cast<uint64_t>(e - b);
    }
    st_.binaries /= 2;
  }

  void cliques();
  void exactly_one();
  void at_most_k(uint64_t max_occurrences);
  // Root-level units of the clauses shortened by root assignments the solver has not propagated
  // yet: propagated here; false on a conflict. The implied literals are root_trail().
  bool root_propagate(const std::vector<Lit>& units);
  const std::vector<Lit>& root_trail() const { return trail_; }

  void coverage() {
    for (size_t v = 0; v < var_flags_.size(); ++v) {
      st_.vars_covered += var_flags_[v] != 0;
      st_.vars_covered4 += (var_flags_[v] & 8) != 0;
      st_.vars_amo2 += var_amo_[v] >= 2;
    }
    st_.clauses_covered = st_.amo_binaries + st_.eo;
  }

 private:
  const Lit* nbr(Lit l) const { return adj_.data() + off_[l]; }
  // Each phase has the whole budget; a phase that runs out sets its bit in st_.incomplete.
  void phase(uint8_t bit) {
    phase_bit_ = bit;
    phase_start_ = st_.work;
  }
  bool over() {
    if (st_.work - phase_start_ <= budget_) return false;
    st_.incomplete |= phase_bit_;
    return true;
  }
  size_t edge(Lit a, Lit b) const {
    const Lit* n = nbr(a);
    return off_[a] + static_cast<size_t>(std::lower_bound(n, n + deg_[a], b) - n);
  }
  void cover(const std::vector<Lit>& lits, uint8_t flag) {
    if (lits.size() >= 4) flag |= 8;
    for (const Lit l : lits) var_flags_[var_of(l)] |= flag;
  }
  uint64_t next_random() {
    rng_ ^= rng_ << 13;
    rng_ ^= rng_ >> 7;
    rng_ ^= rng_ << 17;
    return rng_;
  }

  // Unit propagation for at_most_k (counts of false literals per long clause).
  bool build_occurrences(uint64_t max_occurrences);
  bool bcp_assign(Lit t, uint64_t limit);
  void bcp_undo(size_t to);

  size_t nl_;
  uint64_t budget_;
  uint64_t phase_start_ = 0;
  uint8_t phase_bit_ = 0;
  CardinalityStats& st_;
  std::vector<uint8_t> var_flags_;  // 1 AMO, 2 EO, 4 AMK input, 8 in one of >= 4 literals
  std::vector<uint8_t> var_amo_;    // cliques per variable (saturating)
  std::vector<uint8_t> cov_;        // per adj_ entry: 1 seen as a 2-clique, 2 inside a clique of >= 3
  std::unordered_set<uint64_t> clique_hashes_;
  uint64_t rng_ = 0x2545F4914F6CDD1Dull;
  // Propagation state.
  std::vector<uint64_t> occ_off_;
  std::vector<uint32_t> occ_;
  std::vector<uint32_t> false_count_;
  std::vector<int8_t> val_;
  std::vector<Lit> trail_;
  size_t propagated_ = 0;
};

void Detector::cliques() {
  phase(1);
  std::vector<Lit> order;
  for (Lit l = 0; l < nl_; ++l) {
    if (deg_[l] >= 2) order.push_back(l);
  }
  std::sort(order.begin(), order.end(), [&](Lit a, Lit b) { return deg_[a] != deg_[b] ? deg_[a] > deg_[b] : a < b; });
  cov_.assign(adj_.size(), 0);
  std::vector<uint32_t> xstamp(nl_, 0), hits(nl_, 0);
  std::vector<uint8_t> incand(nl_, 0);
  std::vector<Lit> cand, clique;
  std::vector<std::pair<uint32_t, Lit>> scored;
  uint32_t stamp = 0;
  for (const Lit x : order) {
    if (over()) return;
    ++stamp;
    const Lit* nx = nbr(x);
    for (uint32_t i = 0; i < deg_[x]; ++i) xstamp[nx[i]] = stamp;
    st_.work += deg_[x];
    for (uint32_t i = 0; i < deg_[x]; ++i) {
      if (cov_[off_[x] + i]) continue;
      if (over()) return;
      const Lit y = nx[i];
      // Candidates: the common neighbours of x and y.
      cand.clear();
      const Lit* ny = nbr(y);
      for (uint32_t j = 0; j < deg_[y]; ++j) {
        if (xstamp[ny[j]] == stamp) cand.push_back(ny[j]);
      }
      st_.work += deg_[y];
      clique.assign({x, y});
      if (!cand.empty()) {
        for (const Lit z : cand) incand[z] = 1;
        scored.clear();
        for (const Lit z : cand) {
          uint32_t s = 0;
          const Lit* nz = nbr(z);
          for (uint32_t j = 0; j < deg_[z]; ++j) s += incand[nz[j]];
          st_.work += deg_[z];
          scored.emplace_back(s, z);
        }
        std::sort(scored.begin(), scored.end(),
                  [](const auto& a, const auto& b) { return a.first != b.first ? a.first > b.first : a.second < b.second; });
        // hits[z]: members added after x and y that z is adjacent to; z joins if adjacent to all.
        uint32_t added = 0;
        for (const auto& sz : scored) {
          const Lit z = sz.second;
          if (hits[z] != added) continue;
          clique.push_back(z);
          ++added;
          const Lit* nz = nbr(z);
          for (uint32_t j = 0; j < deg_[z]; ++j) hits[nz[j]] += incand[nz[j]];
          st_.work += deg_[z];
        }
        for (const Lit z : cand) incand[z] = hits[z] = 0;
      }
      const uint8_t mark = clique.size() >= 3 ? 2 : 1;
      for (size_t a = 0; a < clique.size(); ++a) {
        for (size_t b = 0; b < clique.size(); ++b) {
          if (a == b) continue;
          uint8_t& c = cov_[edge(clique[a], clique[b])];
          if (mark == 2 && c != 2 && clique[a] < clique[b]) ++st_.amo_binaries;
          c = std::max(c, mark);
        }
      }
      st_.work += clique.size() * clique.size() * 4;
      if (mark != 2) continue;
      std::sort(clique.begin(), clique.end());
      ++st_.amo;
      st_.amo_lits += clique.size();
      st_.amo_sizes.push_back(static_cast<uint32_t>(clique.size()));
      size_t neg = 0;
      for (const Lit l : clique) {
        neg += is_negative(l);
        uint8_t& m = var_amo_[var_of(l)];
        if (m < 255) ++m;
      }
      if (neg == 0) {
        ++st_.amo_pos;
      } else if (neg == clique.size()) {
        ++st_.amo_neg;
      } else {
        ++st_.amo_mixed;
      }
      cover(clique, 1);
      clique_hashes_.insert(hash_lits(clique));
    }
  }
}

void Detector::exactly_one() {
  phase(2);
  std::vector<uint32_t> cstamp(nl_, 0), bmark(nl_, 0);
  uint32_t stamp = 0, bstamp = 0;
  std::vector<Lit> c, queue;
  for (const LongRef& r : longs_) {
    if (over()) return;
    const uint32_t k = r.size;
    ++st_.long_clauses;
    bool clique = true;
    for (uint32_t i = 0; i < k && clique; ++i) clique = deg_[r.lits[i]] + 1 >= k;
    ++stamp;
    for (uint32_t i = 0; i < k; ++i) cstamp[r.lits[i]] = stamp;
    st_.work += k;
    for (uint32_t i = 0; i < k && clique; ++i) {
      const Lit x = r.lits[i];
      uint32_t in = 0;
      const Lit* nx = nbr(x);
      for (uint32_t j = 0; j < deg_[x]; ++j) in += cstamp[nx[j]] == stamp;
      st_.work += deg_[x];
      clique = in + 1 == k;
    }
    bool big = false;
    if (!clique && k <= 4096) {
      // Pairwise exclusion through binary implications: from x (true), u in the conflict list of
      // a reached literal t makes -u true. Every other clause literal must be reached negated.
      big = true;
      for (uint32_t i = 0; i < k && big; ++i) {
        const Lit x = r.lits[i];
        if (!deg_[x]) {
          big = false;
          break;
        }
        ++bstamp;
        queue.assign(1, x);
        bmark[x] = bstamp;
        uint32_t found = 0;
        const size_t cap = 16 * size_t{k} + 1024;
        for (size_t q = 0; q < queue.size() && found + 1 < k; ++q) {
          const Lit t = queue[q];
          const Lit* nt = nbr(t);
          for (uint32_t j = 0; j < deg_[t]; ++j) {
            const Lit u = nt[j], s = negate(u);
            if (bmark[s] == bstamp) continue;
            bmark[s] = bstamp;
            if (cstamp[u] == stamp && u != x) ++found;
            if (queue.size() < cap) queue.push_back(s);
          }
          st_.work += deg_[t] + 1;
        }
        big = found + 1 >= k;
      }
    }
    if (!clique && !big) continue;
    c.assign(r.lits, r.lits + k);
    std::sort(c.begin(), c.end());
    ++st_.eo;
    st_.eo_lits += k;
    st_.eo_sizes.push_back(k);
    if (clique) {
      ++st_.eo_clique;
      st_.eo_exact += clique_hashes_.count(hash_lits(c)) != 0;
    } else {
      ++st_.eo_big;
    }
    cover(c, 2);
  }
}

bool Detector::bcp_assign(Lit t, uint64_t limit) {
  if (val_[t] > 0) return true;
  if (val_[t] < 0) return false;
  val_[t] = 1;
  val_[negate(t)] = -1;
  trail_.push_back(t);
  const uint64_t start = st_.work;
  while (propagated_ < trail_.size()) {
    if (st_.work - start > limit) return false;
    // Long clauses with -p are counted first: undoing a propagated literal uncounts all of them.
    const Lit p = trail_[propagated_];
    const Lit f = negate(p);
    const uint64_t b = occ_off_[f], e = occ_off_[f + 1];
    for (uint64_t i = b; i < e; ++i) ++false_count_[occ_[i]];
    ++propagated_;
    st_.work += deg_[p] + (e - b) + 1;
    // Binary clauses: the conflict-graph neighbours of p become false.
    const Lit* np = nbr(p);
    for (uint32_t j = 0; j < deg_[p]; ++j) {
      const Lit u = np[j];
      if (val_[u] > 0) return false;
      if (val_[u] == 0) {
        val_[u] = -1;
        val_[negate(u)] = 1;
        trail_.push_back(negate(u));
      }
    }
    for (uint64_t i = b; i < e; ++i) {
      const uint32_t ci = occ_[i];
      const LongRef& r = longs_[ci];
      if (false_count_[ci] + 1 < r.size) continue;
      Lit unit = kNoLit;
      bool sat = false;
      for (uint32_t k = 0; k < r.size; ++k) {
        const int8_t v = val_[r.lits[k]];
        if (v > 0) {
          sat = true;
          break;
        }
        if (v == 0) unit = r.lits[k];
      }
      st_.work += r.size;
      if (sat) continue;
      if (unit == kNoLit) return false;
      val_[unit] = 1;
      val_[negate(unit)] = -1;
      trail_.push_back(unit);
    }
  }
  return true;
}

void Detector::bcp_undo(size_t to) {
  for (size_t i = trail_.size(); i-- > to;) {
    const Lit t = trail_[i];
    if (i < propagated_) {
      const Lit f = negate(t);
      for (uint64_t j = occ_off_[f]; j < occ_off_[f + 1]; ++j) --false_count_[occ_[j]];
    }
    val_[t] = val_[negate(t)] = 0;
  }
  trail_.resize(to);
  propagated_ = to;
}

bool Detector::build_occurrences(uint64_t max_occurrences) {
  if (!occ_off_.empty()) return true;
  occ_off_.assign(nl_ + 1, 0);
  for (const LongRef& r : longs_) {
    for (uint32_t k = 0; k < r.size; ++k) ++occ_off_[r.lits[k] + 1];
  }
  for (size_t l = 0; l < nl_; ++l) occ_off_[l + 1] += occ_off_[l];
  if (occ_off_[nl_] > max_occurrences) {
    st_.incomplete |= 8;
    return false;
  }
  occ_.resize(occ_off_[nl_]);
  std::vector<uint64_t> pos(occ_off_.begin(), occ_off_.end() - 1);
  for (size_t ci = 0; ci < longs_.size(); ++ci) {
    for (uint32_t k = 0; k < longs_[ci].size; ++k) occ_[pos[longs_[ci].lits[k]]++] = static_cast<uint32_t>(ci);
  }
  st_.work += occ_.size();
  false_count_.assign(longs_.size(), 0);
  val_.assign(nl_, 0);
  return true;
}

bool Detector::root_propagate(const std::vector<Lit>& units) {
  if (!build_occurrences(UINT64_MAX)) return false;
  for (const Lit u : units) {
    if (!bcp_assign(u, UINT64_MAX)) return false;
  }
  return true;
}

void Detector::at_most_k(uint64_t max_occurrences) {
  phase(4);
  if (!build_occurrences(max_occurrences)) return;
  constexpr size_t kMaxClosure = 8192;
  constexpr uint64_t kBcpLimit = 2'000'000;
  std::vector<uint32_t> bmark(nl_, 0);
  uint32_t bstamp = 0;
  std::vector<Lit> closure, sources, order;
  std::vector<Var> inner_vars;
  std::unordered_set<uint64_t> seen;
  constexpr size_t kMaxCandidateLits = 20'000'000;
  std::vector<Lit> cand_lits;
  std::vector<size_t> cand_ends;
  for (Lit o = 0; o < nl_; ++o) {
    if (over()) return;
    // Sinks with two or more predecessors (predecessors of t: the conflict list of -t).
    if (deg_[o] != 0 || deg_[negate(o)] < 2) continue;
    ++bstamp;
    closure.assign(1, o);
    bmark[o] = bstamp;
    bool too_big = false;
    for (size_t q = 0; q < closure.size() && !too_big; ++q) {
      const Lit t = closure[q];
      const Lit* pt = nbr(negate(t));
      for (uint32_t j = 0; j < deg_[negate(t)]; ++j) {
        if (bmark[pt[j]] == bstamp) continue;
        bmark[pt[j]] = bstamp;
        closure.push_back(pt[j]);
        if (closure.size() > kMaxClosure) {
          too_big = true;
          break;
        }
      }
      st_.work += deg_[negate(t)] + 1;
    }
    if (too_big) continue;
    sources.clear();
    inner_vars.clear();
    for (const Lit t : closure) {
      if (deg_[negate(t)] == 0) {
        sources.push_back(t);
      } else {
        inner_vars.push_back(var_of(t));
      }
    }
    std::sort(inner_vars.begin(), inner_vars.end());
    inner_vars.erase(std::unique(inner_vars.begin(), inner_vars.end()), inner_vars.end());
    // A pairwise clique gives sinks too (-y, with the clique as its predecessors) but no inner
    // auxiliary variables.
    if (sources.size() < 3 || inner_vars.size() < 2) continue;
    std::sort(sources.begin(), sources.end());
    bool overlap = false;
    for (const Lit s : sources) overlap |= std::binary_search(inner_vars.begin(), inner_vars.end(), var_of(s));
    if (overlap || !seen.insert(hash_lits(sources)).second) continue;
    cand_lits.insert(cand_lits.end(), sources.begin(), sources.end());
    cand_ends.push_back(cand_lits.size());
    if (cand_lits.size() > kMaxCandidateLits) break;
  }
  // Largest candidates first; a candidate whose inputs all belong to accepted constraints is a
  // sub-counter (or a partial view) of one of them.
  std::vector<size_t> by_size(cand_ends.size());
  for (size_t i = 0; i < by_size.size(); ++i) by_size[i] = i;
  auto cand_begin = [&](size_t i) { return i ? cand_ends[i - 1] : size_t{0}; };
  std::stable_sort(by_size.begin(), by_size.end(), [&](size_t a, size_t b) {
    return cand_ends[a] - cand_begin(a) > cand_ends[b] - cand_begin(b);
  });
  std::vector<uint8_t> in_amk(nl_, 0);
  for (const size_t ci : by_size) {
    if (over()) return;
    sources.assign(cand_lits.begin() + static_cast<std::ptrdiff_t>(cand_begin(ci)),
                   cand_lits.begin() + static_cast<std::ptrdiff_t>(cand_ends[ci]));
    bool fresh = false;
    for (const Lit l : sources) fresh |= !in_amk[l];
    if (!fresh) continue;
    ++st_.amk_candidates;
    // k: inputs true one by one (random order) until the other inputs are forced false.
    order = sources;
    for (size_t i = order.size(); i > 1; --i) std::swap(order[i - 1], order[next_random() % i]);
    uint32_t k = 0;
    bool ok = true;
    for (size_t i = 0; i < order.size(); ++i) {
      if (val_[order[i]] != 0 || !bcp_assign(order[i], kBcpLimit)) {
        ok = false;
        break;
      }
      ++k;
      size_t falsified = 0;
      for (const Lit l : sources) falsified += val_[l] < 0;
      if (falsified) {
        ok = falsified + k == sources.size();
        break;
      }
    }
    if (k == sources.size()) ok = false;  // never bounded
    bcp_undo(0);
    // Confirmation with random k-subsets.
    for (int round = 0; ok && round < 3; ++round) {
      order = sources;
      for (size_t i = order.size(); i > 1; --i) std::swap(order[i - 1], order[next_random() % i]);
      for (uint32_t i = 0; i < k && ok; ++i) ok = val_[order[i]] == 0 && bcp_assign(order[i], kBcpLimit);
      for (size_t i = k; i < order.size() && ok; ++i) ok = val_[order[i]] < 0;
      bcp_undo(0);
    }
    if (!ok) continue;
    cover(sources, 4);
    // Mostly inputs of an accepted constraint: another view of the same counter (a different
    // output reaches a different subset of its inputs).
    size_t known = 0;
    for (const Lit l : sources) known += in_amk[l];
    for (const Lit l : sources) in_amk[l] = 1;
    if (2 * known >= sources.size()) {
      ++st_.amk_merged;
      continue;
    }
    ++st_.amk;
    st_.amk_lits += sources.size();
    st_.amk_sizes.emplace_back(static_cast<uint32_t>(sources.size()), k);
  }
}

}  // namespace

void Solver::detect_cardinality(const char* when) {
  if (inconsistent_ || level() != 0) return;
  const auto t0 = std::chrono::steady_clock::now();
  const uint64_t budget = static_cast<uint64_t>(opts_.cardinalityeffort) * 1'000'000;
  const size_t nl = 2 * size_t{num_vars_};
  // Root values: the solver's, plus what unit propagation of the clauses they shorten implies
  // (detection can run before the solver has propagated the input units). A second build when
  // the first one finds new root literals.
  std::vector<int8_t> root(vals_.begin(), vals_.end());
  CardinalityStats st;
  std::unique_ptr<Detector> d;
  std::deque<std::vector<Lit>> copies;
  uint64_t work = 0;
  for (int build = 0;; ++build) {
    st = CardinalityStats();
    st.work = work;
    d = std::make_unique<Detector>(num_vars_, budget, st);
    copies.clear();
    std::vector<Lit> units, extra;  // extra: binary clauses shortened from long ones (pairs)
    bool conflict = false;
    // Long irredundant clauses: satisfied ones skipped, root-falsified literals dropped (copies).
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || c.redundant) continue;
      bool sat = false, dirty = false;
      for (uint32_t k = 0; k < c.size; ++k) {
        const int8_t v = root[c.lits()[k]];
        sat |= v > 0;
        dirty |= v < 0;
      }
      st.work += c.size / 4 + 1;
      if (sat) continue;
      if (!dirty) {
        d->longs_.push_back(LongRef{c.lits(), c.size});
        continue;
      }
      std::vector<Lit> lits;
      for (uint32_t k = 0; k < c.size; ++k) {
        if (!root[c.lits()[k]]) lits.push_back(c.lits()[k]);
      }
      if (lits.empty()) {
        conflict = true;
      } else if (lits.size() == 1) {
        units.push_back(lits[0]);
      } else if (lits.size() == 2) {
        extra.push_back(lits[0]);
        extra.push_back(lits[1]);
      } else {
        copies.push_back(std::move(lits));
        d->longs_.push_back(LongRef{copies.back().data(), static_cast<uint32_t>(copies.back().size())});
      }
    }
    // Conflict graph from the irredundant binary clauses: (a v b) in watches_[a] makes -a and -b
    // exclusive.
    d->off_.assign(nl + 1, 0);
    d->deg_.assign(nl, 0);
    for (Lit l = 0; l < nl; ++l) {
      for (const Watch& w : watches_[l]) {
        if (!w.binary() || w.redundant_binary()) continue;
        const int8_t a = root[l], b = root[w.blit];
        if (a > 0 || b > 0) continue;
        if (a < 0 && b < 0) {
          conflict = true;
        } else if (a < 0) {
          units.push_back(w.blit);
        } else if (!b) {
          ++d->off_[negate(l) + 1];
        }
      }
      st.work += watches_[l].size() / 4 + 1;
    }
    for (size_t i = 0; i < extra.size(); i += 2) {
      ++d->off_[negate(extra[i]) + 1];
      ++d->off_[negate(extra[i + 1]) + 1];
    }
    for (size_t l = 0; l < nl; ++l) d->off_[l + 1] += d->off_[l];
    d->adj_.resize(d->off_[nl]);
    {
      std::vector<uint64_t> pos(d->off_.begin(), d->off_.end() - 1);
      for (Lit l = 0; l < nl; ++l) {
        if (root[l]) continue;
        for (const Watch& w : watches_[l]) {
          if (w.binary() && !w.redundant_binary() && !root[w.blit]) d->adj_[pos[negate(l)]++] = negate(w.blit);
        }
      }
      for (size_t i = 0; i < extra.size(); i += 2) {
        d->adj_[pos[negate(extra[i])]++] = negate(extra[i + 1]);
        d->adj_[pos[negate(extra[i + 1])]++] = negate(extra[i]);
      }
    }
    d->finish_graph();
    if (!conflict && !units.empty() && build == 0) {
      conflict = !d->root_propagate(units);
      if (!conflict) {
        for (const Lit t : d->root_trail()) {
          root[t] = 1;
          root[negate(t)] = -1;
        }
        work = st.work;
        continue;
      }
    }
    if (conflict) {
      std::printf("c cardinality %s: the root assignment is inconsistent, no detection\n", when);
      return;
    }
    break;
  }
  for (Var v = 0; v < num_vars_; ++v) st.vars_active += !eliminated_[v] && !root[make_lit(v, false)];
  auto lap = [&t0]() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); };
  st.phase_seconds[0] = lap();
  d->cliques();
  st.phase_seconds[1] = lap();
  d->exactly_one();
  st.phase_seconds[2] = lap();
  d->at_most_k(50'000'000);
  st.phase_seconds[3] = lap();
  for (int i = 3; i > 0; --i) st.phase_seconds[i] -= st.phase_seconds[i - 1];
  d->coverage();
  st.seconds = lap();

  std::map<std::pair<uint32_t, uint32_t>, uint64_t> amk_hist;
  for (const auto& p : st.amk_sizes) ++amk_hist[p];
  std::string amk;
  for (const auto& [p, c] : amk_hist) {
    if (amk.size() > 60) {
      amk += ",..";
      break;
    }
    if (!amk.empty()) amk += ',';
    amk += "n" + std::to_string(p.first) + "k" + std::to_string(p.second) + ":" + std::to_string(c);
  }
  if (amk.empty()) amk = "-";
  auto pct = [](uint64_t a, uint64_t b) { return b ? 100.0 * static_cast<double>(a) / static_cast<double>(b) : 0.0; };
  auto ull = [](uint64_t x) { return static_cast<unsigned long long>(x); };
  const uint64_t clauses = st.binaries + st.long_clauses;
  std::string limits;
  if (st.incomplete) {
    limits = " (limit hit:";
    if (st.incomplete & 1) limits += " amo";
    if (st.incomplete & 2) limits += " eo";
    if (st.incomplete & 4) limits += " amk";
    if (st.incomplete & 8) limits += " amk-size";
    limits += ")";
  }
  std::printf(
      "c cardinality %s: amo %llu [%s] lits %llu (pos %llu neg %llu mixed %llu) binaries %llu | eo %llu [%s] "
      "(clique %llu = amo %llu, implied %llu) | amk %llu [%s] merged %llu of %llu candidates | vars %llu of %llu (%.1f%%, "
      "size 4+ %.1f%%, in 2+ amo %llu) "
      "| clauses %llu of %llu (%.1f%%) | work %.1fM%s | %.3f s (build %.3f, amo %.3f, eo %.3f, amk %.3f)\n",
      when, ull(st.amo), size_summary(st.amo_sizes).c_str(), ull(st.amo_lits), ull(st.amo_pos), ull(st.amo_neg),
      ull(st.amo_mixed), ull(st.amo_binaries), ull(st.eo), size_summary(st.eo_sizes).c_str(), ull(st.eo_clique),
      ull(st.eo_exact), ull(st.eo_big), ull(st.amk), amk.c_str(), ull(st.amk_merged), ull(st.amk_candidates),
      ull(st.vars_covered), ull(st.vars_active), pct(st.vars_covered, st.vars_active), pct(st.vars_covered4, st.vars_active),
      ull(st.vars_amo2), ull(st.clauses_covered),
      ull(clauses), pct(st.clauses_covered, clauses), static_cast<double>(st.work) / 1e6,
      limits.c_str(), st.seconds, st.phase_seconds[0], st.phase_seconds[1], st.phase_seconds[2], st.phase_seconds[3]);
  std::fflush(stdout);
  if (card_runs_++ == 0) card_stats_ = std::move(st);
}

}  // namespace psat
