// Learned binary clauses.
//
// Binary clauses live only in the watch lists (two watches each, see watches.hpp), and learned
// ones are never reduced: knight_18 ends a 2400 s run with 470k learned binary clauses next to
// 593k irredundant ones (long1). This file has a census of them (--binstats, statistics only) and
// their transitive reduction (--binreduce).
//
// The binary implication graph (BIG) has an edge u -> v (u true implies v) for every binary clause
// (-u v); it is skew-symmetric (u -> v iff -v -> -u), so a binary clause (a b) is implied by the
// others exactly when b is reachable from -a without it (its two edges): it is "transitive".

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <utility>
#include <vector>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

// --binstats: classifies every learned binary clause, with each progress line (output only; the
// search state is not touched except the "recent" marks of the binary watches, which nothing else
// reads):
// - root: a literal is fixed at the root (satisfied or about to be shortened; root simplification
//   removes it);
// - dup: another copy of the same clause exists (an irredundant one, or an earlier learned one);
// - trans: transitive (above), checked in a fixed order with the clauses found transitive before
//   removed from the graph, so that all of them can go together; breadth-first from -a with at most
//   kNodes literals visited ("limit": the search stopped there undecided); trans2: found at
//   distance 2 (a path -a -> x -> b);
// - failed: -a reaches a (a is a failed literal's negation, so a unit implies the clause);
// - never: never implied a literal or conflicted in propagation since it was learned; idle: not
//   since the last census; by age in censuses (learned in the current interval, 1-3 ago, 4+ ago).
// Then the watches by kind and, since the last census, the watches propagation visited per
// propagated literal (learned binary, irredundant binary, long) and the binary implications.
void Solver::binary_census() {
  const auto t0 = std::chrono::steady_clock::now();
  const size_t nlits = 2 * size_t{num_vars_};
  auto root_fixed = [&](Lit l) { return vals_[l] != 0 && vdata_[var_of(l)].level == 0; };
  constexpr uint32_t kMarks = kBinaryUsed | kBinaryRecent;

  // Clause copies from the side of the smaller literal, with the marks of both sides (the mirror
  // watch of a copy is not known when there are several: the marks are merged per literal pair).
  struct Bin {
    Lit a, b;
    uint32_t ref;
  };
  std::vector<Bin> bins, mirror;
  uint64_t watch_red = 0, watch_irr = 0, watch_long = 0, lists = 0;
  for (Lit a = 0; a < nlits; ++a) {
    const ConstWatchList ws = std::as_const(watches_)[a];
    lists += !ws.empty();
    for (const Watch& w : ws) {
      if (!w.binary()) {
        ++watch_long;
        continue;
      }
      ++(w.redundant_binary() ? watch_red : watch_irr);
      if (a < w.blit) {
        bins.push_back(Bin{a, w.blit, w.ref});
      } else {
        mirror.push_back(Bin{w.blit, a, w.ref});
      }
    }
  }
  auto by_pair = [](const Bin& x, const Bin& y) {
    return x.a != y.a ? x.a < y.a : x.b != y.b ? x.b < y.b : (x.ref & 1u) < (y.ref & 1u);
  };
  std::sort(bins.begin(), bins.end(), by_pair);
  std::sort(mirror.begin(), mirror.end(), by_pair);
  // Distinct pairs (a < b): copies by kind and the merged marks of the learned copies.
  struct Pair {
    Lit a, b;
    uint32_t irr, red;
    uint32_t marks;  // of the learned copies
    uint32_t epoch;  // the latest learned copy's
  };
  std::vector<Pair> pairs;
  size_t m = 0;
  for (size_t i = 0; i < bins.size();) {
    const Lit a = bins[i].a, b = bins[i].b;
    Pair p{a, b, 0, 0, 0, 0};
    for (; i < bins.size() && bins[i].a == a && bins[i].b == b; ++i) {
      if (bins[i].ref & 1u) {
        ++p.red;
        p.marks |= bins[i].ref & kMarks;
        p.epoch = std::max(p.epoch, (bins[i].ref >> kBinaryEpochShift) & kBinaryEpochMask);
      } else {
        ++p.irr;
      }
    }
    while (m < mirror.size() && (mirror[m].a < a || (mirror[m].a == a && mirror[m].b < b))) ++m;
    for (; m < mirror.size() && mirror[m].a == a && mirror[m].b == b; ++m) {
      if (mirror[m].ref & 1u) p.marks |= mirror[m].ref & kMarks;
    }
    pairs.push_back(p);
  }

  uint64_t learned = 0, root = 0, dup = 0;
  for (const Pair& p : pairs) {
    learned += p.red;
    if (!p.red) continue;
    if (root_fixed(p.a) || root_fixed(p.b)) {
      root += p.red;
      continue;
    }
    dup += p.irr ? p.red : p.red - 1;
  }

  // The graph over the pairs without root-fixed literals (CSR by source literal).
  std::vector<uint32_t> start(nlits + 1, 0);
  for (const Pair& p : pairs) {
    if (root_fixed(p.a) || root_fixed(p.b)) continue;
    ++start[negate(p.a) + 1];
    ++start[negate(p.b) + 1];
  }
  for (size_t l = 0; l < nlits; ++l) start[l + 1] += start[l];
  std::vector<Lit> target(start[nlits]);
  std::vector<uint32_t> edge_pair(start[nlits]);
  {
    std::vector<uint32_t> fill(start.begin(), start.end() - 1);
    for (uint32_t k = 0; k < pairs.size(); ++k) {
      const Pair& p = pairs[k];
      if (root_fixed(p.a) || root_fixed(p.b)) continue;
      const uint32_t e1 = fill[negate(p.a)]++, e2 = fill[negate(p.b)]++;
      target[e1] = p.b;
      edge_pair[e1] = k;
      target[e2] = p.a;
      edge_pair[e2] = k;
    }
  }
  constexpr size_t kNodes = 1000;
  std::vector<uint8_t> dead(pairs.size(), 0);
  std::vector<uint32_t> seen(nlits, 0);
  std::vector<Lit> queue;
  uint32_t stamp = 0;
  uint64_t trans = 0, trans2 = 0, failed = 0, limit = 0, never = 0, idle = 0, kept = 0;
  uint64_t never_age[3] = {}, kept_age[3] = {};
  for (uint32_t k = 0; k < pairs.size(); ++k) {
    const Pair& p = pairs[k];
    if (!p.red || p.irr || root_fixed(p.a) || root_fixed(p.b)) continue;
    const Lit from = negate(p.a), to = p.b;
    ++stamp;
    queue.clear();
    queue.push_back(from);
    seen[from] = stamp;
    bool found = false, fails = false, cut = false;
    size_t head = 0, level_end = 1;
    uint32_t depth = 1;  // of the literals queue[head..level_end) plus one
    while (head < queue.size() && !found && !cut) {
      if (head == level_end) {
        level_end = queue.size();
        ++depth;
      }
      const Lit u = queue[head++];
      for (uint32_t e = start[u]; e < start[u + 1]; ++e) {
        const uint32_t q = edge_pair[e];
        if (q == k || dead[q]) continue;
        const Lit v = target[e];
        if (v == to) {
          found = true;
          break;
        }
        if (v == p.a) fails = true;
        if (seen[v] == stamp) continue;
        seen[v] = stamp;
        queue.push_back(v);
        if (queue.size() > kNodes) {
          cut = true;
          break;
        }
      }
    }
    const uint32_t age = bin_census_.epoch - p.epoch;
    const int bucket = age == 0 ? 0 : age < 4 ? 1 : 2;
    if (found) {
      ++trans;
      trans2 += depth == 2;
      dead[k] = 1;
      continue;
    }
    if (fails) ++failed;
    if (cut) ++limit;
    ++kept;
    ++kept_age[bucket];
    if (!(p.marks & kBinaryUsed)) {
      ++never;
      ++never_age[bucket];
    }
    if (!(p.marks & kBinaryRecent)) ++idle;
  }
  // The "recent" marks start over.
  for (Lit a = 0; a < nlits; ++a) {
    for (Watch& w : watches_[a]) {
      if (w.binary()) w.ref &= ~kBinaryRecent;
    }
  }

  BinCensus& s = bin_census_;
  const uint64_t props = stats_.propagations - s.last_props;
  const auto per = [&](uint64_t x, uint64_t last) { return props ? static_cast<double>(x - last) / static_cast<double>(props) : 0.0; };
  auto ull = [](uint64_t x) { return static_cast<unsigned long long>(x); };
  s.seconds += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  std::printf("c [%.2f s] bins census=%u learned=%llu root=%llu dup=%llu trans=%llu trans2=%llu failed=%llu limit=%llu "
              "kept=%llu never=%llu idle=%llu kept_age=%llu/%llu/%llu never_age=%llu/%llu/%llu irrbin=%llu "
              "watches_red=%llu watches_irr=%llu watches_long=%llu lists=%llu "
              "visit_red=%.2f visit_irr=%.2f visit_long=%.2f implied_red=%.3f implied_irr=%.3f census_s=%.2f\n",
              seconds(), s.epoch, ull(learned), ull(root), ull(dup), ull(trans), ull(trans2), ull(failed), ull(limit),
              ull(kept), ull(never), ull(idle), ull(kept_age[0]), ull(kept_age[1]), ull(kept_age[2]), ull(never_age[0]),
              ull(never_age[1]), ull(never_age[2]), ull(binaries_irredundant_), ull(watch_red), ull(watch_irr),
              ull(watch_long), ull(lists), per(s.visit_red, s.last_visit_red), per(s.visit_irr, s.last_visit_irr),
              per(s.visit_long, s.last_visit_long), per(s.implied_red, s.last_implied_red),
              per(s.implied_irr, s.last_implied_irr), s.seconds);
  std::fflush(stdout);
  s.last_visit_red = s.visit_red;
  s.last_visit_irr = s.visit_irr;
  s.last_visit_long = s.visit_long;
  s.last_implied_red = s.implied_red;
  s.last_implied_irr = s.implied_irr;
  s.last_props = stats_.propagations;
  ++s.epoch;
}

// Whether the binary clauses other than one learned copy of (a b) imply it, i.e. whether b is
// reachable from -a in the binary implication graph (edge u -> v for each (-u v) in watches_[-u])
// without the copy's two edges -a -> b and -b -> a, through unassigned literals only (at the root,
// an edge to an assigned literal is a satisfied clause):
// - distance 1 (another copy) and 2 exactly: the successors of -a are marked, then the successors
//   of -b scanned for the negation of a marked literal (-b -> -x is the mirror of x -> b), at the
//   cost of the two lists (knight_18: 89% of the transitive learned binaries are at distance 2,
//   and a breadth-first search from -a passes 100 literals before it finds most of them);
// - farther: breadth-first on from the successors of -a, at most binreducenodes literals.
// Ticks: a cache line per eight watches of each list scanned, as in propagation.
bool Solver::binary_implied(Lit a, Lit b, uint64_t& ticks) {
  std::vector<uint32_t>& seen = binreduce_seen_;
  std::vector<Lit>& queue = binreduce_queue_;
  if (++binreduce_stamp_ == 0) {
    std::fill(seen.begin(), seen.end(), 0);
    binreduce_stamp_ = 1;
  }
  const uint32_t stamp = binreduce_stamp_;
  const Lit from = negate(a), mirror = negate(b);
  const size_t limit = static_cast<size_t>(opts_.binreducenodes);
  // (Other copies of (a b) are edges like any other: the scans skip only one learned copy of each
  // edge. The mirror edge -b -> a is skipped in the distance-2 scan and again in the search.)
  bool skip_direct = true, skip_mirror = true;
  // The successors of -a (distance 1).
  queue.clear();
  seen[from] = stamp;
  {
    const ConstWatchList ws = std::as_const(watches_)[a];
    ticks += 1 + ws.size() / 8;
    for (const Watch& w : ws) {
      if (!w.binary()) continue;
      const Lit v = w.blit;
      if (v == b && skip_direct && w.redundant_binary()) {
        skip_direct = false;
        continue;
      }
      if (vals_[v] != 0) continue;
      if (v == b) return true;
      if (seen[v] == stamp) continue;
      seen[v] = stamp;
      queue.push_back(v);
    }
  }
  // Distance 2: -b -> y with -y a successor of -a (or y = a through another copy of the clause).
  {
    const ConstWatchList ws = std::as_const(watches_)[b];
    ticks += 1 + ws.size() / 8;
    for (const Watch& w : ws) {
      if (!w.binary()) continue;
      const Lit y = w.blit;
      if (y == a && skip_mirror && w.redundant_binary()) {
        skip_mirror = false;
        continue;
      }
      if (vals_[y] == 0 && seen[negate(y)] == stamp) return true;
    }
  }
  // Farther: breadth-first from the successors of -a.
  skip_mirror = true;
  if (queue.size() >= limit) {
    ++stats_.binreduce_cut;
    return false;
  }
  for (size_t head = 0; head < queue.size(); ++head) {
    const Lit u = queue[head];
    const ConstWatchList ws = std::as_const(watches_)[negate(u)];
    ticks += 1 + ws.size() / 8;
    for (const Watch& w : ws) {
      if (!w.binary()) continue;
      const Lit v = w.blit;
      if (u == mirror && v == a && skip_mirror && w.redundant_binary()) {
        skip_mirror = false;
        continue;
      }
      if (vals_[v] != 0) continue;
      if (v == b) return true;
      if (seen[v] == stamp) continue;
      seen[v] = stamp;
      queue.push_back(v);
      if (queue.size() > limit) {
        ++stats_.binreduce_cut;
        return false;
      }
    }
  }
  return false;
}

// --binreduce: transitive reduction of the learned binary clauses, at the root (vivification
// rounds, after root simplification: every binary clause left has two unassigned literals). Each
// learned binary clause (a b), a < b, not checked before, in literal order from where the last
// round stopped, is deleted when the other binary clauses imply it (binary_implied); one that
// stays gets kBinaryChecked on its watch in a's list and is not checked again (a path that later
// binary clauses close is missed; knight_18 with every clause checked again at each round: 28M
// checks for 6.7k deletions). Each check sees the graph without the clauses deleted before it, so
// the deletions never depend on each other, and deleting a learned clause is always sound: the
// proof gets a deletion line. Irredundant binary clauses are kept (unhiding removes transitive
// ones among those, from irredundant paths only).
void Solver::reduce_binaries(uint64_t ticks_limit) {
  const PassTimer pass_timer(*this, kPassBinreduce);
  ++stats_.binreduce_rounds;
  if (!binaries_redundant_ || level() != 0) return;
  const size_t nlits = 2 * size_t{num_vars_};
  if (binreduce_seen_.size() < nlits) binreduce_seen_.resize(nlits, 0);
  uint64_t ticks = 0;
  std::vector<Lit>& cands = binreduce_cands_;
  auto candidate = [&](Lit a, const Watch& w) {
    return w.binary() && w.redundant_binary() && !(w.ref & kBinaryChecked) && a < w.blit && vals_[w.blit] == 0;
  };
  Lit a = binreduce_next_ < nlits ? binreduce_next_ : 0;
  for (size_t done = 0; done < nlits; ++done, ++a) {
    if (a >= nlits) a = 0;
    if (ticks > ticks_limit || stop_requested()) break;
    if (vals_[a] != 0 || eliminated_[var_of(a)]) continue;
    cands.clear();
    {
      const ConstWatchList ws = std::as_const(watches_)[a];
      ticks += 1 + ws.size() / 8;
      for (const Watch& w : ws) {
        if (candidate(a, w)) cands.push_back(w.blit);
      }
    }
    if (cands.empty()) continue;
    for (const Lit b : cands) {
      ++stats_.binreduce_checked;
      if (!binary_implied(a, b, ticks)) continue;
      remove_binary_watch(a, b, true);
      remove_binary_watch(b, a, true);
      if (opts_.invariants) {  // (debugging: -a must still propagate b, or a conflict)
        control_.push_back(static_cast<uint32_t>(trail_.size()));
        assign(negate(a), kNoReason);
        const bool implied = !propagate_vivify(kNoReason) || vals_[b] > 0;
        backtrack(0);
        if (!implied) {
          std::fprintf(stderr, "c DEBUG binreduce deleted a binary clause that is not implied: %d %d\n",
                       to_dimacs(external_lit(a)), to_dimacs(external_lit(b)));
          std::abort();
        }
      }
      if (proof_) {
        const Lit bin[2] = {a, b};
        proof_->del(bin, 2);
      }
      --binaries_redundant_;
      ++stats_.binreduce_deleted;
    }
    for (Watch& w : watches_[a]) {
      if (candidate(a, w)) w.ref |= kBinaryChecked;
    }
  }
  binreduce_next_ = a;
  stats_.binreduce_ticks += ticks;
}

}  // namespace psat
