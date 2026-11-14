// Boolean constraint propagation with two watched literals.
//
// Watch lists are indexed by the watched literal and visited when it becomes false. Long-clause
// watches carry a blocking literal: when it is true the clause is skipped without touching the
// arena. The two watched literals of a long clause are lits[0] and lits[1]; the replacement
// search resumes where the last one ended (Gent, JAIR 2013), which matters for long clauses.

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdio>

#include "psat/solver/solver.hpp"

namespace psat {

// Prefetching the clause of the watch kPrefetchDistance ahead, in watch lists of at least
// kPrefetchList watches, pays where the arena does not fit the caches (M4: constraints_17, 21 MB
// of long clauses, -10% time; scc_9630, -6 to -11%); with smaller arenas it cost up to 3%
// (station-repacking, 6 MB), and without the list length gate 17-40% on ncc and 8% on
// linked_list (millions of variables, short lists, most blockers true). It changes nothing else.
// On the i7-7700K with 4 jobs sharing memory bandwidth (sc2026, 12 instances, two rounds) it cost
// ~20% (+15% against the build before it, where everything else gained ~5%); prefetching only
// where the blocking literal is not true halved that and won on constraints_16/17 but lost on
// post-cbmc and ntil. Hence --prefetch=0 by default.
constexpr std::ptrdiff_t kPrefetchDistance = 4;
constexpr size_t kPrefetchList = 16;
constexpr size_t kPrefetchArenaWords = size_t{1} << 21;  // 8 MB

bool Solver::propagate() {
  if (gauss_on_) return propagate_with_gauss();  // (the detached Gauss-Jordan solver only)
  return propagate_search();
}

bool Solver::propagate_search() {
  if (opts_.propstats) {
    if (opts_.propstats == 2 && !prop_cache_[0].sets) {
      prop_cache_[0].init(size_t{32} << 10, 8);
      prop_cache_[1].init(size_t{256} << 10, 4);
      prop_cache_[2].init(size_t{2} << 20, 16);
      prop_cache_[3].init(size_t{8} << 20, 16);
    }
    const auto t0 = std::chrono::steady_clock::now();
    const bool ok = opts_.propstats == 2 ? propagate_impl<false, false, false, 2>(kNoReason)
                                         : propagate_impl<false, false, false, 1>(kNoReason);
    prop_stats_.nanos += static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now() - t0).count());
    ++prop_stats_.calls;
    return ok;
  }
  const bool prefetch = opts_.prefetch && arena_.size() >= kPrefetchArenaWords;
  if (opts_.binstats) return prefetch ? propagate_impl<false, true, true>(kNoReason) : propagate_impl<false, false, true>(kNoReason);
  return prefetch ? propagate_impl<false, true>(kNoReason) : propagate_impl<false, false>(kNoReason);
}

// Vivification propagates without the clause being vivified, and books its ticks separately from
// search. Both skip garbage clauses (deleted in the proof already) and drop their watches.
//
// With chronological backtracking (search only), an implied literal gets the highest level of the
// other literals of its reason. That is the current level whenever the propagated literal is on
// the current level, so the reason is scanned only while propagating a lower-level literal (kept
// on the trail by a chronological backtrack, or implied out of order).
bool Solver::propagate_vivify(uint32_t ignore) {
  return opts_.prefetch && arena_.size() >= kPrefetchArenaWords ? propagate_impl<true, true>(ignore)
                                                                : propagate_impl<true, false>(ignore);
}

// kStats (--binstats, search only): watches visited by kind and binary implications counted, and
// every binary watch that implies or conflicts marked used (binaries.cpp); the search is the same.
template <bool kVivify, bool kPrefetch, bool kStats, int kProp>
bool Solver::propagate_impl(uint32_t ignore) {
  has_conflict_ = false;
  const size_t start = propagated_;
  uint64_t ticks = 0;
  // Local copies of the arrays' base pointers: the int8_t stores of an assignment may alias any
  // object for the compiler, which would otherwise reload every member pointer after each one.
  // None of these arrays is reallocated during propagation (the trail has room for every
  // variable, see grow_vars()); only the watch pool can move (below).
  int8_t* const vals = vals_.data();
  VarData* const vdata = vdata_.data();
  int8_t* const saved = saved_.data();
  uint32_t* const arena = arena_.data();
  const uint32_t current = level();
  [[maybe_unused]] const bool prefetch_open_only = opts_.prefetch == 2;  // (kPrefetch only)
  size_t propagated = propagated_;
  bool conflict = false;
  [[maybe_unused]] uint64_t visit_red = 0, visit_irr = 0, visit_long = 0, implied_red = 0, implied_irr = 0;
  // The assignment of assign_at(), inlined.
  const auto imply = [&](Lit l, uint32_t reason, uint32_t lvl) {
    const Var v = var_of(l);
    vals[l] = 1;
    vals[negate(l)] = -1;
    VarData& d = vdata[v];
    d.level = lvl;
    d.reason = lvl ? reason : kNoReason;
    d.trail = static_cast<uint32_t>(trail_.size());
    saved[v] = is_negative(l) ? -1 : 1;
    trail_.push_back(l);
    if (!lvl) on_root_fixed(l);
  };
  while (propagated < trail_.size()) {
    const Lit lit = trail_[propagated++];
    const Lit not_lit = negate(lit);
    uint32_t lit_level = current;
    bool lower = false;  // lit is below the current level: implied levels need a scan
    if constexpr (!kVivify) {
      if (opts_.chrono) {
        lit_level = vdata[var_of(lit)].level;
        lower = lit_level < current;
      }
    }
    // The list is a slice of the watch pool: moving a watch to another list can relocate that
    // list and grow (move) the pool, so the pointers are re-derived from the slice's begin index
    // (which only compaction changes) after every such push.
    const size_t list_size = watches_[not_lit].size();
    const uint32_t list_begin = watches_.begin_index(not_lit);
    Watch* begin = watches_.pool() + list_begin;
    Watch* end = begin + list_size;
    Watch* i = begin;
    Watch* j = begin;
    ticks += 1 + (list_size >> 3);
    if constexpr (kProp > 0) {
      ++prop_stats_.lists;
      prop_stats_.list_watches += list_size;
    }
    [[maybe_unused]] auto touch = [&](const void* from, const void* to) {  // (kProp == 2) [from, to)
      const uint64_t a = reinterpret_cast<uintptr_t>(from) >> 6, b = (reinterpret_cast<uintptr_t>(to) - 1) >> 6;
      for (uint64_t line = a; line <= b; ++line) {
        ++prop_stats_.lines;
        for (CacheModel& m : prop_cache_) m.touch(line);
      }
    };
    [[maybe_unused]] const bool long_list = list_size >= kPrefetchList;  // (kPrefetch only)
    while (i != end) {
      // Runs of watches with a true blocking literal (89% of the long-clause watches late on the
      // booth / sbdp4 miters) in tight loops: while no watch has left the list (j == i) they are
      // not even copied. The order and every decision are the same; -1% time on booth29 (M4).
      if constexpr (!kPrefetch && !kStats && kProp == 0) {
        if (j == i) {
          while (vals[i->blit] > 0) {
            if (++i == end) break;
          }
          j = i;
        } else {
          while (vals[i->blit] > 0) {
            *j++ = *i++;
            if (i == end) break;
          }
        }
        if (i == end) break;
      }
      if constexpr (kPrefetch) {
        if (long_list && end - i > kPrefetchDistance) {
          const Watch p = i[kPrefetchDistance];
          if (!p.binary() && (!prefetch_open_only || vals[p.blit] <= 0)) PSAT_PREFETCH(arena + p.ref);
        }
      }
      const Watch w = *i;
      if (j != i) *j = w;
      ++i;
      ++j;
      if constexpr (kProp == 2) {
        if (((reinterpret_cast<uintptr_t>(i - 1)) & 63) == 0 || i - 1 == begin) touch(i - 1, i);
      }
      if constexpr (kProp > 0) ++(w.binary() ? prop_stats_.bin : prop_stats_.longw);
      if constexpr (kStats) {
        if (!w.binary()) {
          ++visit_long;
        } else if (w.redundant_binary()) {
          ++visit_red;
        } else {
          ++visit_irr;
        }
      }
      const int8_t bv = vals[w.blit];
      if (bv > 0) {
        if constexpr (kProp > 0) prop_stats_.blocked += !w.binary();
        continue;
      }
      if (w.binary()) {
        if constexpr (kStats) {
          j[-1].ref = w.ref | kBinaryUsed | kBinaryRecent;
          ++(w.redundant_binary() ? implied_red : implied_irr);
        }
        if (bv < 0) {
          conflict_bin_[0] = not_lit;
          conflict_bin_[1] = w.blit;
          conflict_ref_ = kNoReason;
          conflict = true;
          break;
        }
        imply(w.blit, kBinaryTag | not_lit, lit_level);
        continue;
      }
      ++ticks;
      Clause& c = *reinterpret_cast<Clause*>(arena + w.ref);
      [[maybe_unused]] int kind = 0;  // (kProp) irredundant, tier1, tier2, tier3
      [[maybe_unused]] uint32_t psm_bucket = 0;
      if constexpr (kProp > 0) {
        kind = !c.redundant ? 0 : (c.keep || c.glue <= tier1_) ? 1 : c.glue <= tier2_ ? 2 : 3;
        if (c.garbage) {
          ++prop_stats_.garbage;
        } else {
          ++prop_stats_.visit[kind];
          psm_bucket = psm_quartile(c);
          ++prop_stats_.psm_visit[kind == 1][psm_bucket];
        }
        if constexpr (kProp == 2) touch(&c, c.lits() + 2);
      }
      if (c.garbage) {  // deleted clause (collections are deferred): drop its watch
        --j;
        continue;
      }
      if constexpr (kVivify) {
        if (w.ref == ignore) continue;
      }
      Lit* lits = c.lits();
      const Lit other = lits[0] ^ lits[1] ^ not_lit;
      const int8_t ov = vals[other];
      if (ov > 0) {
        j[-1].blit = other;
        if constexpr (kProp > 0) ++prop_stats_.other_true;
        continue;
      }
      lits[0] = other;
      lits[1] = not_lit;
      const uint32_t size = c.size;
      uint32_t pos = c.pos;
      if (pos < 2 || pos >= size) pos = 2;
      uint32_t k = pos;
      int8_t rv = -1;
      for (; k < size; ++k) {
        rv = vals[lits[k]];
        if (rv >= 0) break;
      }
      if (rv < 0) {
        for (k = 2; k < pos; ++k) {
          rv = vals[lits[k]];
          if (rv >= 0) break;
        }
      }
      if constexpr (kProp > 0) {
        // literals read by the replacement search: pos..k, or pos..size and 2..k after the wrap
        const uint32_t end_k = rv >= 0 ? k + 1 : size;
        const bool wrapped = rv < 0 || k < pos;
        prop_stats_.lits_read += wrapped ? (size - pos) + ((rv >= 0 ? k + 1 : pos) - 2) : end_k - pos;
        if constexpr (kProp == 2) {
          if (wrapped) {
            if (size > pos) touch(lits + pos, lits + size);
            if ((rv >= 0 ? k + 1 : pos) > 2) touch(lits + 2, lits + (rv >= 0 ? k + 1 : pos));
          } else {
            touch(lits + pos, lits + end_k);
          }
        }
      }
      if (rv >= 0) {
        c.pos = k;
        const Lit r = lits[k];
        if (rv > 0) {
          // Satisfied by a non-watched literal: keep the watch, remember r as blocker.
          j[-1].blit = r;
          if constexpr (kProp > 0) ++prop_stats_.repl_true;
          continue;
        }
        if constexpr (kProp > 0) ++prop_stats_.moved;
        lits[1] = r;
        lits[k] = not_lit;
        --j;
        const size_t oi = static_cast<size_t>(i - begin), oj = static_cast<size_t>(j - begin);
        watches_.push_back(r, Watch{other, w.ref});
        Watch* const moved = watches_.pool() + list_begin;
        if (moved != begin) {
          begin = moved;
          i = begin + oi;
          j = begin + oj;
          end = begin + list_size;
        }
        continue;
      }
      if (ov < 0) {
        conflict_ref_ = w.ref;
        conflict = true;
        if constexpr (kProp > 0) {
          ++prop_stats_.conflict[kind];
          ++prop_stats_.psm_implied[kind == 1][psm_bucket];
        }
        break;
      }
      if constexpr (kProp > 0) {
        ++prop_stats_.implied[kind];
        ++prop_stats_.psm_implied[kind == 1][psm_bucket];
      }
      if (lower) {
        uint32_t lvl = lit_level;
        for (uint32_t m = 2; m < size; ++m) lvl = std::max(lvl, vdata[var_of(lits[m])].level);
        ticks += size / 8;
        imply(other, w.ref, lvl);
      } else {
        imply(other, w.ref, current);
      }
    }
    if (conflict) {
      while (i != end) *j++ = *i++;
    }
    watches_[not_lit].resize(static_cast<size_t>(j - begin));
    if (conflict) break;
  }
  propagated_ = propagated;
  has_conflict_ = conflict;
  stats_.propagations += propagated - start;
  if constexpr (kProp > 0) prop_stats_.props += propagated - start;
  if constexpr (kStats) {
    bin_census_.visit_red += visit_red;
    bin_census_.visit_irr += visit_irr;
    bin_census_.visit_long += visit_long;
    bin_census_.implied_red += implied_red;
    bin_census_.implied_irr += implied_irr;
  }
  if constexpr (kVivify) {
    stats_.vivify_ticks += ticks;
  } else {
    stats_.ticks += ticks;
  }
  return !conflict;
}

// --propstats: the share of a clause's literals that the saved phases satisfy (Audemard, Lagniez,
// Mazure and Sais 2011, the progress saving measure), as a quartile 0-3.
uint32_t Solver::psm_quartile(const Clause& c) const {
  const Lit* lits = c.lits();
  uint32_t psm = 0;
  for (uint32_t k = 0; k < c.size; ++k) psm += saved_[var_of(lits[k])] == (is_negative(lits[k]) ? -1 : 1);
  return std::min<uint32_t>(3, 4 * psm / c.size);
}

// --propstats: one line per progress line, the interval since the last one (search propagation):
// share = time in propagation / wall time, ticks / ns per propagated literal, watches visited per
// propagation (binary, long), blocked = long-clause watches with a true blocking literal, visits =
// clause dereferences, their outcomes (shares of the visits) and literals scanned, then visits,
// implications and conflicts by clause kind (irredundant, tier1, tier2, tier3; shares of the visits
// of that kind), visits by PSM quartile with their implication rate, the tier1 clauses by PSM, and
// with --propstats=2 the lines touched and the cache models' misses per propagation.
void Solver::report_propstats() {
  PropStats& s = prop_stats_;
  PropStats& l = prop_last_;
  const auto d = [](uint64_t a, uint64_t b) { return b ? static_cast<double>(a) / static_cast<double>(b) : 0.0; };
  const uint64_t props = s.props - l.props;
  uint64_t visits = 0, vis[4], imp[4], con[4];
  for (int k = 0; k < 4; ++k) {
    vis[k] = s.visit[k] - l.visit[k];
    imp[k] = s.implied[k] - l.implied[k];
    con[k] = s.conflict[k] - l.conflict[k];
    visits += vis[k];
  }
  const uint64_t longw = s.longw - l.longw;
  const double now = seconds();
  std::printf("c [%.2f s] prop props=%llu share=%.3f ticks/prop=%.2f ns/prop=%.1f ns/call=%.0f watches/prop=%.1f "
              "bin/prop=%.2f long/prop=%.1f blocked=%.3f visits/prop=%.2f garbage/prop=%.3f other_true=%.3f "
              "repl_true=%.3f moved=%.3f implied=%.3f conflict=%.4f lits/visit=%.2f "
              "visit_irr/t1/t2/t3=%.3f/%.3f/%.3f/%.3f implied_irr/t1/t2/t3=%.3f/%.3f/%.3f/%.3f "
              "conflict_irr/t1/t2/t3=%.3f/%.3f/%.3f/%.3f",
              now, static_cast<unsigned long long>(props),
              now > prop_last_seconds_ ? static_cast<double>(s.nanos - l.nanos) / 1e9 / (now - prop_last_seconds_) : 0.0,
              d(stats_.ticks - prop_last_ticks_, props), d(s.nanos - l.nanos, props),
              d(s.nanos - l.nanos, s.calls - l.calls), d(s.list_watches - l.list_watches, props),
              d(s.bin - l.bin, props), d(longw, props), d(s.blocked - l.blocked, longw), d(visits, props),
              d(s.garbage - l.garbage, props), d(s.other_true - l.other_true, visits),
              d(s.repl_true - l.repl_true, visits), d(s.moved - l.moved, visits),
              d(imp[0] + imp[1] + imp[2] + imp[3], visits), d(con[0] + con[1] + con[2] + con[3], visits),
              d(s.lits_read - l.lits_read, visits), d(vis[0], visits), d(vis[1], visits), d(vis[2], visits),
              d(vis[3], visits), d(imp[0], vis[0]), d(imp[1], vis[1]), d(imp[2], vis[2]), d(imp[3], vis[3]),
              d(con[0], vis[0]), d(con[1], vis[1]), d(con[2], vis[2]), d(con[3], vis[3]));
  // PSM quartiles of the visited clauses (tier1 / the others): the share of the visits, and the
  // share of those visits that implied or conflicted.
  for (int t = 1; t >= 0; --t) {
    uint64_t total = 0;
    for (int b = 0; b < 4; ++b) total += s.psm_visit[t][b] - l.psm_visit[t][b];
    std::printf(" psm_%s=", t ? "t1" : "other");
    for (int b = 0; b < 4; ++b) {
      const uint64_t v = s.psm_visit[t][b] - l.psm_visit[t][b];
      std::printf("%s%.3f(%.3f)", b ? "/" : "", d(v, total), d(s.psm_implied[t][b] - l.psm_implied[t][b], v));
    }
  }
  {
    // PSM quartiles of the tier1 clauses now (not weighted by visits).
    uint64_t q[4] = {}, n = 0;
    for (const uint32_t ref : clauses_) {
      const Clause& c = clause(ref);
      if (c.garbage || !c.redundant || !(c.keep || c.glue <= tier1_)) continue;
      ++q[psm_quartile(c)];
      ++n;
    }
    std::printf(" t1psm=%.3f/%.3f/%.3f/%.3f", d(q[0], n), d(q[1], n), d(q[2], n), d(q[3], n));
  }
  if (opts_.propstats == 2) {
    std::printf(" lines/prop=%.2f", d(s.lines - l.lines, props));
    static const char* const kNames[4] = {"32K", "256K", "2M", "8M"};
    for (int k = 0; k < 4; ++k) {
      std::printf(" miss%s/prop=%.2f", kNames[k], d(prop_cache_[k].miss - prop_last_miss_[k], props));
      prop_last_miss_[k] = prop_cache_[k].miss;
    }
  }
  std::printf("\n");
  std::fflush(stdout);
  l = s;
  prop_last_seconds_ = now;
  prop_last_ticks_ = stats_.ticks;
}

}  // namespace psat
