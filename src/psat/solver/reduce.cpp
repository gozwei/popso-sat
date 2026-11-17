// Clause database maintenance: learned clause reduction (three tiers by glue, CaDiCaL's "used"
// aging), root-level simplification (satisfied clauses, falsified literals) and the compacting
// garbage collector of the clause arena.

#include <algorithm>
#include <cmath>
#include <cstring>

#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace psat {

void Solver::delete_clause_proof(const Clause& c) {
  if (proof_) proof_->del(c.lits(), c.size);
}

void Solver::mark_reasons(bool on) {
  for (const Lit l : trail_) {
    const VarData& d = vdata_[var_of(l)];
    if (!d.level || d.reason == kNoReason || (d.reason & kBinaryTag)) continue;
    clause(d.reason).reason = on;
  }
}

void Solver::update_tier_limits() {
  // --dynamictiers=1: one histogram (focused-mode uses); 2: the current mode's own histogram.
  uint64_t* const used = opts_.dynamictiers == 2 ? mode_used_glue_[stable_] : used_glue_;
  uint64_t total = 0;
  for (uint32_t g = 0; g < kGlueBuckets; ++g) total += used[g];
  if (total < 1000) return;  // too few samples: keep the current limits
  const uint64_t q1 = total * static_cast<uint64_t>(opts_.tier1quantile) / 100;
  const uint64_t q2 = total * static_cast<uint64_t>(opts_.tier2quantile) / 100;
  uint64_t cum = 0;
  uint32_t t1 = 0, t2 = 0;
  for (uint32_t g = 0; g < kGlueBuckets; ++g) {
    cum += used[g];
    if (!t1 && cum >= q1) t1 = g;
    if (!t2 && cum >= q2) t2 = g;
  }
  if (!t1) t1 = kGlueBuckets - 1;
  if (!t2) t2 = kGlueBuckets - 1;
  tier1_ = std::max<uint32_t>(t1, 1);
  tier2_ = std::max(tier1_ + 1, t2);
  mode_tier1_[stable_] = tier1_, mode_tier2_[stable_] = tier2_;
  for (uint32_t g = 0; g < kGlueBuckets; ++g) used[g] /= 2;  // older samples fade
}

// --tier1revive=p: an age limit L (2-31; 32: none) that follows the age at which the chance of a
// tier1 clause being used again falls below p per mille. At each reduction the oldest age kept,
// L - 1, is looked at: if its unused clauses were used again (before the next reduction) in fewer
// than p per mille of the cases (decayed counts, enough of them), L falls by one, otherwise it
// rises by one. The chance falls with the age (--tierstats; per reduce interval at ages 1, 2-3,
// 4-7, 8-15, 16-31: crn_40_1521_s 6.8, 4.4, 2.1, 1.3, 0.54%; knight_18 29, 21, 14, 6.7, 1.2%;
// gensys-ukn004 31, 26, 20, 13, 2.5%). A first version jumped to the youngest age below p: noisy
// single ages sent L from 32 to 6 at once on crn_40 (and back to 19). Between ages 5 and 20 the
// chance is flat near 1% on crn_40, so that even the gradual L wandered from 22 to 5 and back to
// 13: L stays at least --tier1revivemin (8, the tested --tier1age). Paired 120 s: 72 solved
// against 74 (ps_200_300_70 and SC23_Timetable lost).
void Solver::update_revive_limit() {
  const double p = static_cast<double>(opts_.tier1revive) / 1000.0;
  constexpr double kSamples = 1000;  // least decayed exposure to judge an age
  const auto min_limit = static_cast<uint32_t>(opts_.tier1revivemin);
  const uint32_t oldest = revive_limit_ - 1;
  if (revive_exposure_[oldest] >= kSamples && revive_count_[oldest] < p * revive_exposure_[oldest]) {
    if (revive_limit_ > min_limit) --revive_limit_;
  } else if (revive_limit_ < 32) {
    ++revive_limit_;
  }
  for (uint32_t a = 0; a < 32; ++a) {  // (a window of about 16 reductions)
    revive_exposure_[a] *= 15.0 / 16.0;
    revive_count_[a] *= 15.0 / 16.0;
  }
}

void Solver::reduce() {
  const PassTimer pass_timer(*this, kPassReduce);
  ++stats_.reductions;
  if (opts_.dynamictiers) update_tier_limits();
  mark_reasons(true);
  // Candidates: unprotected learned clauses not used since the last reduction (tier2 clauses
  // survive two rounds unused, tier1 clauses are kept).
  // Kept for good, tier1 grows with the run, mostly through promotion (the glue of a learned clause
  // recomputed in conflict analysis falls to tier1: 72-96% of the tier1 inflow on crn_40, knight_18,
  // gensys, asconhash H10): crn_40 2.98M tier1 clauses at 420 s (20x its 145k irredundant ones, 3%
  // of them used in the last two intervals), knight_18 581k at 2160 s, gensys-ukn004 107k (6x).
  // --tier1age=n: a tier1 clause found unused (no use in the last two intervals) at n reductions in
  // a row is deleted. With n = 8: knight_18 tier1 about 100k, gensys 46k, conflicts per second
  // +57% and +20% late; asconhash H10 496 s against 1578 s; but paired 120 s 70 solved against 74.
  // --tier1ageconf=k: the same with the limit in conflicts, about k thousand: ceil(k * 1000 / the
  // interval that just ended) reductions (1-31), so the limit in reductions falls as the interval
  // grows.
  // --tier1revive: an adaptive age limit (update_revive_limit).
  // --tier1limit=r: a tier1 budget of r % of the irredundant long clauses (at least --tier1min);
  // above it the tier1 clauses unused through --tier1limitage reductions are deleted, the longest
  // unused first, down to the budget. Aging alone lost on large formulas whose tier1 is a small
  // part of the clauses (ps_200_300_70, 1.5M clauses, 216k tier1: 48 s -> unsolved at 120 s;
  // spg_420_280 16 -> 48 s; SC23_Timetable 42 s -> unsolved) and gained where tier1 is many times
  // the formula (case9, 4.5k clauses: 73 -> 16 s). r = 100: paired 120 s 75 solved against 74,
  // crn_40 tier1 280k and twice the conflicts in 1800 s; asconhash and knight_18 (tier1 below the
  // formula) unchanged. r = 25: asconhash 729 s, but knight_18 unsolved at 3000 s on seeds 0 and 1.
  // --tier1agepromoted: these delete only clauses promoted into tier1 (not kept).
  // --tier1keepglue=G: they delete only tier1 clauses above glue G, whose glue keeps being
  // recomputed (kept ones are not): with G = 1 the clauses that propagate within one level stay for
  // good (as Kissat's tier1, glue 1 under its dynamic limit on the miters) and glue-2 ones can go.
  // With --tier1age=16 (glue-2 ones go after 16 reductions unused): booth28 wallace 1914 -> 1640 s
  // at the same conflicts (tier1 at 1560 s 148k -> 113k), but ps_200_323_70 40 s -> unsolved at
  // 120 s (large formula, tier1 a small part of it, as with --tier1age=8). With --tier1limit=100
  // --tier1limitage=16 instead the same deletions happen only above the budget: wallace 1617 s,
  // booth29 442 s against 420-450 s, paired 120 s 73 solved against 72, crn_40 peak RSS 332 MB
  // against 640 MB (its glue-1 class still grows).
  // --tierstats keeps the ages without deleting (and counts the exposure by age).
  uint32_t age_limit = static_cast<uint32_t>(opts_.tier1age);
  if (!age_limit && opts_.tier1ageconf) {
    const double interval = static_cast<double>(opts_.reduceint) * std::sqrt(static_cast<double>(stats_.reductions));
    const double limit = std::ceil(1000.0 * static_cast<double>(opts_.tier1ageconf) / interval);
    age_limit = static_cast<uint32_t>(std::clamp(limit, 1.0, 31.0));
  }
  if (!age_limit && opts_.tier1revive) {
    update_revive_limit();
    if (revive_limit_ < 32) age_limit = revive_limit_;
  }
  const bool budget = opts_.tier1limit != 0;
  const bool track_age = age_limit || budget || opts_.tierstats || opts_.tier1revive;
  uint64_t tier1_count = 0;
  std::vector<std::pair<uint64_t, uint32_t>> order, tier1_order;
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (!c.redundant || c.garbage) continue;
    const bool tier1 = c.keep || c.glue <= tier1_;
    if (c.reason) {
      tier1_count += tier1;
      continue;
    }
    const bool used = c.used != 0;
    if (used) --c.used;
    if (track_age && tier1) {
      if (used) {
        c.age = 0;
      } else if (c.age < 31) {
        ++c.age;
      }
      const bool agable = !used && !((opts_.tier1agepromoted || opts_.tier1keepglue) && c.keep);
      if (age_limit && agable && c.age >= age_limit) {
        delete_clause_proof(c);
        c.garbage = 1;
        note_garbage(c);
        garbage_words_ += kHeaderWords + c.size;
        --redundant_;
        ++stats_.reduced_clauses;
        ++stats_.reduced_tier1;
        continue;
      }
      if (!used) {
        if (opts_.tierstats) ++tier_stats_.exposure[age_bucket(c.age)];
        revive_exposure_[c.age] += 1;
      }
      ++tier1_count;
      // Longest unused first, then high glue, then long.
      if (budget && agable && c.age >= static_cast<uint32_t>(opts_.tier1limitage)) {
        tier1_order.emplace_back((uint64_t{c.age} << 52) | (uint64_t{c.glue} << 32) | c.size, ref);
      }
      continue;
    }
    if (used || tier1) continue;
    // Least useful first: high glue, then long.
    order.emplace_back((uint64_t{c.glue} << 32) | c.size, ref);
  }
  if (budget) {
    const uint64_t limit = std::max<uint64_t>(static_cast<uint64_t>(opts_.tier1min),
                                              irredundant_ * static_cast<uint64_t>(opts_.tier1limit) / 100);
    if (tier1_count > limit) {
      const size_t excess = static_cast<size_t>(std::min<uint64_t>(tier1_count - limit, tier1_order.size()));
      std::sort(tier1_order.begin(), tier1_order.end(),
                [](const auto& a, const auto& b) { return a.first != b.first ? a.first > b.first : a.second < b.second; });
      for (size_t i = 0; i < excess; ++i) {
        Clause& c = clause(tier1_order[i].second);
        delete_clause_proof(c);
        c.garbage = 1;
        note_garbage(c);
        garbage_words_ += kHeaderWords + c.size;
        --redundant_;
        ++stats_.reduced_clauses;
        ++stats_.reduced_tier1;
      }
    }
  }
  // Ties (same glue and size) by arena position, older first: std::sort leaves equal keys in an
  // order that differs between standard libraries (libc++ / libstdc++ took different searches).
  std::sort(order.begin(), order.end(),
            [](const auto& a, const auto& b) { return a.first != b.first ? a.first > b.first : a.second < b.second; });
  const size_t n = order.size();
  const size_t target = n * static_cast<size_t>(opts_.reducefraction) / 100;
  for (size_t i = 0; i < target; ++i) {
    Clause& c = clause(order[i].second);
    delete_clause_proof(c);
    c.garbage = 1;
    note_garbage(c);
    garbage_words_ += kHeaderWords + c.size;
    --redundant_;
    ++stats_.reduced_clauses;
  }
  mark_reasons(false);
  maybe_collect_garbage();
  const double delta = static_cast<double>(opts_.reduceint) * std::sqrt(static_cast<double>(stats_.reductions + 1));
  reduce_limit_ = stats_.conflicts + static_cast<uint64_t>(delta);
  if (opts_.verbose >= 3) {
    // Progress since the last reduction: learned clause size and glue, decisions and
    // propagations per conflict; the clause database and root units now.
    const auto d = [](uint64_t a, uint64_t b) { return b ? static_cast<double>(a) / static_cast<double>(b) : 0.0; };
    const uint64_t nl = stats_.learned - progress_.learned, c = stats_.conflicts - progress_.conflicts;
    std::printf("c [%.2f s] %c conflicts %llu  size %.1f  glue %.1f  decisions %.1f  props %.0f /conflict  tiers %u/%u  "
                "irredundant %llu+%llu binary  learned %llu+%llu binary  fixed %llu  vivified %llu/%llu\n",
                seconds(), stable_ ? 'S' : 'F', static_cast<unsigned long long>(stats_.conflicts),
                d(stats_.learned_literals - progress_.learned_literals, nl), d(stats_.learned_glue - progress_.learned_glue, nl),
                d(stats_.decisions - progress_.decisions, c), d(stats_.propagations - progress_.propagations, c), tier1_, tier2_,
                static_cast<unsigned long long>(irredundant_), static_cast<unsigned long long>(binaries_irredundant_),
                static_cast<unsigned long long>(redundant_), static_cast<unsigned long long>(binaries_redundant_),
                static_cast<unsigned long long>(fixed_), static_cast<unsigned long long>(stats_.vivified),
                static_cast<unsigned long long>(stats_.vivify_checked));
    progress_ = stats_;
  }
}

// Removes binary clauses satisfied at the root (level 0 only, after complete propagation: then
// every binary clause with an assigned literal is satisfied).
void Solver::flush_root_binaries() {
  for (Lit l = 0; l < 2 * num_vars_; ++l) {
    const WatchList ws = watches_[l];
    const bool l_assigned = vals_[l] != 0;
    size_t j = 0;
    for (size_t i = 0; i < ws.size(); ++i) {
      const Watch w = ws[i];
      if (w.binary() && (l_assigned || vals_[w.blit] != 0)) {
        if (l < w.blit) {
          if (proof_) {
            const Lit bin[2] = {l, w.blit};
            proof_->del(bin, 2);
          }
          if (w.redundant_binary()) {
            --binaries_redundant_;
          } else {
            --binaries_irredundant_;
          }
        }
        continue;
      }
      ws[j++] = w;
    }
    ws.resize(j);
  }
}

void Solver::simplify_root() {
  const ProofScope proof_scope(*this, kProofSimplify);
  // Precondition: level 0, everything propagated, no conflict.
  last_simplify_fixed_ = fixed_;
  ++stats_.simplified_root;
  flush_root_binaries();
  std::vector<Lit> removed;  // root-falsified literals of a clause (for the proof)
  for (const uint32_t ref : clauses_) {
    Clause& c = clause(ref);
    if (c.garbage) continue;
    Lit* lits = c.lits();
    bool satisfied = false, falsified = false;
    for (uint32_t k = 0; k < c.size; ++k) {
      const int8_t v = vals_[lits[k]];
      if (v > 0) {
        satisfied = true;
        break;
      }
      if (v < 0) falsified = true;
    }
    if (!satisfied && !falsified) continue;
    if (satisfied) {
      delete_clause_proof(c);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      continue;
    }
    // Remove the root-falsified literals. The watched literals lits[0], lits[1] are not false
    // (the clause would otherwise have propagated or be satisfied), so they stay in place. The
    // proof keeps the longer clause (ProofWriter::shorten).
    clause_buf_.clear();
    for (uint32_t k = 0; k < c.size; ++k) {
      if (vals_[lits[k]] == 0) clause_buf_.push_back(lits[k]);
    }
    if (proof_) {
      removed.clear();
      for (uint32_t k = 0; k < c.size; ++k) {
        if (vals_[lits[k]] < 0) removed.push_back(lits[k]);
      }
      proof_->shorten(clause_buf_.data(), clause_buf_.size(), removed.data(), removed.size());
    }
    if (clause_buf_.size() == 2) {
      add_binary(clause_buf_[0], clause_buf_[1], c.redundant);
      c.garbage = 1;
      note_garbage(c);
      garbage_words_ += kHeaderWords + c.size;
      if (c.redundant) {
        --redundant_;
      } else {
        --irredundant_;
      }
      continue;
    }
    garbage_words_ += c.size - static_cast<uint32_t>(clause_buf_.size());
    shrunk_words_ += c.size - static_cast<uint32_t>(clause_buf_.size());
    std::copy(clause_buf_.begin(), clause_buf_.end(), lits);
    c.size = static_cast<uint32_t>(clause_buf_.size());
    c.pos = 2;
    if (c.glue > c.size - 1) c.glue = c.size - 1;
  }
  maybe_collect_garbage();
  // Amortize: the next simplification waits for search effort proportional to its cost.
  simplify_ticks_limit_ = stats_.ticks + arena_.size() / 4 + 2 * size_t{num_vars_};
}

// Compacts the arena from the first garbage clause on (as Kissat's sparse collection): clauses
// before it keep their place, and their watches are not even looked up. Learned clauses live at
// the end of the arena, so collections after a reduction move only the learned tail instead of
// the whole (mostly irredundant) formula. Words left dead by clauses shortened in place are
// reclaimed by a full compaction once they exceed an eighth of the arena.
void Solver::collect_garbage() {
  if (garbage_words_ == 0) return;
  ++stats_.collections;
  const bool full = shrunk_words_ * 8 > arena_.size();
  // clauses_ is in arena order: find the first garbage clause.
  size_t first = 0;
  if (!full) {
    if (first_garbage_ == UINT32_MAX) {  // only shrunk clauses: their few dead words stay for now
      garbage_words_ = 0;
      return;
    }
    first = static_cast<size_t>(std::lower_bound(clauses_.begin(), clauses_.end(), first_garbage_) - clauses_.begin());
  }
  const uint32_t start = full ? 0 : clauses_[first];
  if (full) ++stats_.collections_full;
  stats_.collected_words += arena_.size() - start;
  // Pass 1: forwarding addresses (in the header's pos field) for the surviving clauses.
  uint32_t dst = start;
  for (size_t i = first; i < clauses_.size(); ++i) {
    Clause& c = clause(clauses_[i]);
    if (c.garbage) continue;
    c.pos = dst;
    dst += kHeaderWords + c.size;
  }
  // Pass 2: watches and reasons (only references at or after the start can change).
  for (size_t l = 0; l < watches_.size(); ++l) {
    const WatchList ws = watches_[l];
    size_t j = 0;
    for (size_t i = 0; i < ws.size(); ++i) {
      Watch w = ws[i];
      if (!w.binary() && w.ref >= start) {
        const Clause& c = clause(w.ref);
        if (c.garbage) continue;
        w.ref = c.pos;
      }
      ws[j++] = w;
    }
    ws.resize(j);
  }
  for (const Lit l : trail_) {
    VarData& d = vdata_[var_of(l)];
    if (d.reason == kNoReason || (d.reason & kBinaryTag) || d.reason < start) continue;
    d.reason = clause(d.reason).pos;
  }
  // Pass 3: move (destinations never overlap later clauses).
  size_t live = first;
  for (size_t i = first; i < clauses_.size(); ++i) {
    const uint32_t ref = clauses_[i];
    const Clause& c = clause(ref);
    if (c.garbage) continue;
    const uint32_t to = c.pos;
    const uint32_t words = kHeaderWords + c.size;
    if (to != ref) std::memmove(arena_.data() + to, arena_.data() + ref, size_t{words} * sizeof(uint32_t));
    clause(to).pos = 2;
    clauses_[live++] = to;
  }
  clauses_.resize(live);
  watched_clauses_ = live;
  arena_.resize(dst);
  if (arena_.capacity() > 2 * arena_.size() + 1024) arena_.shrink_to_fit();
  garbage_words_ = 0;
  first_garbage_ = UINT32_MAX;
  recent_learned_.clear();
  if (full) shrunk_words_ = 0;
  watches_.maybe_compact();  // (no watch list is being iterated here)
}

// Propagation drops watches of garbage clauses when it meets them, so a collection can wait until
// it pays: when at least half of what it would move is garbage (typically the learned tail after
// a reduction), or when garbage is an eighth of the arena (memory).
void Solver::maybe_collect_garbage() {
  if (garbage_words_ == 0) return;
  const uint64_t tail = first_garbage_ == UINT32_MAX ? 0 : arena_.size() - first_garbage_;
  if (2 * garbage_words_ >= tail || 8 * garbage_words_ >= arena_.size() || shrunk_words_ * 8 > arena_.size()) {
    collect_garbage();
  }
}

}  // namespace psat
