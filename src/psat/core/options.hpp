#pragma once
// Solver options: one table of named integer knobs with defaults and ranges. The CLI accepts
// every option as --name=value (--name means 1, --no-name means 0), which keeps A/B experiments
// and tuning free of plumbing.

#include <cstdint>
#include <cstdio>
#include <string>

namespace psat {

// X(name, default, min, max, description)
#define PSAT_OPTIONS(X)                                                                            \
  X(seed, 0, 0, INT32_MAX, "random seed (0 = natural variable order)")                            \
  X(seedorder, 1, 0, 1, "a nonzero --seed also shuffles the initial decision order (0: natural order; the seed drives only the random choices)") \
  X(verbose, 0, 0, 3, "verbosity level")                                                          \
  X(check, 1, 0, 1, "check a SAT model against the original formula before reporting it")         \
  X(reportmem, 0, 0, 3600, "memory report (resident size and its parts) every <n> seconds and after the large passes, with a progress line (counts, tiers, schedules, pass times) in the search (0: off)") \
  X(invariants, 0, 0, 1, "debugging: check watch / elimination invariants after inprocessing")   \
  X(stopfault, 0, 0, INT32_MAX, "debugging: every n-th stop check of the inprocessing passes ends the pass as at the time limit, and the search goes on (0: off)") \
  X(watchstress, 0, 0, 1, "debugging: copy the watch pool on every relocation and compact at every chance (stale pointers become use-after-free)") \
  X(stable, 1, 0, 2, "search mode: 0 = focused only, 1 = switch focused/stable, 2 = stable only") \
  X(queueorder, 0, 0, 4, "initial focused-mode decision order: 0 = highest variable index first, 1 = lowest first, 2 = lowest first if AND gate outputs are numbered after their inputs (queueordergates, queueorderforward), 3 = as 2 in the first focused phase only, 4 = lowest first in the first focused phase only") \
  X(queueordergates, 50, 0, 1000, "--queueorder=2 / 3: least share of the variables that are AND gate outputs (per mille)") \
  X(queueorderforward, 900, 0, 1000, "--queueorder=2 / 3: least share of the AND gates whose output index is above their inputs' (per mille)") \
  X(stablereorder, 0, 0, 2, "at a switch to stable mode the scores come from clause occurrences weighted 1 / size (1: replaced, 2: added; the heaviest variable gets one current bump; 0: off)") \
  X(stablereordersize, 100, 2, 100000, "--stablereorder: only clauses of at most this many literals count") \
  X(queuescores, 0, 0, 2, "at a switch to focused mode the decision queue takes the stable-mode score order, highest score decided first (1: every switch, 2: the first switch only; 0: the queue keeps its order)") \
  X(renumber, 1, 0, 3, "renumber the variables internally for memory locality, before preprocessing (1: breadth-first on the clause graph if the input numbering looks random; 2: breadth-first always; 3: random, for experiments); decision order, proofs and models keep the input numbering") \
  X(renumberrandom, 950, 0, 1000, "--renumber=1: the input numbering looks random if its clause span is this many per mille of a random numbering's") \
  X(modeinit, 1000, 10, INT32_MAX, "conflicts before the first mode switch")                      \
  X(modegrowth, 200, 100, 1000, "growth of the mode length in ticks per focused+stable pair (%)") \
  X(modeschedule, 1, 0, 2, "mode lengths: 0 = geometric (modegrowth), 1 = quadratic in the pair count, 2 = power modepower") \
  X(modepower, 150, 50, 400, "--modeschedule=2: mode length grows with this power of the pair count (%)") \
  X(restartint, 1, 1, 10000, "minimum conflicts between focused-mode restarts")                   \
  X(restartgrow, 1, 0, 1, "focused restart interval grows with log10 of the restart count")      \
  X(restartmargin, 10, 0, 100, "fast glue average above slow one by this much restarts (%)")      \
  X(reusetrail, 1, 0, 1, "restarts keep the decisions that would be taken again")               \
  X(emafast, 33, 1, 1000, "window of the fast glue moving average (conflicts)")                   \
  X(emaslow, 100000, 100, 10000000, "window of the slow glue moving average (conflicts)")         \
  X(reluctant, 1, 0, 1, "reluctant doubling (Luby) restarts in stable mode")                      \
  X(reluctantint, 1024, 1, 1 << 20, "base interval of reluctant doubling (conflicts)")            \
  X(reluctantlim, 1048576, 1, 1 << 30, "largest reluctant doubling interval (conflicts)")         \
  X(reduceint, 1000, 10, 1000000, "base reduce interval (scaled by sqrt(reductions))")            \
  X(reducefraction, 75, 10, 100, "fraction of reduce candidates removed (%)")                     \
  X(tier1, 2, 1, 100, "glue limit of tier1 (kept) learned clauses")                               \
  X(tier2, 6, 1, 1000, "glue limit of tier2 (kept while used) learned clauses")                   \
  X(tier1age, 0, 0, 31, "a tier1 learned clause not used through this many reductions in a row is deleted (0: tier1 clauses are kept for good)") \
  X(tier1ageconf, 0, 0, 1000000, "a tier1 learned clause not used for about this many thousand conflicts is deleted (aging as --tier1age, its limit in reductions from the current reduce interval; 0: off; --tier1age wins)") \
  X(tier1revive, 0, 0, 1000, "tier1 aging with an adaptive age limit (reductions in a row unused): it falls by one while the unused tier1 clauses of the oldest age kept are used again in fewer than this many per mille of the following reduce intervals (decayed counts), else it rises by one (0: off; --tier1age / --tier1ageconf win)") \
  X(tier1revivemin, 8, 2, 31, "--tier1revive: the age limit stays at least this many reductions") \
  X(tier1limit, 0, 0, 100000, "tier1 budget in per cent of the irredundant long clauses (at least --tier1min): above it, tier1 clauses unused through --tier1limitage reductions in a row are deleted, the longest unused first, down to the budget (0: no budget)") \
  X(tier1min, 10000, 0, INT32_MAX, "--tier1limit: the budget is at least this many clauses") \
  X(tier1limitage, 8, 1, 31, "--tier1limit: only tier1 clauses unused through this many reductions in a row are deleted") \
  X(tier1keepglue, 0, 0, 100, "the tier1 learned clauses kept for good (their glue no longer recomputed) are those of glue at most this; the other tier1 clauses keep having their glue recomputed and are the ones --tier1age / --tier1ageconf / --tier1revive / --tier1limit delete (0: all tier1 clauses are kept for good)") \
  X(tier1agepromoted, 0, 0, 1, "--tier1age / --tier1ageconf / --tier1revive / --tier1limit delete only clauses promoted into tier1 (glue fell to tier1 when used in conflict analysis); clauses learned in tier1 are kept") \
  X(tierstats, 0, 0, 1, "statistics: with --reportmem two lines on the learned clauses at every progress line (tier1 by glue and age, inflow, how often aged tier1 clauses are used again; all learned clauses and their uses by glue, vivification by tier; the search is the same)") \
  X(dynamictiers, 0, 0, 2, "tier limits from glue quantiles of used clauses (1: focused-mode uses, glue before recomputation, one pair of limits; 2: per mode, each mode's limits from its own uses, glue after recomputation)") \
  X(tier1keep, 1, 0, 1, "learned clauses reaching tier1 are kept for good (their glue no longer recomputed); 0: tier1 membership follows the current glue and tier1 limit (age them with --tier1age)") \
  X(tier1quantile, 50, 1, 99, "dynamic tier1: share of used clauses with glue <= tier1 (%)")      \
  X(tier2quantile, 90, 1, 99, "dynamic tier2: share of used clauses with glue <= tier2 (%)")      \
  X(minimize, 1, 0, 1, "recursive learned clause minimization")                                   \
  X(minimizedepth, 1000, 1, 100000, "recursion depth limit of minimization")                      \
  X(shrink, 2, 0, 2, "shrink learned clauses to block UIPs (1; 2: lower-level reason literals may be implied)")     \
  X(phase, 1, 0, 1, "initial decision phase (1 = true)")                                          \
  X(target, 1, 0, 2, "target phases: 0 = off, 1 = stable mode, 2 = always")                       \
  X(rephase, 1, 0, 1, "periodic rephasing (best / original / inverted phases)")                   \
  X(rephaseint, 1000, 10, 1000000, "base rephase interval (conflicts)")                           \
  X(rephasestable, 0, 0, 2, "rephase only in stable mode (1; 2: the interval counts stable-mode conflicts)") \
  X(targetrestart, 0, 0, 1, "stable-mode restarts restart the target phases' consistent-trail record") \
  X(rephasescale, 0, 0, 1, "growth of the rephase interval: 0 = --rephaseint x the rephase count, 1 = --rephaseint x n x log10(n + 9)^3 for the n-th rephase") \
  X(rephasebestkeep, 0, 0, 1, "the best phases' trail record is reset only by a best rephase (B), not by the walk, original and inverted ones") \
  X(prefetch, 0, 0, 2, "prefetch the clauses of long watch lists in propagation on arenas of 8 MB or more (1: every long-clause watch; 2: only where the blocking literal is not true; 64-bit ARM builds only); off: on the i7 with 4 jobs, 1 cost ~20% time") \
  X(walk, 1, 0, 1, "local search phases in the rephase cycle (algorithm: --walkmode)")         \
  X(lucky, 1, 0, 1, "try trivial assignments (all false / all true, both orders) before search")  \
  X(walkeffort, 50, 1, 100000, "walk effort relative to search ticks (per mille)")               \
  X(walkmode, 3, 0, 3, "walk algorithm: 0 = ProbSAT, 1 = DDFW clause weighting (Ishtaiwi et al. 2005), 2 = DDFW with linear weight transfers and weighted-random flips (Chowdhury, Codel, Heule 2023), 3 = ProbSAT for the phases, then the walk of 2 for a model only; with 1-3 a walk that finds a model answers SAT") \
  X(walkfrom, 0, 0, 1, "the walk starts from: 0 = the saved phases, 1 = the decision phases (the target phase where decisions use it)") \
  X(walkrecord, 0, 0, 1, "a walk's assignment becomes the saved phases only if no earlier walk ended with fewer unsatisfied clauses") \
  X(walkmodel, 2, 0, 2, "--walkmode=3: the model walk's budget: 0 = the phase walk's (walkeffort share, at least 2 x literals); 1 = that while near a model (a minimum of at most sqrt(clauses) x walkmodelnear % unsatisfied clauses), else back off (skip 2^k - 1 calls after k far walks) on the share only; 2 = 1, and near walks get the 2 x literals floor only after a new lowest minimum") \
  X(walkmodelnear, 100, 0, 100000, "--walkmodel=1 / 2: near a model means at most sqrt(clauses) x this % unsatisfied clauses") \
  X(decay, 50, 1, 200, "EVSIDS score decay (per mille)")                                          \
  X(bumpreasons, 1, 0, 1, "also bump variables in reasons of learned clause literals")           \
  X(bumpreasonslimit, 100, 1, 100000, "skip reason bumping for learned clauses longer than this")   \
  X(randec, 0, 0, 1, "random decision sequences: now and then the decisions of a few conflicts pick random variables") \
  X(randecint, 500, 1, INT32_MAX, "base conflicts between random decision sequences (times the square root of their count)") \
  X(randeclength, 10, 1, 1000000, "conflicts in a random decision sequence")                      \
  X(randecstable, 0, 0, 1, "random decision sequences in stable mode too (else focused mode only)") \
  X(watchtrue, 0, 0, 1, "propagation: a true non-watched literal found while visiting a clause becomes the blocking literal of the falsified watch (0) or is watched instead (1)") \
  X(chrono, 0, 0, 2, "chronological backtracking (backjumps over more than chronolevels; 2: a missed implication before the next decision backjumps as usual)") \
  X(chronolevels, 100, 0, 1000000, "backjumps over more levels backtrack one level instead")     \
  X(chronounits, 0, 0, 1, "with --chrono: learned units too (assigned at the root out of order, without a restart)") \
  X(eliminate, 1, 0, 1, "bounded variable elimination rounds (pre- and inprocessing)")             \
  X(eliminateinit, 0, 0, INT32_MAX, "conflicts before the first round (0 = preprocess)")          \
  X(eliminateint, 2000, 10, INT32_MAX, "base interval between elimination rounds (conflicts)")    \
  X(eliminatebound, 16, 0, 1024, "largest clause-count increase allowed per eliminated variable") \
  X(eliminatetouched, 0, 0, 1, "another elimination round when variables were touched since the last one") \
  X(eliminatelitbound, 1000000, 0, 1000000, "largest literal-count increase allowed per eliminated variable") \
  X(eliminategrowth, 100, 0, 1000000, "cap on the irredundant literals added by elimination, per mille of those before the first round (0: none)") \
  X(eliminategrowthmin, 10000000, 0, INT32_MAX, "the elimination growth cap applies from this many irredundant literals before the first round") \
  X(eliminatefloor, 1000, 1, 1000000, "effort floor of the first elimination round (before search) in per mille of 1M + half the arena words")         \
  X(eliminateextend, 0, 0, 100, "first elimination round: past its budget, one more budget-sized chunk while the last chunk eliminated at least this share of its tries (%; AND circuits: goldcrest-xor-11 4.7k -> 222k eliminated before search); 0: off") \
  X(eliminateextendmax, 100, 1, 100000, "--eliminateextend: at most this many extra chunks")         \
  X(eliminateclslim, 100, 2, 100000, "largest resolvent size")                                   \
  X(eliminategatelim1, 3, 0, 100000, "largest resolvent of an elimination by a definition of a kind in --eliminategatekinds1 in the first elimination round (multiplier circuits eliminated before search: gm24sparrc); 0: no extra limit") \
  X(eliminategatekinds1, 4, 0, 15, "definitions --eliminategatelim1 applies to: 1 AND / equivalence, 2 XOR, 4 ITE (gm24sparrc), 8 semantic (all: asconhash H7 unsolved)") \
  X(eliminateclslim1, 0, 0, 100000, "largest resolvent size in the first elimination round (before search: eliminations with long resolvents there can hide circuit structure, gm24sparrc); 0: --eliminateclslim") \
  X(eliminategates, 1, 0, 1, "AND-gate / equivalence definitions in elimination")                 \
  X(eliminatexorlim, 3, 0, 1000, "largest XOR merged by elimination (0 = no limit)")              \
  X(definitions, 1, 0, 1, "semantic definitions in elimination (unsat cores by Kitten)")        \
  X(definitionticks, 2000, 10, 1000000, "Kitten ticks per definition attempt")                  \
  X(eliminateocclim, 1000, 1, 1000000, "skip variables with more occurrences in one polarity")    \
  X(eliminateeffort, 100, 1, 100000, "elimination effort relative to search ticks (per mille)")   \
  X(eliminatecomplete, 0, 0, 2, "the elimination bound grows only after a round that tried all its candidates (2: or eliminated fewer than a sixteenth of those it tried; 0: every round)") \
  X(eliminatelongskip, 0, 0, 1, "a variable whose last try failed on --eliminateclslim is not tried again while it has a clause longer than that limit + 1") \
  X(eliminatecircuit, 0, 0, 1000, "on an AND circuit numbered inputs first (at least this many per mille of the variables AND gate outputs, 90% of the gates forward) elimination runs as with --eliminateheap=1 --eliminatecomplete=1 (0: off)") \
  X(eliminateheap, 0, 0, 2, "elimination candidates from a heap on their current occurrence product (2: product of the literals in the clauses of each polarity; 0: sorted once per round)") \
  X(subsume, 1, 0, 1, "forward subsumption and strengthening in elimination rounds")              \
  X(mergepairs, 1, 0, 1, "elimination rounds, before forward subsumption: irredundant clauses over the same variables whose signs differ in one place are replaced by their resolvent, down by size (truth-table encodings: random-circuits)") \
  X(subsumeeffort, 100, 1, 100000, "forward subsumption effort per round in percent of the default") \
  X(subsumerel, 0, 0, 100000, "later rounds' forward subsumption effort is at least this many per mille of the search ticks since the last round (0: the fixed default only)") \
  X(eagersubsume, 20, 0, 100, "learned clauses checked for subsumption by each new learned clause") \
  X(substitute, 1, 0, 1, "equivalent literal substitution (SCCs of binary implications)")         \
  X(substituterounds, 1, 1, 64, "substitution passes in a row while each finds equivalences (clauses rewritten to binaries close new cycles)") \
  X(bva, 1, 0, 1, "bounded variable addition in elimination rounds")                             \
  X(bvavars, 1000000, 1, 1000000, "BVA adds at most max(bvavars, variables / 10) variables per round")  \
  X(bvahops, 0, 0, 1, "BVA ties: most 3-hop paths to the factored literal (SBVA), else smaller")     \
  X(bvafirst, 1, 0, 1, "BVA before (1) or after (0) the eliminations of the first round")            \
  X(bvaevery, 0, 0, 1, "BVA in every elimination round (not only the first)")                           \
  X(bvaprotect, 0, 0, 1, "variables added by BVA are not elimination candidates")                      \
  X(bvavarsrel, 0, 0, 100000, "BVA only if its trial adds at most this many per mille of the variables (0: no limit)") \
  X(bvamin, 180, 0, 1000, "BVA only if a trial round removes this many per mille of the clauses (0: always; 200 declined reconf10_22_queen20 at 199.96)") \
  X(bvaticks, 100000000, 1000, INT32_MAX, "BVA budget floor (ticks; at least a quarter of the arena)") \
  X(bvasched, 0, 0, 1, "BVA budget: half in the plain order, the rest by literal class (occurrence magnitude) and its clauses removed per tick") \
  X(bvaexplore, 25, 1, 100, "--bvasched: percent of the rest of the budget first split evenly over the classes") \
  X(bvaextend, 8, 1, 1000, "BVA past its budget (first rounds; plain order in eighths of it, --bvasched in shares) while the last part was productive (--bvaextendticks), up to this many times the budget") \
  X(bvaextendticks, 40000, 1, INT32_MAX, "--bvaextend: a share is productive if it removed a clause per this many ticks") \
  X(bvaextendreal, 1, 0, 1, "--bvaextend in the plain order also for the real round after a trial: past the trial's budget in eighths while productive") \
  X(bvalitcap, 0, 0, 1000, "BVA: one literal's matching stops at this many per mille of the round's budget (0: only at the round's limit)") \
  X(bvarealtarget, 0, 0, 1, "--bvaextend, real round after a qualifying trial: extend while below the trial's reduction (instead of while productive)") \
  X(bvaretries, 8, 0, 1000000, "BVA: a literal is matched again after a replacement at most this many times in a row") \
  X(bvarequeue, 0, 0, 1, "BVA (plain order): the literals of each fresh variable join the end of the round's queue, so factored clauses are factored again") \
  X(bvadecide, 0, 0, 1, "variables added by BVA are decided last (0: first, as the newest in the decision queue)") \
  X(bvasearch, 1, 0, 1, "BVA also in later elimination rounds, after the eliminations, on literals of touched variables (only if the first round added variables); elimination keeps BVA variables unless that removes clauses") \
  X(bvasearcheffort, 50, 1, 100000, "--bvasearch: BVA effort per round relative to search ticks since the last round (per mille)") \
  X(congruence, 1, 0, 1, "congruence closure on AND gates in elimination rounds")                 \
  X(congruencecost, 2000000, 0, INT32_MAX, "congruence: a round of 64M work units or more is productive only below this many per equivalence found (0: any equivalence)") \
  X(simeq, 1, 0, 1, "equivalences proposed by random simulation of AND gates, proven by Kitten")   \
  X(simeqticks, 50000, 1, INT32_MAX, "simulation pass budget (thousands of ticks)")             \
  X(simeqconst, 1, 0, 1, "simulation: also check variables that were constant in every vector")      \
  X(simeqite, 0, 0, 1, "simulation: if-then-else gates too")                                   \
  X(simeqdepth, 16, 1, 64, "depth of the fan-in windows that prove simulation candidates")          \
  X(cardinality, 0, 0, 2, "detect cardinality constraints, statistics only (1: before search, 2: also after the first elimination round)") \
  X(cardinalityeffort, 100, 1, 100000, "cardinality detection budget per phase in millions of work units") \
  X(counting, 1, 0, 1, "counting certificates before search: pigeonhole / parity / Count^3 / clique-colouring get PR clauses (DPR proof)") \
  X(countingeffort, 2000, 1, 1000000, "counting certificates: budget of a structure in millions of work units") \
  X(countingprobe, 0, 0, 1, "counting: also at-most-one constraints over auxiliary variables (exclusions by read-only probing)") \
  X(countingfault, 0, 0, INT32_MAX, "debugging: the k-th counting PR step gets a wrong witness (its check must refuse it)") \
  X(congruenceclosure, 1, 0, 1, "AND gate congruence to a fixpoint per call (union-find, re-hashing)")   \
  X(congruencerewrite, 0, 0, 1, "congruence closure rewrites degenerate gates instead of dropping them: x + x + R = R in XORs, ITE(c, t, -t) as an XOR, ITE(c, c, e) / ITE(c, t, c) / ITE(c, t, -c) as AND gates") \
  X(congruencegates, 1, 0, 1, "XOR and ITE gates join the congruence closure (else matched pairwise after it)") \
  X(congruencetern, 0, 0, 2, "before each congruence call: binary resolvents of ternary clause pairs (a b c) (a b -c), which subsume both (substitution into XOR encodings leaves such pairs); 2: the ternary clauses are kept (gates use them)") \
  X(dedup, 1, 0, 1, "remove duplicate binary clauses after substitution")                         \
  X(binpairunits, 0, 0, 2, "elimination rounds start with the units of binary clause pairs (a b) (a -b) (2: binary clauses include the resolvents of ternary pairs (a b c) (a b -c))") \
  X(gauss, 1, 0, 1, "XORs from complete clause encodings: a detached Gauss-Jordan solver (no proof) looks for a model") \
  X(gaussmin, 100, 0, 1000, "Gauss-Jordan only if XOR encodings cover this many per mille of the clauses") \
  X(gaussxors, 16, 1, INT32_MAX, "Gauss-Jordan only with at least this many XORs")                      \
  X(gaussmaxsize, 6, 2, 8, "largest XOR extracted (its encoding has 2^(size-1) clauses)")              \
  X(gausseffort, 1000, 1, 100000, "largest detached Gauss-Jordan solver effort relative to search ticks (per mille)") \
  X(gaussadapt, 1, 0, 1, "adaptive detached solver share: from 1/8 of gausseffort, doubled or halved by its Gauss-Jordan conflicts, stopped below 1/64") \
  X(gaussgrow, 100, 0, 1000, "double the share when this many per mille of the detached solver's conflicts are Gauss-Jordan conflicts") \
  X(gaussshrink, 10, 0, 1000, "halve the share when fewer than this many per mille are") \
  X(gaussinit, 20000, 0, INT32_MAX, "detached solver budget before search (thousands of ticks)")      \
  X(gaussint, 20000, 1, INT32_MAX, "search ticks between detached solver rounds (thousands)")         \
  X(gaussproof, 1, 0, 1, "refute inconsistent XORs before search (Gaussian elimination, DRAT proof with extension variables)") \
  X(xorsub, 1, 0, 1, "XOR-substitution reversal before search: variables replaced by the XOR of 2 or 3 variables, with a proof") \
  X(xorsubmin, 100, 0, 1000, "XOR-substitution reversal only if the expansions are this many per mille of the clauses") \
  X(linmod, 1, 0, 1, "linear equations mod 3, 5 or 7 on one-hot domains (exactly-one clauses + forbidden-tuple clauses): Gaussian elimination over GF(p) before search, its solution tried as a model (no proof: an inconsistent system is only counted)") \
  X(linmodmin, 500, 0, 1000, "--linmod: only if the domains and equations cover this many per mille of the clauses") \
  X(gaussfacts, 0, 0, 2, "root units and equivalences the XOR echelon form implies: 1 count, 2 also add them (experiment, only without a proof)") \
  X(gaussproofsize, 1000, 0, INT32_MAX, "largest refutation (thousands of chain positions; about 250 bytes of proof each)") \
  X(gaussdecide, 1, 0, 1, "detached solver: decide variables outside the XOR matrices first (the rest is linear)") \
  X(gaussmatrix, 64, 1, 4096, "largest Gauss-Jordan matrix (millions of bits, rows x columns)")        \
  X(gausswords, 64, 1, 4096, "copy the formula for the detached solver only up to this size (millions of words)") \
  X(vivify, 1, 0, 1, "vivification of learned and irredundant clauses")                         \
  X(vivifyint, 2000, 10, INT32_MAX, "base interval between vivification rounds (conflicts)")      \
  X(vivifyeffort, 100, 1, 100000, "vivification effort relative to search ticks (per mille)")     \
  X(vivifyirred, 1, 0, 1, "also vivify irredundant clauses")                                      \
  X(vivifytier3, 0, 0, 1, "also vivify tier3 learned clauses (lowest glue first, as all candidates)") \
  X(vivifyinst, 0, 0, 1, "vivification instantiation: last literal true, a conflict removes it (Kissat)") \
  X(vivifyimplied, 0, 0, 1, "vivification deletes learned clauses implied by others (Kissat)")        \
  X(vivifysort, 1, 0, 2, "vivification decides literals by their occurrences in all clauses: 1 for irredundant clauses, 2 for all (0: among the candidates)") \
  X(vivifysubsume, 1, 0, 1, "vivification deletes clauses that the conflicting (or implying) clause subsumes instead of adding a copy of it") \
  X(vivifyasym, 0, 0, 1, "vivification deletes irredundant clauses implied by the other irredundant ones") \
  X(vivifytier1, 0, 0, 100000, "tier1 learned clauses (glue <= tier1 or kept) get a vivification pass of their own each round with this effort in per mille of the search ticks (besides --vivifyeffort), every tier1 clause tried once before any is tried again; tier2 then has the learned share of --vivifyeffort to itself, in turns of its own (0: tier1 and tier2 share one pass whose turns restart only when every clause of both had one)") \
  X(probe, 1, 0, 1, "failed literal probing on binary implication graph roots (vivify rounds)")  \
  X(probeuip, 0, 0, 1, "a failed probe learns its first unique implication point (not the probe)")   \
  X(unhide, 0, 0, 1, "unhiding: binary implication graph stamps (failed literals, transitive, hidden tautologies and literals)") \
  X(unhideeffort, 20, 1, 100000, "unhiding effort in per mille of search ticks (vivify rounds)")       \
  X(binstats, 0, 0, 1, "statistics: with --reportmem a census of the learned binary clauses at every progress line (duplicates, transitive, unused) and the watches propagation visited by kind (the search is the same, a little slower)") \
  X(dumpsimplified, 0, 0, INT32_MAX, "debugging: at the first root-level decision after N - 1 conflicts (1: before the first decision), write the irredundant formula (root units, binary and long clauses, internal numbering) as DIMACS to the file named by PSAT_DUMP (default simplified.cnf) and stop") \
  X(propstats, 0, 0, 2, "statistics: with --reportmem a line on search propagation at every progress line (time share, ticks, watches and clause visits per propagation, blocker hits, visit outcomes and implications by tier, saved-phase quartiles; 2: also cache models; the search is the same, slower)") \
  X(binreduce, 0, 0, 1, "transitive reduction of the learned binary clauses in vivification rounds: one implied by the other binary clauses (a path in the binary implication graph) is deleted") \
  X(binreduceeffort, 10, 1, 100000, "--binreduce effort in per mille of search ticks") \
  X(binreducenodes, 100, 2, 1000000, "--binreduce: most literals a breadth-first search for a path visits") \
  X(sweep, 1, 0, 1, "sweeping: backbones and equivalences in variable environments (Kitten)")    \
  X(sweepeffort, 1000, 1, 100000, "sweeping effort in per mille of search ticks")                \
  X(sweepdepth, 2, 0, 8, "environment depth (clause steps from the swept variable)")            \
  X(sweepvars, 128, 2, 8192, "most variables in an environment")                                \
  X(sweepclauses, 1024, 2, 65536, "most clauses in an environment")                             \
  X(sweepgrow, 1, 0, 1, "sweep environments grow after a full cycle that found little")                \
  X(sweepgrowmax, 3, 0, 8, "most growth steps of the sweep environment limits")                         \
  X(sweepgrowcheck, 0, 0, 1000000, "sweep environments grow after this many swept variables that found little (0: after a full cycle)") \
  X(sweepsubst, 0, 0, 1, "substitute the equivalences sweeping found right away (not at the next elimination)") \
  X(sweepclasses, 1, 0, 1, "sweeping checks equivalences within classes of all environment literals (Kissat)") \
  X(sweepknown, 1, 0, 2, "sweeping skips equivalences whose binary clauses are in the formula (2: also keeps proved ones out of the candidates until substituted)") \
  X(sweepphase, 1, 0, 1, "sweeping: Kitten decides backbone candidates false and the members of each candidate class with alternating values (0: random phases)") \
  X(sweepqueue, 1, 0, 1, "sweeping: Kitten decides from a move-to-front queue (0: score heap)") \
  X(sweepbackbone, 1, 0, 1, "sweeping checks backbone candidates with Kitten (0: only the units Kitten learns)") \
  X(sweepouter, 1, 0, 1, "sweeping checks equivalences between two outermost environment literals (0: only with an inner one)") \
  X(sweepfollow, 0, 0, 1, "sweeping sweeps a variable again right after an equivalence with it was proved") \
  X(sweeporder, 0, 0, 3, "order of the swept variables: 0 index, 1 reverse index, 2 most long-clause occurrences first, 3 fewest first (more than --sweepclauses in a polarity: last; each sweep sorts again)") \
  X(sweepdirty, 0, 0, 1, "sweeping skips variables whose clauses did not change since they were swept (while others remain)") \
  X(binaryproof, 1, 0, 1, "write the DRAT proof in binary format")                                \
  X(strict, 1, 0, 1, "strict DIMACS parsing")

struct Options {
#define PSAT_OPTION_FIELD(name, def, lo, hi, desc) int64_t name = def;
  PSAT_OPTIONS(PSAT_OPTION_FIELD)
#undef PSAT_OPTION_FIELD

  // Sets an option by name; returns false for unknown names. Throws std::invalid_argument for
  // out-of-range or malformed values.
  bool set(const std::string& name, const std::string& value);
  bool has(const std::string& name) const;
  // Prints all options with defaults and descriptions (for --help).
  static void print_help(std::FILE* out);
  // Prints the options that differ from their defaults as 'c' comment lines.
  void print_changed(std::FILE* out) const;
};

}  // namespace psat
