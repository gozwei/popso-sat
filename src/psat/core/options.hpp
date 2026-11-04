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
  X(verbose, 0, 0, 3, "verbosity level")                                                          \
  X(check, 1, 0, 1, "check a SAT model against the original formula before reporting it")         \
  X(invariants, 0, 0, 1, "debugging: check watch / elimination invariants after inprocessing")   \
  X(stable, 1, 0, 2, "search mode: 0 = focused only, 1 = switch focused/stable, 2 = stable only") \
  X(modeinit, 1000, 10, INT32_MAX, "conflicts before the first mode switch")                      \
  X(modegrowth, 200, 100, 1000, "growth of the mode length in ticks per focused+stable pair (%)") \
  X(restartint, 1, 1, 10000, "minimum conflicts between focused-mode restarts")                   \
  X(restartmargin, 10, 0, 100, "fast glue average above slow one by this much restarts (%)")      \
  X(emafast, 33, 1, 1000, "window of the fast glue moving average (conflicts)")                   \
  X(emaslow, 100000, 100, 10000000, "window of the slow glue moving average (conflicts)")         \
  X(reluctant, 1, 0, 1, "reluctant doubling (Luby) restarts in stable mode")                      \
  X(reluctantint, 1024, 1, 1 << 20, "base interval of reluctant doubling (conflicts)")            \
  X(reluctantlim, 1048576, 1, 1 << 30, "largest reluctant doubling interval (conflicts)")         \
  X(reduceint, 1000, 10, 1000000, "base reduce interval (scaled by sqrt(reductions))")            \
  X(reducefraction, 75, 10, 100, "fraction of reduce candidates removed (%)")                     \
  X(tier1, 2, 1, 100, "glue limit of tier1 (kept) learned clauses")                               \
  X(tier2, 6, 1, 1000, "glue limit of tier2 (kept while used) learned clauses")                   \
  X(dynamictiers, 0, 0, 1, "tier limits from glue quantiles of used clauses (Kissat 4)")          \
  X(tier1quantile, 50, 1, 99, "dynamic tier1: share of used clauses with glue <= tier1 (%)")      \
  X(tier2quantile, 90, 1, 99, "dynamic tier2: share of used clauses with glue <= tier2 (%)")      \
  X(minimize, 1, 0, 1, "recursive learned clause minimization")                                   \
  X(minimizedepth, 1000, 1, 100000, "recursion depth limit of minimization")                      \
  X(shrink, 0, 0, 1, "shrink learned clauses to block UIPs per level (Fleury & Biere 2021)")     \
  X(phase, 1, 0, 1, "initial decision phase (1 = true)")                                          \
  X(target, 1, 0, 2, "target phases: 0 = off, 1 = stable mode, 2 = always")                       \
  X(rephase, 1, 0, 1, "periodic rephasing (best / original / inverted phases)")                   \
  X(rephaseint, 1000, 10, 1000000, "base rephase interval (conflicts)")                           \
  X(walk, 1, 0, 1, "local search (ProbSAT walk) phases in the rephase cycle")                    \
  X(lucky, 1, 0, 1, "try trivial assignments (all false / all true, both orders) before search")  \
  X(walkeffort, 50, 1, 100000, "walk effort relative to search ticks (per mille)")               \
  X(decay, 50, 1, 200, "EVSIDS score decay (per mille)")                                          \
  X(bumpreasons, 1, 0, 1, "also bump variables in reasons of learned clause literals")           \
  X(bumpreasonslimit, 100, 1, 100000, "skip reason bumping for learned clauses longer than this")   \
  X(chrono, 0, 0, 1, "chronological backtracking (not implemented yet)")                          \
  X(eliminate, 1, 0, 1, "bounded variable elimination rounds (pre- and inprocessing)")             \
  X(eliminateinit, 0, 0, INT32_MAX, "conflicts before the first round (0 = preprocess)")          \
  X(eliminateint, 2000, 10, INT32_MAX, "base interval between elimination rounds (conflicts)")    \
  X(eliminatebound, 16, 0, 1024, "largest clause-count increase allowed per eliminated variable") \
  X(eliminateclslim, 100, 2, 100000, "largest resolvent size")                                   \
  X(eliminategates, 1, 0, 1, "AND-gate / equivalence definitions in elimination")                 \
  X(definitions, 0, 0, 1, "semantic definitions in elimination (unsat cores by Kitten)")        \
  X(definitionticks, 2000, 10, 1000000, "Kitten ticks per definition attempt")                  \
  X(eliminateocclim, 1000, 1, 1000000, "skip variables with more occurrences in one polarity")    \
  X(eliminateeffort, 100, 1, 100000, "elimination effort relative to search ticks (per mille)")   \
  X(subsume, 1, 0, 1, "forward subsumption and strengthening in elimination rounds")              \
  X(subsumeeffort, 100, 1, 100000, "forward subsumption effort per round in percent of the default") \
  X(eagersubsume, 20, 0, 100, "learned clauses checked for subsumption by each new learned clause") \
  X(substitute, 1, 0, 1, "equivalent literal substitution (SCCs of binary implications)")         \
  X(bva, 0, 0, 1, "bounded variable addition in elimination rounds")                             \
  X(congruence, 1, 0, 1, "congruence closure on AND gates in elimination rounds")                 \
  X(vivify, 1, 0, 1, "vivification of learned and irredundant clauses")                         \
  X(vivifyint, 2000, 10, INT32_MAX, "base interval between vivification rounds (conflicts)")      \
  X(vivifyeffort, 100, 1, 100000, "vivification effort relative to search ticks (per mille)")     \
  X(vivifyirred, 1, 0, 1, "also vivify irredundant clauses")                                      \
  X(probe, 1, 0, 1, "failed literal probing on binary implication graph roots (vivify rounds)")  \
  X(sweep, 0, 0, 1, "sweeping: backbones and equivalences in variable environments (Kitten)")    \
  X(sweepeffort, 100, 1, 100000, "sweeping effort in per mille of search ticks")                \
  X(sweepdepth, 2, 0, 8, "environment depth (clause steps from the swept variable)")            \
  X(sweepvars, 128, 2, 8192, "most variables in an environment")                                \
  X(sweepclauses, 1024, 2, 65536, "most clauses in an environment")                             \
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
