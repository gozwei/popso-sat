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
  X(minimize, 1, 0, 1, "recursive learned clause minimization")                                   \
  X(minimizedepth, 1000, 1, 100000, "recursion depth limit of minimization")                      \
  X(phase, 1, 0, 1, "initial decision phase (1 = true)")                                          \
  X(target, 1, 0, 2, "target phases: 0 = off, 1 = stable mode, 2 = always")                       \
  X(rephase, 1, 0, 1, "periodic rephasing (best / original / inverted phases)")                   \
  X(rephaseint, 1000, 10, 1000000, "base rephase interval (conflicts)")                           \
  X(decay, 50, 1, 200, "EVSIDS score decay (per mille)")                                          \
  X(bumpreasons, 1, 0, 1, "also bump variables in reasons of learned clause literals")           \
  X(bumpreasonslimit, 100, 1, 100000, "skip reason bumping for learned clauses longer than this")   \
  X(chrono, 0, 0, 1, "chronological backtracking (not implemented yet)")                          \
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
