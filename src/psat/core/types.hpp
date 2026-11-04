#pragma once
// Basic types. Variables are 0-based internally (DIMACS variable v is internal variable v - 1);
// a literal is 2 * var + sign, sign 1 meaning negative.

#include <cstdint>

namespace psat {

using Var = uint32_t;
using Lit = uint32_t;

constexpr Lit kNoLit = UINT32_MAX;
// Largest DIMACS variable index accepted (literals and binary-reason tags need the top bit).
constexpr int kMaxVar = (1 << 28) - 1;

inline constexpr Lit make_lit(Var v, bool negative) { return 2 * v + (negative ? 1u : 0u); }
inline constexpr Var var_of(Lit l) { return l >> 1; }
inline constexpr bool is_negative(Lit l) { return (l & 1) != 0; }
inline constexpr Lit negate(Lit l) { return l ^ 1; }

inline constexpr Lit from_dimacs(int d) {
  return d > 0 ? 2 * static_cast<Lit>(d - 1) : 2 * static_cast<Lit>(-d - 1) + 1;
}
inline constexpr int to_dimacs(Lit l) {
  const int v = static_cast<int>(var_of(l)) + 1;
  return is_negative(l) ? -v : v;
}

// Solve results, with the SAT Competition exit codes.
enum Result : int { kUnknown = 0, kSat = 10, kUnsat = 20 };

}  // namespace psat
