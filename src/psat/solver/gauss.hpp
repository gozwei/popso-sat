#pragma once
// Gauss-Jordan elimination on XOR constraints (--gauss): data structures.
//
// XOR constraints are extracted from complete clause encodings (gauss.cpp). Each connected
// component of XORs (sharing variables) becomes one GF(2) matrix with one bit-packed row per XOR
// and one column per variable. The matrix is kept in reduced row echelon form over its "basic"
// columns (one per row, appearing in no other row); propagation follows Han & Jiang (CAV 2012):
// every open row watches its basic column and one non-basic column, both unassigned; when the
// basic column is assigned and the row has another unassigned column, that column becomes basic
// (it is eliminated from every other row). Row operations only ever add rows, so the matrix is an
// equivalent system at every point and needs no undo on backtracking.

#include <cstdint>
#include <vector>

#include "psat/core/types.hpp"

namespace psat {

// XOR constraints vars[start[i] .. start[i + 1]) sum to rhs[i] over GF(2).
struct XorList {
  std::vector<Var> vars;
  std::vector<uint32_t> start{0};
  std::vector<uint8_t> rhs;
  uint64_t covered = 0;  // distinct irredundant clauses that are part of an XOR encoding
  uint64_t subsumed = 0;  // XORs with encoding clauses subsumed by binary clauses
  size_t size() const { return rhs.size(); }
  void push(const Var* v, uint32_t n, uint8_t parity) {
    vars.insert(vars.end(), v, v + n);
    start.push_back(static_cast<uint32_t>(vars.size()));
    rhs.push_back(parity);
  }
};

struct GaussMatrix {
  static constexpr uint32_t kNone = UINT32_MAX;
  uint32_t nrows = 0, ncols = 0, words = 0;
  std::vector<uint64_t> bits;         // nrows * words
  std::vector<uint8_t> rhs;           // per row
  std::vector<Var> col_var;           // column -> variable
  std::vector<uint32_t> basic;        // row -> basic column
  std::vector<uint32_t> basic_row;    // column -> row (kNone for non-basic columns)
  std::vector<uint32_t> watch;        // row -> watched non-basic column (kNone: closed row)
  std::vector<std::vector<uint32_t>> watchers;  // column -> rows that watched it (stale entries skipped)
  std::vector<uint64_t> assigned, values;       // per column: assigned in the solver's view, its value
  std::vector<uint8_t> queued;        // per row: in the solver's dirty queue

  uint64_t* row(uint32_t r) { return bits.data() + size_t{r} * words; }
  const uint64_t* row(uint32_t r) const { return bits.data() + size_t{r} * words; }
  static bool test(const uint64_t* b, uint32_t c) { return (b[c >> 6] >> (c & 63)) & 1u; }
  bool is_assigned(uint32_t c) const { return test(assigned.data(), c); }
};

struct GaussQueued {
  uint32_t matrix, row, trigger;
};

// A row found with at most one unassigned column (propagating, satisfied or conflicting) on a
// decision level: backtracking below that level reopens it.
struct GaussClosed {
  uint32_t level, matrix, row;
};

struct GaussStats {
  // Detection (main solver).
  uint64_t xors = 0, xor_sizes[9] = {}, covered = 0, clauses = 0, components = 0, subsumed = 0;
  uint64_t matrices = 0, matrix_rows = 0, matrix_cols = 0, skipped_matrices = 0, rank_deficit = 0;
  double detect_seconds = 0;
  // The detached solver (main solver view).
  uint64_t rounds = 0, sub_ticks = 0, sub_conflicts = 0;
  uint64_t share = 0, max_share = 0, grown = 0, shrunk = 0;  // adaptive share (per mille)
  bool stopped = false;  // the detached solver was stopped (Gauss-Jordan did too little)
  int sub_result = 0;
  bool gated = false, started = false, model = false;
  // Propagation (in the solver that runs Gauss-Jordan).
  uint64_t propagations = 0, conflicts = 0, pivots = 0, row_checks = 0, reopened = 0, root_units = 0;
  // Refutation of inconsistent XOR systems before search (main solver, with a DRAT proof).
  uint64_t refutations = 0, proof_lines = 0, proof_positions = 0, refute_aborted = 0;
};

}  // namespace psat
