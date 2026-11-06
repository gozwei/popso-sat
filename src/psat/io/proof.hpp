#pragma once
// DRAT / DPR proof writer (text or binary format), buffered.
//
// Binary DRAT: 'a' or 'd', then each literal l as an unsigned varint (7 bits per byte, low bits
// first, high bit = more bytes) of 2 * |l| + (l < 0), then a 0 byte. Text DRAT: "1 -2 0" lines,
// deletions prefixed by "d ". Literals are written in DIMACS numbering.
//
// PR lines (DPR, checked by dpr-trim): the clause, then the witness, whose first literal repeats
// the clause's first literal; the checker splits the line at that repetition. The same layout
// works in both formats: a binary PR line is one 'a' record holding the clause and the witness.

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <string>
#include <vector>

#include "psat/core/types.hpp"

namespace psat {

class ProofWriter {
 public:
  using Sink = std::function<void(const char* data, size_t n)>;

  ProofWriter(Sink sink, bool binary);
  // Writes to a file opened by the caller (not closed here).
  ProofWriter(std::FILE* file, bool binary);
  ~ProofWriter();
  ProofWriter(const ProofWriter&) = delete;
  ProofWriter& operator=(const ProofWriter&) = delete;

  // Internal literals (2 * var + sign).
  void add(const Lit* lits, size_t n) { line(false, lits, n, nullptr, 0); }
  void del(const Lit* lits, size_t n) { line(true, lits, n, nullptr, 0); }
  void add_unit(Lit l) { line(false, &l, 1, nullptr, 0); }
  void add_empty() { line(false, nullptr, 0, nullptr, 0); }
  // A PR clause with its witness (a consistent set of literals that satisfies the clause). The
  // caller guarantees witness[0] == lits[0] and that neither the rest of the clause nor the rest
  // of the witness repeats lits[0] (the checker splits the line at the last repetition).
  void add_pr(const Lit* lits, size_t n, const Lit* witness, size_t m) { line(false, lits, n, witness, m); }

  // Hands the buffer to the sink. A sink that throws (write error, full disk) marks the proof as
  // failed: nothing more is written, and the caller must not claim unsatisfiability
  // (an incomplete proof is rejected; a SAT answer needs no proof, so solving goes on).
  void flush();
  // Literal renaming, for a solver working on renumbered variables: map[l] is the literal written
  // for its literal l (null: none).
  void set_map(const std::vector<Lit>* map) { map_ = map; }
  // Proof lines already encoded in this writer's format (the output of another writer), with
  // their counts.
  void raw(const char* data, size_t n, uint64_t added, uint64_t deleted, uint64_t pr);
  bool failed() const { return failed_; }
  bool binary() const { return binary_; }
  uint64_t added() const { return added_; }
  uint64_t deleted() const { return deleted_; }
  uint64_t pr() const { return pr_; }
  uint64_t bytes() const { return bytes_; }

 private:
  // One proof line: the literals a[0..n) then b[0..m) (the witness of a PR line, else empty).
  void line(bool deletion, const Lit* a, size_t n, const Lit* b, size_t m);
  void put_binary(Lit l);
  void put_text(Lit l);
  void reserve(size_t n) {
    if (buf_.size() - pos_ < n) flush();
  }

  Sink sink_;
  bool binary_;
  std::vector<char> buf_;
  size_t pos_ = 0;
  bool failed_ = false;
  uint64_t added_ = 0, deleted_ = 0, pr_ = 0, bytes_ = 0;
  const std::vector<Lit>* map_ = nullptr;
  std::vector<Lit> mapped_;
};

}  // namespace psat
