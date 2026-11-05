#pragma once
// DRAT proof writer (text or binary format), buffered.
//
// Binary DRAT: 'a' or 'd', then each literal l as an unsigned varint (7 bits per byte, low bits
// first, high bit = more bytes) of 2 * |l| + (l < 0), then a 0 byte. Text DRAT: "1 -2 0" lines,
// deletions prefixed by "d ". Literals are written in DIMACS numbering.

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
  void add(const Lit* lits, size_t n) { line(false, lits, n); }
  void del(const Lit* lits, size_t n) { line(true, lits, n); }
  void add_unit(Lit l) { line(false, &l, 1); }
  void add_empty() { line(false, nullptr, 0); }

  // Hands the buffer to the sink. A sink that throws (write error, full disk) marks the proof as
  // failed: nothing more is written, and the caller must not claim unsatisfiability
  // (an incomplete proof is rejected; a SAT answer needs no proof, so solving goes on).
  void flush();
  bool failed() const { return failed_; }
  bool binary() const { return binary_; }
  uint64_t added() const { return added_; }
  uint64_t deleted() const { return deleted_; }
  uint64_t bytes() const { return bytes_; }

 private:
  void line(bool deletion, const Lit* lits, size_t n);
  void reserve(size_t n) {
    if (buf_.size() - pos_ < n) flush();
  }

  Sink sink_;
  bool binary_;
  std::vector<char> buf_;
  size_t pos_ = 0;
  bool failed_ = false;
  uint64_t added_ = 0, deleted_ = 0, bytes_ = 0;
};

}  // namespace psat
