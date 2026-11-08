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
#include <unordered_map>
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
  // Root-level strengthening: a clause of the formula lost the literals removed[0..m), all false at
  // the root, and lits[0..n) remain. Nothing is written: the checker keeps the longer clause, which
  // propagates as the shorter one does (its extra literals are false at the root there too), and
  // the next deletion of the shorter clause deletes the longer one. This saves an addition and a
  // deletion per clause and simplification round (most of the proof on formulas with long clauses
  // and units trickling in). Deletions are looked up only while such clauses exist.
  void shorten(const Lit* lits, size_t n, const Lit* removed, size_t m);
  // Deletes a clause from the proof before the solver does (one the checker no longer needs: it is
  // satisfied at the root, or subsumed by a clause in the formula); the solver's own deletion of
  // it later writes nothing. Checkers visit every clause of the formula for each RAT or PR step,
  // so the counting certificates drop their clauses this way as soon as they are done with them.
  void forget(const Lit* lits, size_t n);
  // Takes over the shortened and forgotten clauses of another writer whose lines were copied into
  // this one (raw), in the same numbering.
  void adopt(ProofWriter& other);

  // Hands the buffer to the sink. A sink that throws (write error, full disk) marks the proof as
  // failed: nothing more is written, and the caller must not claim unsatisfiability
  // (an incomplete proof is rejected; a SAT answer needs no proof, so solving goes on).
  void flush();
  // Literal renaming, for a solver working on renumbered variables: map[l] is the literal written
  // for its literal l, and literals beyond the map are written as they are (null: none).
  void set_map(const std::vector<Lit>* map) { map_ = map; }
  const std::vector<Lit>* map() const { return map_; }
  // Proof lines already encoded in this writer's format (the output of another writer), with
  // their counts and the bytes of their deletion lines.
  void raw(const char* data, size_t n, uint64_t added, uint64_t deleted, uint64_t pr, uint64_t deleted_bytes = 0);
  bool failed() const { return failed_; }
  bool binary() const { return binary_; }
  uint64_t added() const { return added_; }
  uint64_t deleted() const { return deleted_; }
  uint64_t pr() const { return pr_; }
  uint64_t bytes() const { return bytes_; }
  // Bytes encoded for deletion lines (written or not).
  uint64_t deleted_bytes() const { return deleted_bytes_; }
  // Memory for the clauses kept by shorten and forget (estimated per entry: node, bucket, removed
  // literals). Beyond this budget, shorten writes the addition and the deletion, and forget does
  // nothing. Default 256 MB.
  void set_shorten_budget(size_t bytes) { longer_budget_ = bytes; }
  // Root-level strengthenings not written (shorten), clauses deleted early (forget), and entries
  // of either kind not yet matched by a deletion of the solver's.
  uint64_t shortened() const { return shortened_; }
  uint64_t forgotten() const { return forgotten_; }
  size_t shortened_live() const { return longer_.size(); }

  // Statistics by source: the caller tags lines with a source (0 .. kSources - 1) and reads the
  // lines added and deleted and the bytes encoded for each (all lines, and deletion lines).
  static constexpr int kSources = 24;
  struct SourceStats {
    uint64_t added = 0, deleted = 0, bytes = 0, deleted_bytes = 0;
  };
  int source() const { return source_; }
  void set_source(int s) { source_ = s; }
  const SourceStats& source_stats(int s) const { return src_[s]; }

 private:
  // One proof line: the literals a[0..n) then b[0..m) (the witness of a PR line, else empty).
  void line(bool deletion, const Lit* a, size_t n, const Lit* b, size_t m);
  void encode(bool deletion, const Lit* a, size_t n, const Lit* b, size_t m);
  uint64_t encoded() const { return handed_ + pos_; }
  void put_binary(Lit l);
  void put_text(Lit l);
  void reserve(size_t n) {
    if (buf_.size() - pos_ < n) flush();
  }
  // Shortened clauses (see shorten) and clauses deleted early (forget), by an order-independent
  // hash of their literals: a second hash and the size confirm a match. For a shortened clause,
  // `removed` holds the literals the checker's clause has beyond them (sorted).
  struct Longer {
    uint64_t check;
    uint32_t size;
    bool gone;  // deleted early: the solver's deletion writes nothing
    std::vector<Lit> removed;
  };
  static void hashes(const Lit* lits, size_t n, uint64_t& key, uint64_t& check);
  // The entry for the clause lits[0..n) (taken out of the map), or false.
  bool take_longer(const Lit* lits, size_t n, std::vector<Lit>& removed, bool& gone);
  void put_longer(uint64_t key, Longer&& entry);
  static size_t longer_bytes(const Longer& e) { return 112 + sizeof(Lit) * e.removed.size(); }
  size_t longer_bytes_ = 0, longer_budget_ = size_t{256} << 20;
  // Applies the literal map to a[0..n) into out.
  void map_into(const Lit* a, size_t n, std::vector<Lit>& out) const;

  Sink sink_;
  bool binary_;
  std::vector<char> buf_;
  size_t pos_ = 0;
  bool failed_ = false;
  uint64_t added_ = 0, deleted_ = 0, pr_ = 0, bytes_ = 0, deleted_bytes_ = 0;
  uint64_t handed_ = 0;  // bytes taken from the buffer by flush() (written or not)
  int source_ = 0;
  SourceStats src_[kSources];
  const std::vector<Lit>* map_ = nullptr;
  std::vector<Lit> mapped_;
  std::unordered_multimap<uint64_t, Longer> longer_;
  uint64_t shortened_ = 0, forgotten_ = 0;
  std::vector<Lit> longer_tmp_, removed_tmp_;
};

}  // namespace psat
