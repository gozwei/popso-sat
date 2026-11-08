#include "psat/io/proof.hpp"

#include <algorithm>
#include <stdexcept>

namespace psat {

namespace {
constexpr size_t kBufferSize = size_t{1} << 20;

// Binary DRAT literal: varint of 2 * |l| + (l < 0), at most 5 bytes for 28-bit variables.
inline char* put_varint(char* out, Lit l) {
  uint32_t u = 2 * (var_of(l) + 1) + (is_negative(l) ? 1 : 0);
  while (u > 127) {
    *out++ = static_cast<char>((u & 127) | 128);
    u >>= 7;
  }
  *out++ = static_cast<char>(u);
  return out;
}
}  // namespace

ProofWriter::ProofWriter(Sink sink, bool binary) : sink_(std::move(sink)), binary_(binary), buf_(kBufferSize) {}

ProofWriter::ProofWriter(std::FILE* file, bool binary)
    : ProofWriter(
          [file](const char* data, size_t n) {
            if (std::fwrite(data, 1, n, file) != n) throw std::runtime_error("proof: write error");
          },
          binary) {}

ProofWriter::~ProofWriter() { flush(); }

void ProofWriter::flush() {
  if (pos_ == 0) return;
  if (!failed_) {
    try {
      sink_(buf_.data(), pos_);
      bytes_ += pos_;
    } catch (...) {
      failed_ = true;
    }
  }
  handed_ += pos_;
  pos_ = 0;
}

void ProofWriter::put_binary(Lit l) {
  reserve(5);
  pos_ = static_cast<size_t>(put_varint(buf_.data() + pos_, l) - buf_.data());
}

void ProofWriter::put_text(Lit l) {
  reserve(13);
  int d = to_dimacs(l);
  char tmp[12];
  int k = 0;
  const bool neg = d < 0;
  unsigned u = static_cast<unsigned>(neg ? -d : d);
  do {
    tmp[k++] = static_cast<char>('0' + u % 10);
    u /= 10;
  } while (u);
  if (neg) buf_[pos_++] = '-';
  while (k) buf_[pos_++] = tmp[--k];
  buf_[pos_++] = ' ';
}

void ProofWriter::raw(const char* data, size_t n, uint64_t added, uint64_t deleted, uint64_t pr, uint64_t deleted_bytes) {
  added_ += added;
  deleted_ += deleted;
  pr_ += pr;
  deleted_bytes_ += deleted_bytes;
  src_[source_].added += added;
  src_[source_].deleted += deleted;
  src_[source_].bytes += n;
  src_[source_].deleted_bytes += deleted_bytes;
  while (n) {
    if (pos_ == buf_.size()) flush();
    const size_t k = std::min(n, buf_.size() - pos_);
    std::copy(data, data + k, buf_.data() + pos_);
    pos_ += k;
    data += k;
    n -= k;
  }
}

namespace {
inline uint64_t mix64(uint64_t x) {
  x ^= x >> 30;
  x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27;
  x *= 0x94d049bb133111ebULL;
  x ^= x >> 31;
  return x;
}
}  // namespace

void ProofWriter::hashes(const Lit* lits, size_t n, uint64_t& key, uint64_t& check) {
  key = n;
  check = n << 32;
  for (size_t i = 0; i < n; ++i) {
    key += mix64(lits[i] + 0x9e3779b97f4a7c15ULL);
    check += mix64((uint64_t{lits[i]} << 1) ^ 0x632be59bd9b4e019ULL);
  }
}

bool ProofWriter::take_longer(const Lit* lits, size_t n, std::vector<Lit>& removed, bool& gone) {
  uint64_t key, check;
  hashes(lits, n, key, check);
  auto [it, end] = longer_.equal_range(key);
  for (; it != end; ++it) {
    if (it->second.size != n || it->second.check != check) continue;
    longer_bytes_ -= longer_bytes(it->second);
    removed = std::move(it->second.removed);
    gone = it->second.gone;
    longer_.erase(it);
    return true;
  }
  return false;
}

void ProofWriter::put_longer(uint64_t key, Longer&& entry) {
  longer_bytes_ += longer_bytes(entry);
  longer_.emplace(key, std::move(entry));
}

void ProofWriter::map_into(const Lit* a, size_t n, std::vector<Lit>& out) const {
  out.clear();
  if (!map_) {
    out.assign(a, a + n);
    return;
  }
  const std::vector<Lit>& map = *map_;
  for (size_t i = 0; i < n; ++i) out.push_back(a[i] < map.size() ? map[a[i]] : a[i]);
}

void ProofWriter::shorten(const Lit* lits, size_t n, const Lit* removed, size_t m) {
  if (longer_bytes_ >= longer_budget_) {  // (the longer clause may be an entry: del finds it)
    std::vector<Lit> old(lits, lits + n);
    old.insert(old.end(), removed, removed + m);
    add(lits, n);
    del(old.data(), old.size());
    return;
  }
  ++shortened_;
  // The clause before: lits and removed (in the writer's numbering). If it was a shortened clause
  // itself, the checker's clause has its removed literals too.
  std::vector<Lit> kept, before;
  map_into(lits, n, kept);
  map_into(removed, m, before);
  Longer entry;
  entry.gone = false;
  entry.removed = before;
  before.insert(before.begin(), kept.begin(), kept.end());
  std::vector<Lit> older;
  bool gone = false;
  if (!longer_.empty() && take_longer(before.data(), before.size(), older, gone)) {
    if (gone) {  // (the checker has no such clause: nor will it have the shorter one)
      entry.gone = true;
      entry.removed.clear();
    } else {
      entry.removed.insert(entry.removed.end(), older.begin(), older.end());
    }
  }
  std::sort(entry.removed.begin(), entry.removed.end());
  uint64_t key;
  hashes(kept.data(), kept.size(), key, entry.check);
  entry.size = static_cast<uint32_t>(kept.size());
  put_longer(key, std::move(entry));
}

void ProofWriter::forget(const Lit* lits, size_t n) {
  if (longer_bytes_ >= longer_budget_) return;  // (the clause stays until the solver deletes it)
  del(lits, n);
  ++forgotten_;
  Longer entry;
  entry.gone = true;
  std::vector<Lit> mapped;
  map_into(lits, n, mapped);
  uint64_t key;
  hashes(mapped.data(), mapped.size(), key, entry.check);
  entry.size = static_cast<uint32_t>(mapped.size());
  put_longer(key, std::move(entry));
}

void ProofWriter::adopt(ProofWriter& other) {
  for (auto& [key, entry] : other.longer_) put_longer(key, std::move(entry));
  other.longer_.clear();
  other.longer_bytes_ = 0;
  shortened_ += other.shortened_;
  forgotten_ += other.forgotten_;
}

void ProofWriter::line(bool deletion, const Lit* a, size_t n, const Lit* b, size_t m) {
  if (map_) {
    mapped_.clear();
    const std::vector<Lit>& map = *map_;
    for (size_t i = 0; i < n; ++i) mapped_.push_back(a[i] < map.size() ? map[a[i]] : a[i]);
    for (size_t i = 0; i < m; ++i) mapped_.push_back(b[i] < map.size() ? map[b[i]] : b[i]);
    const std::vector<Lit>* saved = map_;
    map_ = nullptr;
    line(deletion, mapped_.data(), n, mapped_.data() + n, m);
    map_ = saved;
    return;
  }
  bool gone = false;
  if (deletion && !longer_.empty() && take_longer(a, n, removed_tmp_, gone)) {
    if (gone) return;  // deleted early (forget)
    // The checker has the longer clause (see shorten).
    longer_tmp_.assign(a, a + n);
    longer_tmp_.insert(longer_tmp_.end(), removed_tmp_.begin(), removed_tmp_.end());
    a = longer_tmp_.data();
    n = longer_tmp_.size();
  }
  if (deletion) {
    ++deleted_;
    ++src_[source_].deleted;
  } else {
    ++added_;
    ++src_[source_].added;
  }
  if (m) ++pr_;
  const uint64_t before = encoded();
  encode(deletion, a, n, b, m);
  const uint64_t k = encoded() - before;
  src_[source_].bytes += k;
  if (deletion) {
    src_[source_].deleted_bytes += k;
    deleted_bytes_ += k;
  }
}

void ProofWriter::encode(bool deletion, const Lit* a, size_t n, const Lit* b, size_t m) {
  if (binary_) {
    if (n + m <= 1024) {
      reserve(2 + 5 * (n + m));
      char* out = buf_.data() + pos_;
      *out++ = deletion ? 'd' : 'a';
      for (size_t i = 0; i < n; ++i) out = put_varint(out, a[i]);
      for (size_t i = 0; i < m; ++i) out = put_varint(out, b[i]);
      *out++ = 0;
      pos_ = static_cast<size_t>(out - buf_.data());
      return;
    }
    // Long clause: write piecewise.
    reserve(1);
    buf_[pos_++] = deletion ? 'd' : 'a';
    for (size_t i = 0; i < n; ++i) put_binary(a[i]);
    for (size_t i = 0; i < m; ++i) put_binary(b[i]);
    reserve(1);
    buf_[pos_++] = 0;
    return;
  }
  if (deletion) {
    reserve(2);
    buf_[pos_++] = 'd';
    buf_[pos_++] = ' ';
  }
  for (size_t i = 0; i < n; ++i) put_text(a[i]);
  for (size_t i = 0; i < m; ++i) put_text(b[i]);
  reserve(2);
  buf_[pos_++] = '0';
  buf_[pos_++] = '\n';
}

}  // namespace psat
