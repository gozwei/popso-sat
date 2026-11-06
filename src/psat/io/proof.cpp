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

void ProofWriter::raw(const char* data, size_t n, uint64_t added, uint64_t deleted, uint64_t pr) {
  added_ += added;
  deleted_ += deleted;
  pr_ += pr;
  while (n) {
    if (pos_ == buf_.size()) flush();
    const size_t k = std::min(n, buf_.size() - pos_);
    std::copy(data, data + k, buf_.data() + pos_);
    pos_ += k;
    data += k;
    n -= k;
  }
}

void ProofWriter::line(bool deletion, const Lit* a, size_t n, const Lit* b, size_t m) {
  if (map_) {
    mapped_.clear();
    for (size_t i = 0; i < n; ++i) mapped_.push_back((*map_)[a[i]]);
    for (size_t i = 0; i < m; ++i) mapped_.push_back((*map_)[b[i]]);
    const std::vector<Lit>* map = map_;
    map_ = nullptr;
    line(deletion, mapped_.data(), n, mapped_.data() + n, m);
    map_ = map;
    return;
  }
  if (deletion) {
    ++deleted_;
  } else {
    ++added_;
  }
  if (m) ++pr_;
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
