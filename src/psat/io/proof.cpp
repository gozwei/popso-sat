#include "psat/io/proof.hpp"

#include <stdexcept>

namespace psat {

namespace {
constexpr size_t kBufferSize = size_t{1} << 20;
}

ProofWriter::ProofWriter(Sink sink, bool binary) : sink_(std::move(sink)), binary_(binary), buf_(kBufferSize) {}

ProofWriter::ProofWriter(std::FILE* file, bool binary)
    : ProofWriter(
          [file](const char* data, size_t n) {
            if (std::fwrite(data, 1, n, file) != n) throw std::runtime_error("proof: write error");
          },
          binary) {}

ProofWriter::~ProofWriter() {
  try {
    flush();
  } catch (...) {
  }
}

void ProofWriter::flush() {
  if (pos_ == 0) return;
  sink_(buf_.data(), pos_);
  bytes_ += pos_;
  pos_ = 0;
}

void ProofWriter::line(bool deletion, const Lit* lits, size_t n) {
  if (deletion) {
    ++deleted_;
  } else {
    ++added_;
  }
  if (binary_) {
    char* out;
    // Each literal takes at most 5 varint bytes for 28-bit variables.
    if (n <= 1024) {
      reserve(2 + 5 * n);
      out = buf_.data() + pos_;
      *out++ = deletion ? 'd' : 'a';
      for (size_t i = 0; i < n; ++i) {
        uint32_t u = 2 * (var_of(lits[i]) + 1) + (is_negative(lits[i]) ? 1 : 0);
        while (u > 127) {
          *out++ = static_cast<char>((u & 127) | 128);
          u >>= 7;
        }
        *out++ = static_cast<char>(u);
      }
      *out++ = 0;
      pos_ = static_cast<size_t>(out - buf_.data());
      return;
    }
    // Long clause: write piecewise.
    reserve(1);
    buf_[pos_++] = deletion ? 'd' : 'a';
    for (size_t i = 0; i < n; ++i) {
      reserve(5);
      uint32_t u = 2 * (var_of(lits[i]) + 1) + (is_negative(lits[i]) ? 1 : 0);
      while (u > 127) {
        buf_[pos_++] = static_cast<char>((u & 127) | 128);
        u >>= 7;
      }
      buf_[pos_++] = static_cast<char>(u);
    }
    reserve(1);
    buf_[pos_++] = 0;
    return;
  }
  if (deletion) {
    reserve(2);
    buf_[pos_++] = 'd';
    buf_[pos_++] = ' ';
  }
  for (size_t i = 0; i < n; ++i) {
    reserve(13);
    int d = to_dimacs(lits[i]);
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
  reserve(2);
  buf_[pos_++] = '0';
  buf_[pos_++] = '\n';
}

}  // namespace psat
