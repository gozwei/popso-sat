// xz (.xz container, LZMA2 filter) decoder, written from the .xz file format specification
// (version 1.2.x) and the description of the LZMA / LZMA2 algorithms.
//
// Layout of an .xz file: one or more streams, each optionally followed by stream padding (zero
// bytes, a multiple of four). A stream is a 12-byte header (magic, flags, CRC32), a sequence of
// blocks, an index (one record per block: unpadded and uncompressed size), and a 12-byte footer
// (CRC32, backward size = index size, flags, magic "YZ"). A block is a header (sizes, filter
// chain, CRC32), the compressed data, zero padding to a multiple of four and the integrity check
// of the uncompressed data (none, CRC32, CRC64 or SHA-256).
//
// Only the LZMA2 filter is supported (BCJ and delta filters are rejected): it covers every .xz
// file made by xz / liblzma / Python for text input such as CNF files.
//
// The decoder never holds the whole file: compressed input is read in 64 KiB pieces (one LZMA2
// chunk at a time), and the output is decoded into the LZMA dictionary (a circular window) and
// handed to the sink from there. The window starts small and doubles up to the dictionary size
// declared in the block header, so a small file compressed with a 64 MiB dictionary (xz -9) only
// needs a little memory. Everything read from the input is bounds-checked: corrupt or truncated
// data throws XzError.

#include "psat/io/xz.hpp"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <memory>
#include <new>
#include <string>
#include <vector>

#include "psat/io/gzip.hpp"  // crc32_update: xz uses the same CRC-32 as gzip

namespace psat {

namespace {

[[noreturn]] void fail(const std::string& what) { throw XzError(what); }

uint32_t le32(const unsigned char* p) {
  return static_cast<uint32_t>(p[0]) | static_cast<uint32_t>(p[1]) << 8 | static_cast<uint32_t>(p[2]) << 16 |
         static_cast<uint32_t>(p[3]) << 24;
}

uint64_t le64(const unsigned char* p) {
  return static_cast<uint64_t>(le32(p)) | static_cast<uint64_t>(le32(p + 4)) << 32;
}

// ------------------------------------------------------------------------------------------------
// Integrity checks.

// CRC-64 as used by xz: ECMA-182 polynomial, bit-reflected, initial value and final XOR all ones.
// CRC-64 is xz's default check, so it is computed 8 bytes at a time ("slicing by 8": table k
// advances a byte through k further zero bytes) to keep it cheap next to the LZMA decoder.
using Crc64Tables = std::array<std::array<uint64_t, 256>, 8>;

const Crc64Tables& crc64_tables() {
  static const Crc64Tables tables = [] {
    Crc64Tables t{};
    for (uint32_t i = 0; i < 256; ++i) {
      uint64_t c = i;
      for (int k = 0; k < 8; ++k) c = (c & 1) ? 0xC96C5795D7870F42ull ^ (c >> 1) : c >> 1;
      t[0][i] = c;
    }
    for (size_t k = 1; k < 8; ++k) {
      for (size_t i = 0; i < 256; ++i) t[k][i] = (t[k - 1][i] >> 8) ^ t[0][t[k - 1][i] & 0xFF];
    }
    return t;
  }();
  return tables;
}

uint64_t crc64_update(uint64_t crc, const unsigned char* p, size_t n) {
  const Crc64Tables& t = crc64_tables();
  uint64_t c = ~crc;
  for (; n >= 8; n -= 8, p += 8) {
    c ^= le64(p);
    c = t[7][c & 0xFF] ^ t[6][(c >> 8) & 0xFF] ^ t[5][(c >> 16) & 0xFF] ^ t[4][(c >> 24) & 0xFF] ^
        t[3][(c >> 32) & 0xFF] ^ t[2][(c >> 40) & 0xFF] ^ t[1][(c >> 48) & 0xFF] ^ t[0][c >> 56];
  }
  for (; n > 0; --n) c = t[0][(c ^ *p++) & 0xFF] ^ (c >> 8);
  return ~c;
}

// SHA-256 (FIPS 180-4).
class Sha256 {
 public:
  using Digest = std::array<unsigned char, 32>;

  Sha256() { reset(); }

  void reset() {
    static constexpr uint32_t kInit[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                          0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    std::copy(kInit, kInit + 8, h_);
    fill_ = 0;
    bytes_ = 0;
  }

  void update(const unsigned char* p, size_t n) {
    bytes_ += n;
    if (fill_ > 0) {
      const size_t k = std::min(n, sizeof(buf_) - fill_);
      std::memcpy(buf_ + fill_, p, k);
      fill_ += k;
      p += k;
      n -= k;
      if (fill_ < sizeof(buf_)) return;
      compress(buf_);
      fill_ = 0;
    }
    for (; n >= 64; n -= 64, p += 64) compress(p);
    std::memcpy(buf_, p, n);
    fill_ = n;
  }

  Digest finish() {
    const uint64_t bits = bytes_ * 8;
    unsigned char pad[72] = {0x80};
    // Pad with 0x80, zeros, and the 64-bit big-endian bit count to a multiple of 64 bytes.
    const size_t zeros = (fill_ < 56 ? 56 - fill_ : 120 - fill_);
    for (int k = 0; k < 8; ++k) pad[zeros + static_cast<size_t>(k)] = static_cast<unsigned char>(bits >> (56 - 8 * k));
    update(pad, zeros + 8);
    Digest d;
    for (size_t k = 0; k < 8; ++k) {
      for (size_t b = 0; b < 4; ++b) d[4 * k + b] = static_cast<unsigned char>(h_[k] >> (24 - 8 * b));
    }
    return d;
  }

 private:
  static uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }

  void compress(const unsigned char* p) {
    static constexpr uint32_t kRound[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
    uint32_t w[64];
    for (int i = 0; i < 16; ++i) {
      w[i] = static_cast<uint32_t>(p[4 * i]) << 24 | static_cast<uint32_t>(p[4 * i + 1]) << 16 |
             static_cast<uint32_t>(p[4 * i + 2]) << 8 | static_cast<uint32_t>(p[4 * i + 3]);
    }
    for (int i = 16; i < 64; ++i) {
      const uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
      const uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
      w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = h_[0], b = h_[1], c = h_[2], d = h_[3], e = h_[4], f = h_[5], g = h_[6], h = h_[7];
    for (int i = 0; i < 64; ++i) {
      const uint32_t t1 = h + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + kRound[i] + w[i];
      const uint32_t t2 = (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
      h = g;
      g = f;
      f = e;
      e = d + t1;
      d = c;
      c = b;
      b = a;
      a = t1 + t2;
    }
    h_[0] += a;
    h_[1] += b;
    h_[2] += c;
    h_[3] += d;
    h_[4] += e;
    h_[5] += f;
    h_[6] += g;
    h_[7] += h;
  }

  uint32_t h_[8];
  unsigned char buf_[64];
  size_t fill_ = 0;
  uint64_t bytes_ = 0;
};

// Check types defined by the format (stream flags, low nibble).
constexpr unsigned kCheckNone = 0x00, kCheckCrc32 = 0x01, kCheckCrc64 = 0x04, kCheckSha256 = 0x0A;

size_t check_size(unsigned type) {
  switch (type) {
    case kCheckNone: return 0;
    case kCheckCrc32: return 4;
    case kCheckCrc64: return 8;
    case kCheckSha256: return 32;
    default: return 0;
  }
}

// ------------------------------------------------------------------------------------------------
// Buffered input: pulls the source in 64 KiB pieces and counts the bytes consumed (the container
// sizes are checked against these counts).

class Reader {
 public:
  explicit Reader(const XzSource& source) : source_(source), buf_(kChunk) {}

  // Copies up to n bytes; fewer only at the end of the input.
  size_t read_some(unsigned char* dst, size_t n) {
    size_t done = 0;
    while (done < n) {
      if (pos_ == len_ && !fill()) break;
      const size_t k = std::min(n - done, len_ - pos_);
      std::memcpy(dst + done, buf_.data() + pos_, k);
      pos_ += k;
      done += k;
    }
    consumed_ += done;
    return done;
  }

  void read(unsigned char* dst, size_t n) {
    if (read_some(dst, n) != n) truncated();
  }

  unsigned char byte() {
    if (pos_ == len_ && !fill()) truncated();
    ++consumed_;
    return buf_[pos_++];
  }

  uint64_t consumed() const { return consumed_; }

  [[noreturn]] static void truncated() { fail("unexpected end of xz data (truncated file?)"); }

 private:
  static constexpr size_t kChunk = size_t{1} << 16;

  bool fill() {
    if (eof_) return false;
    const size_t got = source_(buf_.data(), buf_.size());
    if (got > buf_.size()) fail("input source returned more bytes than requested");
    pos_ = 0;
    len_ = got;
    eof_ = got == 0;
    return !eof_;
  }

  const XzSource& source_;
  std::vector<unsigned char> buf_;
  size_t pos_ = 0, len_ = 0;
  bool eof_ = false;
  uint64_t consumed_ = 0;
};

// ------------------------------------------------------------------------------------------------
// LZMA range decoder and probability model.
//
// Probabilities are 11-bit estimates of "the next bit is 0", adapted by 1/32 of the error after
// every bit. The range decoder keeps range >= 2^24 by shifting in one input byte whenever it drops
// below; this decoder normalizes lazily before each bit and once more at the end of a chunk,
// after which exactly the chunk's compressed bytes have been consumed and `code` is 0.

constexpr uint32_t kTop = uint32_t{1} << 24;
constexpr int kProbBits = 11;
constexpr uint32_t kProbOne = uint32_t{1} << kProbBits;
constexpr int kMoveBits = 5;

struct RangeDecoder {
  uint32_t range;
  uint32_t code;
  const unsigned char* in;
};

inline void rc_normalize(RangeDecoder& rc) {
  if (rc.range < kTop) {
    rc.range <<= 8;
    rc.code = (rc.code << 8) | *rc.in++;
  }
}

inline uint32_t rc_bit(RangeDecoder& rc, uint16_t& prob) {
  rc_normalize(rc);
  const uint32_t p = prob;
  const uint32_t bound = (rc.range >> kProbBits) * p;
  if (rc.code < bound) {
    rc.range = bound;
    prob = static_cast<uint16_t>(p + ((kProbOne - p) >> kMoveBits));
    return 0;
  }
  rc.range -= bound;
  rc.code -= bound;
  prob = static_cast<uint16_t>(p - (p >> kMoveBits));
  return 1;
}

// Bits most significant first through a binary tree of probabilities (indices 1 .. 2^bits - 1).
template <int Bits>
inline uint32_t rc_tree(RangeDecoder& rc, uint16_t* probs) {
  uint32_t m = 1;
  for (int i = 0; i < Bits; ++i) m = (m << 1) | rc_bit(rc, probs[m]);
  return m - (uint32_t{1} << Bits);
}

// Bits least significant first through a binary tree (distance low bits).
inline uint32_t rc_reverse(RangeDecoder& rc, uint16_t* probs, uint32_t bits) {
  uint32_t m = 1, sym = 0;
  for (uint32_t i = 0; i < bits; ++i) {
    const uint32_t b = rc_bit(rc, probs[m]);
    m = (m << 1) | b;
    sym |= b << i;
  }
  return sym;
}

// Bits with probability 1/2 (the middle bits of large distances), most significant first.
inline uint32_t rc_direct(RangeDecoder& rc, uint32_t bits) {
  uint32_t r = 0;
  for (uint32_t i = 0; i < bits; ++i) {
    rc_normalize(rc);
    rc.range >>= 1;
    // code >= range means bit 1; then the subtraction leaves the top bit clear.
    const uint32_t zero = (rc.code - rc.range) >> 31;
    rc.code -= rc.range & (zero - 1);
    r = (r << 1) | (zero ^ 1);
  }
  return r;
}

// LZMA model constants.
constexpr uint32_t kStates = 12;
constexpr uint32_t kLiteralStates = 7;  // states below 7 follow a literal
constexpr uint32_t kEndPosModel = 14;   // distance slots below this use the "special" probabilities
constexpr uint32_t kFullDistances = 128;

// Offsets into the flat probability array (one array makes the reset a single fill).
constexpr int kLenChoice = 0;
constexpr int kLenChoice2 = 1;
constexpr int kLenLow = 2;                 // [pos_state][8], lengths 2..9
constexpr int kLenMid = kLenLow + 16 * 8;  // [pos_state][8], lengths 10..17
constexpr int kLenHigh = kLenMid + 16 * 8;  // [256], lengths 18..273
constexpr int kLenProbs = kLenHigh + 256;

constexpr int kIsMatch = 0;  // [state][pos_state]
constexpr int kIsRep = kIsMatch + kStates * 16;
constexpr int kIsRepG0 = kIsRep + kStates;
constexpr int kIsRepG1 = kIsRepG0 + kStates;
constexpr int kIsRepG2 = kIsRepG1 + kStates;
constexpr int kIsRep0Long = kIsRepG2 + kStates;  // [state][pos_state]
constexpr int kDistSlot = kIsRep0Long + kStates * 16;  // [min(len, 5) - 2][64]
constexpr int kDistSpecial = kDistSlot + 4 * 64;
constexpr int kDistAlign = kDistSpecial + (kFullDistances - kEndPosModel);
constexpr int kMatchLen = kDistAlign + 16;
constexpr int kRepLen = kMatchLen + kLenProbs;
constexpr int kLiteral = kRepLen + kLenProbs;  // [context][0x300], context < 2^(lc + lp) <= 16
constexpr int kNumProbs = kLiteral + 0x300 * 16;

inline uint32_t decode_len(RangeDecoder& rc, uint16_t* probs, uint32_t pos_state) {
  if (rc_bit(rc, probs[kLenChoice]) == 0) return 2 + rc_tree<3>(rc, probs + kLenLow + pos_state * 8);
  if (rc_bit(rc, probs[kLenChoice2]) == 0) return 10 + rc_tree<3>(rc, probs + kLenMid + pos_state * 8);
  return 18 + rc_tree<8>(rc, probs + kLenHigh);
}

// ------------------------------------------------------------------------------------------------
// The decoder.

constexpr unsigned char kMagic[6] = {0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00};
constexpr uint64_t kUnknown = ~uint64_t{0};
constexpr uint32_t kLzma2FilterId = 0x21;
// The window is allocated on demand and grows up to the declared dictionary size; this caps it
// (xz's own encoder never uses a dictionary above 1.5 GiB).
constexpr size_t kMaxWindow = size_t{3} << 29;
constexpr size_t kInitialWindow = size_t{1} << 20;
// Decoded data is handed to the sink at the end of an LZMA2 chunk once this much is pending (and
// whenever the window wraps), so the consumer works on cache-warm pieces of a few hundred KB.
constexpr size_t kFlushThreshold = size_t{1} << 18;
// An LZMA chunk holds at most 64 KiB of compressed data. The buffer has slack after it so that
// the range decoder can run past the end of corrupt data within one symbol without a bounds check
// per input byte (it reads at most a few dozen bytes per symbol); overruns are caught per symbol.
constexpr size_t kMaxPacked = size_t{1} << 16;
constexpr size_t kPackedSlack = 256;

const char* filter_name(uint64_t id) {
  switch (id) {
    case 0x03: return "delta";
    case 0x04: return "BCJ x86";
    case 0x05: return "BCJ PowerPC";
    case 0x06: return "BCJ IA-64";
    case 0x07: return "BCJ ARM";
    case 0x08: return "BCJ ARM-Thumb";
    case 0x09: return "BCJ SPARC";
    case 0x0A: return "BCJ ARM64";
    case 0x0B: return "BCJ RISC-V";
    default: return "unknown";
  }
}

std::string hex(uint64_t v) {
  char buf[24];
  std::snprintf(buf, sizeof(buf), "0x%llX", static_cast<unsigned long long>(v));
  return buf;
}

// Multibyte integer (7 bits per byte, least significant first, at most 9 bytes, no redundant
// trailing zero bytes) from a buffer, bounds-checked against end.
uint64_t vli_from(const unsigned char* buf, size_t end, size_t& pos, const char* what) {
  uint64_t v = 0;
  for (int i = 0; i < 9; ++i) {
    if (pos >= end) fail(std::string("corrupt block header (") + what + " runs past the header)");
    const unsigned b = buf[pos++];
    v |= static_cast<uint64_t>(b & 0x7F) << (7 * i);
    if ((b & 0x80) == 0) {
      if (b == 0 && i > 0) fail(std::string("corrupt block header (non-minimal ") + what + ")");
      return v;
    }
  }
  fail(std::string("corrupt block header (") + what + " too long)");
}

class XzDecoder {
 public:
  XzDecoder(const XzSource& source, const XzSink& sink)
      : in_(source), sink_(sink), packed_(kMaxPacked + kPackedSlack), probs_(kNumProbs) {}

  uint64_t run() {
    unsigned char h[12];
    const size_t got = in_.read_some(h, sizeof(h));
    if (got < sizeof(kMagic) || std::memcmp(h, kMagic, sizeof(kMagic)) != 0) fail("not xz data (bad magic bytes)");
    if (got < sizeof(h)) Reader::truncated();
    for (;;) {
      stream(h);
      // Stream padding (groups of four zero bytes), then the end of the input or another stream.
      for (;;) {
        const size_t n = in_.read_some(h, 4);
        if (n == 0) return total_out_;
        if (n < 4) fail("trailing garbage or truncated stream padding after the xz stream");
        if (le32(h) == 0) continue;
        if (std::memcmp(h, kMagic, 4) != 0) fail("trailing garbage after the xz stream");
        in_.read(h + 4, 8);
        if (h[4] != kMagic[4] || h[5] != kMagic[5]) fail("trailing garbage after the xz stream");
        break;
      }
    }
  }

 private:
  // --- container

  void stream(const unsigned char* header) {
    if (crc32_update(0, header + 6, 2) != le32(header + 8)) fail("stream header CRC32 mismatch (corrupt data)");
    if (header[6] != 0 || (header[7] & 0xF0) != 0) fail("unsupported stream flags (newer xz format?)");
    check_type_ = header[7];
    if (check_type_ != kCheckNone && check_type_ != kCheckCrc32 && check_type_ != kCheckCrc64 &&
        check_type_ != kCheckSha256) {
      fail("unsupported integrity check type " + std::to_string(check_type_));
    }
    blocks_ = 0;
    block_records_.reset();
    for (;;) {
      const unsigned char b = in_.byte();
      if (b == 0) break;  // index indicator
      block(b);
    }
    const uint64_t index_size = index();
    unsigned char f[12];
    in_.read(f, sizeof(f));
    if (f[10] != 'Y' || f[11] != 'Z') fail("bad stream footer magic (corrupt data)");
    if (crc32_update(0, f + 4, 6) != le32(f)) fail("stream footer CRC32 mismatch (corrupt data)");
    if (f[8] != header[6] || f[9] != header[7]) fail("stream footer flags differ from the stream header");
    if ((static_cast<uint64_t>(le32(f + 4)) + 1) * 4 != index_size) fail("stream footer backward size mismatch");
  }

  void block(unsigned char size_byte) {
    const size_t header_size = (static_cast<size_t>(size_byte) + 1) * 4;
    unsigned char h[1024];
    h[0] = size_byte;
    in_.read(h + 1, header_size - 1);
    const size_t end = header_size - 4;
    if (crc32_update(0, h, end) != le32(h + end)) fail("block header CRC32 mismatch (corrupt data)");
    const unsigned flags = h[1];
    if (flags & 0x3C) fail("reserved block header flags set (newer xz format?)");
    size_t p = 2;
    uint64_t declared_packed = kUnknown, declared_unpacked = kUnknown;
    if (flags & 0x40) {
      declared_packed = vli_from(h, end, p, "compressed size");
      if (declared_packed == 0) fail("corrupt block header (compressed size 0)");
    }
    if (flags & 0x80) declared_unpacked = vli_from(h, end, p, "uncompressed size");
    const unsigned filters = (flags & 3) + 1;
    uint64_t ids[4];
    unsigned lzma2_props = 0;
    for (unsigned i = 0; i < filters; ++i) {
      ids[i] = vli_from(h, end, p, "filter id");
      const uint64_t props = vli_from(h, end, p, "filter properties size");
      if (props > end - p) fail("corrupt block header (filter properties run past the header)");
      if (ids[i] == kLzma2FilterId) {
        if (props != 1) fail("corrupt block header (LZMA2 properties must be one byte)");
        lzma2_props = h[p];
      }
      p += static_cast<size_t>(props);
    }
    for (; p < end; ++p) {
      if (h[p] != 0) fail("corrupt block header (non-zero padding)");
    }
    for (unsigned i = 0; i < filters; ++i) {
      if (ids[i] != kLzma2FilterId) {
        fail(std::string("unsupported xz filter ") + hex(ids[i]) + " (" + filter_name(ids[i]) +
             "); only LZMA2 is supported (recompress with plain 'xz')");
      }
    }
    if (filters != 1) fail("invalid xz filter chain (LZMA2 more than once)");
    if (lzma2_props > 40) fail("invalid LZMA2 dictionary size");
    // Property 40 means 4 GiB - 1; otherwise 2 or 3 times a power of two, from 4 KiB.
    const uint64_t dict = lzma2_props == 40 ? 0xFFFFFFFFull
                                            : static_cast<uint64_t>(2 | (lzma2_props & 1)) << (lzma2_props / 2 + 11);

    block_out_ = 0;
    if (check_type_ == kCheckCrc32) crc32_ = 0;
    if (check_type_ == kCheckCrc64) crc64_ = 0;
    if (check_type_ == kCheckSha256) sha256_.reset();
    const uint64_t data_start = in_.consumed();
    lzma2(dict, data_start, declared_packed, declared_unpacked);
    flush();
    const uint64_t packed = in_.consumed() - data_start;
    if (declared_packed != kUnknown && packed != declared_packed) fail("block compressed size mismatch (corrupt data)");
    if (declared_unpacked != kUnknown && block_out_ != declared_unpacked) {
      fail("block uncompressed size mismatch (corrupt data)");
    }
    for (uint64_t k = packed; k % 4 != 0; ++k) {
      if (in_.byte() != 0) fail("non-zero block padding (corrupt data)");
    }
    verify_check();
    // Record the block for the index check: unpadded size = header + compressed data + check.
    unsigned char rec[16];
    const uint64_t unpadded = header_size + packed + check_size(check_type_);
    for (int k = 0; k < 8; ++k) {
      rec[k] = static_cast<unsigned char>(unpadded >> (8 * k));
      rec[8 + k] = static_cast<unsigned char>(block_out_ >> (8 * k));
    }
    block_records_.update(rec, sizeof(rec));
    ++blocks_;
  }

  void verify_check() {
    unsigned char c[32];
    in_.read(c, check_size(check_type_));
    bool ok = true;
    if (check_type_ == kCheckCrc32) ok = le32(c) == crc32_;
    if (check_type_ == kCheckCrc64) ok = le64(c) == crc64_;
    if (check_type_ == kCheckSha256) ok = std::memcmp(sha256_.finish().data(), c, 32) == 0;
    if (!ok) fail("integrity check mismatch (corrupt data)");
  }

  // The index: the indicator byte (already read), the record count, one (unpadded size,
  // uncompressed size) record per block, zero padding to a multiple of four, CRC32. The records
  // are compared through a hash, so the decoder needs no per-block memory. Returns the index size.
  uint64_t index() {
    uint32_t crc = crc32_update(0, reinterpret_cast<const unsigned char*>("\0"), 1);
    uint64_t size = 1;
    const auto next = [&]() {
      const unsigned char b = in_.byte();
      crc = crc32_update(crc, &b, 1);
      ++size;
      return b;
    };
    const auto vli = [&]() {
      uint64_t v = 0;
      for (int i = 0; i < 9; ++i) {
        const unsigned b = next();
        v |= static_cast<uint64_t>(b & 0x7F) << (7 * i);
        if ((b & 0x80) == 0) {
          if (b == 0 && i > 0) fail("corrupt xz index (non-minimal integer)");
          return v;
        }
      }
      fail("corrupt xz index (integer too long)");
    };
    const uint64_t count = vli();
    if (count != blocks_) {
      fail("xz index lists " + std::to_string(count) + " blocks, the stream has " + std::to_string(blocks_));
    }
    Sha256 records;
    for (uint64_t i = 0; i < count; ++i) {
      unsigned char rec[16];
      const uint64_t unpadded = vli(), unpacked = vli();
      for (int k = 0; k < 8; ++k) {
        rec[k] = static_cast<unsigned char>(unpadded >> (8 * k));
        rec[8 + k] = static_cast<unsigned char>(unpacked >> (8 * k));
      }
      records.update(rec, sizeof(rec));
    }
    if (records.finish() != block_records_.finish()) fail("xz index does not match the blocks (corrupt data)");
    while (size % 4 != 0) {
      if (next() != 0) fail("non-zero xz index padding (corrupt data)");
    }
    unsigned char c[4];
    in_.read(c, 4);
    if (le32(c) != crc) fail("xz index CRC32 mismatch (corrupt data)");
    return size + 4;
  }

  // --- LZMA2: a sequence of chunks, each starting with a control byte.
  //   0x00         end of the LZMA2 data
  //   0x01, 0x02   uncompressed chunk (with / without dictionary reset), 16-bit size - 1
  //   0x80..0xFF   LZMA chunk: bits 0-4 are bits 16-20 of the uncompressed size - 1, followed by
  //                its low 16 bits and the compressed size - 1 (16 bits, big endian); bits 5-6:
  //                0 = continue, 1 = reset state, 2 = reset state + new properties byte,
  //                3 = also reset the dictionary.
  // The first chunk must reset the dictionary, and the first LZMA chunk after a dictionary reset
  // must set the properties.

  void lzma2(uint64_t dict, uint64_t data_start, uint64_t declared_packed, uint64_t declared_unpacked) {
    dict_size_ = dict;
    bool need_dict_reset = true, need_props = true;
    for (;;) {
      const unsigned control = in_.byte();
      if (control == 0x00) break;
      if (control > 0x02 && control < 0x80) fail("corrupt LZMA2 data (invalid control byte " + hex(control) + ")");
      if (control >= 0xE0 || control == 0x01) {
        reset_dict();
        need_dict_reset = false;
        need_props = true;
      } else if (need_dict_reset) {
        fail("corrupt LZMA2 data (no dictionary reset at the start)");
      }
      if (control >= 0x80) {
        unsigned char s[4];
        in_.read(s, 4);
        const size_t unpacked =
            ((static_cast<size_t>(control & 0x1F) << 16) | static_cast<size_t>(s[0]) << 8 | s[1]) + 1;
        const size_t packed = (static_cast<size_t>(s[2]) << 8 | s[3]) + 1;
        if (control >= 0xC0) {
          set_props(in_.byte());
          need_props = false;
          reset_state();
        } else if (need_props) {
          fail("corrupt LZMA2 data (LZMA chunk without properties)");
        } else if (control >= 0xA0) {
          reset_state();
        }
        if (packed < 5) fail("corrupt LZMA2 data (LZMA chunk too short)");
        in_.read(packed_.data(), packed);
        lzma_chunk(packed_.data(), packed, unpacked);
      } else {
        unsigned char s[2];
        in_.read(s, 2);
        copy_uncompressed((static_cast<size_t>(s[0]) << 8 | s[1]) + 1);
      }
      // Fail early (before decoding much more) when the block header's sizes are exceeded.
      if (declared_packed != kUnknown && in_.consumed() - data_start > declared_packed) {
        fail("block compressed size mismatch (corrupt data)");
      }
      if (declared_unpacked != kUnknown && block_out_ + (pos_ - flushed_) > declared_unpacked) {
        fail("block uncompressed size mismatch (corrupt data)");
      }
      if (pos_ - flushed_ >= kFlushThreshold) flush();
    }
  }

  void set_props(unsigned b) {
    if (b >= 9 * 5 * 5) fail("corrupt LZMA2 data (invalid properties byte)");
    lc_ = b % 9;
    lp_ = (b / 9) % 5;
    pb_ = b / 45;
    if (lc_ + lp_ > 4) fail("corrupt LZMA2 data (lc + lp > 4)");
  }

  void reset_state() {
    std::fill(probs_.begin(), probs_.end(), static_cast<uint16_t>(kProbOne / 2));
    state_ = 0;
    rep0_ = rep1_ = rep2_ = rep3_ = 0;
  }

  // --- the dictionary window
  //
  // win_[0, cap_) is a circular buffer; pos_ is the next write position and flushed_ the end of
  // the data already handed to the sink. Until the window wraps for the first time it holds the
  // whole history since the dictionary reset at [0, pos_), so it can grow by reallocating; once
  // cap_ equals the dictionary size it wraps instead.

  void reset_dict() {
    flush();
    pos_ = flushed_ = 0;
    wrapped_ = false;
    total_ = 0;
    if (alloc_ == 0) allocate(static_cast<size_t>(std::min<uint64_t>(dict_size_, kInitialWindow)));
    cap_ = static_cast<size_t>(std::min<uint64_t>(dict_size_, alloc_));
  }

  void allocate(size_t n) {
    std::unique_ptr<unsigned char[]> w;
    try {
      w.reset(new unsigned char[n]);
    } catch (const std::bad_alloc&) {
      fail("out of memory for the LZMA2 dictionary (" + std::to_string(n >> 20) + " MiB)");
    }
    if (pos_ > 0) std::memcpy(w.get(), win_.get(), pos_);
    win_ = std::move(w);
    alloc_ = n;
  }

  // Called when pos_ reaches cap_: hands the pending output to the sink, then grows the window
  // (before the first wrap, while it is below the dictionary size) or wraps around.
  void make_room() {
    flush();
    if (cap_ < dict_size_) {
      if (cap_ >= kMaxWindow) {
        fail("LZMA2 dictionary larger than " + std::to_string(kMaxWindow >> 20) + " MiB is not supported");
      }
      const size_t want = static_cast<size_t>(std::min<uint64_t>({dict_size_, uint64_t{2} * cap_, kMaxWindow}));
      if (want > alloc_) allocate(want);
      cap_ = want;
    } else {
      pos_ = flushed_ = 0;
      wrapped_ = true;
    }
  }

  void flush() {
    if (pos_ > flushed_) {
      emit(win_.get() + flushed_, pos_ - flushed_);
      flushed_ = pos_;
    }
  }

  void emit(const unsigned char* p, size_t n) {
    switch (check_type_) {
      case kCheckCrc32: crc32_ = crc32_update(crc32_, p, n); break;
      case kCheckCrc64: crc64_ = crc64_update(crc64_, p, n); break;
      case kCheckSha256: sha256_.update(p, n); break;
      default: break;
    }
    block_out_ += n;
    total_out_ += n;
    sink_(reinterpret_cast<const char*>(p), n);
  }

  void copy_uncompressed(size_t n) {
    total_ += n;
    while (n > 0) {
      const size_t k = std::min(n, cap_ - pos_);
      in_.read(win_.get() + pos_, k);
      pos_ += k;
      n -= k;
      if (pos_ == cap_) make_room();
    }
  }

  // Decodes one LZMA chunk: `packed` compressed bytes at in (followed by kPackedSlack readable
  // bytes) into exactly `unpacked` bytes of output. The hot state lives in locals: stores through
  // unsigned char* may alias anything, so members would be reloaded after every output byte.
  void lzma_chunk(const unsigned char* in, size_t packed, size_t unpacked) {
    if (in[0] != 0) fail("corrupt LZMA data (bad range coder start)");
    RangeDecoder rc{0xFFFFFFFFu, static_cast<uint32_t>(in[1]) << 24 | static_cast<uint32_t>(in[2]) << 16 |
                                     static_cast<uint32_t>(in[3]) << 8 | in[4],
                    in + 5};
    const unsigned char* const in_end = in + packed;
    uint16_t* const pr = probs_.data();
    unsigned char* win = win_.get();
    size_t cap = cap_, pos = pos_;
    bool wrapped = wrapped_;
    uint64_t total = total_;
    uint32_t state = state_, rep0 = rep0_, rep1 = rep1_, rep2 = rep2_, rep3 = rep3_;
    const uint32_t pb_mask = (uint32_t{1} << pb_) - 1, lp_mask = (uint32_t{1} << lp_) - 1;
    const uint32_t lc = lc_;
    size_t left = unpacked;

    // After pos reaches cap: let make_room flush / grow / wrap, then reload the window.
    const auto room = [&]() {
      pos_ = pos;
      make_room();
      win = win_.get();
      cap = cap_;
      pos = pos_;
      wrapped = wrapped_;
    };

    while (left > 0) {
      if (rc.in > in_end) fail("corrupt LZMA data (compressed chunk overrun)");
      const uint32_t pos_state = static_cast<uint32_t>(total) & pb_mask;

      if (rc_bit(rc, pr[kIsMatch + state * 16 + pos_state]) == 0) {
        // Literal, coded with the previous byte's high bits and the position's low bits as context.
        const uint32_t prev = pos > 0 ? win[pos - 1] : wrapped ? win[cap - 1] : 0;
        uint16_t* lit = pr + kLiteral + 0x300 * (((static_cast<uint32_t>(total) & lp_mask) << lc) + (prev >> (8 - lc)));
        uint32_t sym = 1;
        if (state < kLiteralStates) {
          do sym = (sym << 1) | rc_bit(rc, lit[sym]);
          while (sym < 0x100);
        } else {
          // After a match: the byte at distance rep0 steers the probabilities until the first
          // bit that differs from it ("matched literal").
          if (rep0 >= (wrapped ? cap : pos)) fail("corrupt LZMA data (distance beyond the dictionary)");
          uint32_t match = win[pos > rep0 ? pos - rep0 - 1 : pos + cap - rep0 - 1];
          do {
            const uint32_t match_bit = (match >> 7) & 1;
            match <<= 1;
            const uint32_t b = rc_bit(rc, lit[0x100 + (match_bit << 8) + sym]);
            sym = (sym << 1) | b;
            if (b != match_bit) {
              while (sym < 0x100) sym = (sym << 1) | rc_bit(rc, lit[sym]);
              break;
            }
          } while (sym < 0x100);
        }
        win[pos++] = static_cast<unsigned char>(sym);
        ++total;
        --left;
        state = state < 4 ? 0 : state < 10 ? state - 3 : state - 6;
        if (pos == cap) room();
        continue;
      }

      uint32_t len;
      if (rc_bit(rc, pr[kIsRep + state]) == 0) {
        // A match with a new distance: length, then a 6-bit distance slot (context: length),
        // then the slot's extra bits.
        len = decode_len(rc, pr + kMatchLen, pos_state);
        state = state < kLiteralStates ? 7 : 10;
        const uint32_t slot = rc_tree<6>(rc, pr + kDistSlot + 64 * (len < 6 ? len - 2 : 3));
        uint32_t dist = slot;
        if (slot >= 4) {
          const uint32_t bits = (slot >> 1) - 1;
          dist = (2 | (slot & 1)) << bits;
          if (slot < kEndPosModel) {
            dist += rc_reverse(rc, pr + kDistSpecial - 1 + (dist - slot), bits);
          } else {
            dist += rc_direct(rc, bits - 4) << 4;
            dist += rc_reverse(rc, pr + kDistAlign, 4);
          }
        }
        if (dist == 0xFFFFFFFFu) fail("corrupt LZMA2 data (end marker inside a chunk)");
        rep3 = rep2;
        rep2 = rep1;
        rep1 = rep0;
        rep0 = dist;
      } else if (rc_bit(rc, pr[kIsRepG0 + state]) == 0) {
        if (rc_bit(rc, pr[kIsRep0Long + state * 16 + pos_state]) == 0) {
          // "Short rep": one byte from distance rep0.
          if (rep0 >= (wrapped ? cap : pos)) fail("corrupt LZMA data (distance beyond the dictionary)");
          state = state < kLiteralStates ? 9 : 11;
          win[pos] = win[pos > rep0 ? pos - rep0 - 1 : pos + cap - rep0 - 1];
          ++pos;
          ++total;
          --left;
          if (pos == cap) room();
          continue;
        }
        len = decode_len(rc, pr + kRepLen, pos_state);
        state = state < kLiteralStates ? 8 : 11;
      } else {
        // Repeat of rep1, rep2 or rep3, which moves to the front.
        uint32_t dist;
        if (rc_bit(rc, pr[kIsRepG1 + state]) == 0) {
          dist = rep1;
        } else {
          if (rc_bit(rc, pr[kIsRepG2 + state]) == 0) {
            dist = rep2;
          } else {
            dist = rep3;
            rep3 = rep2;
          }
          rep2 = rep1;
        }
        rep1 = rep0;
        rep0 = dist;
        len = decode_len(rc, pr + kRepLen, pos_state);
        state = state < kLiteralStates ? 8 : 11;
      }

      // Copy len bytes from distance rep0 + 1. Matches never cross an LZMA2 chunk boundary.
      if (rep0 >= (wrapped ? cap : pos)) fail("corrupt LZMA data (distance beyond the dictionary)");
      if (len > left) fail("corrupt LZMA data (match runs past the chunk end)");
      total += len;
      left -= len;
      if (pos > rep0 && len < cap - pos) {
        // Fast path: source and destination contiguous. Overlap (distance < length) repeats the
        // last `distance` bytes, so it must go forward byte by byte.
        unsigned char* d = win + pos;
        const unsigned char* s = d - rep0 - 1;
        if (rep0 >= len) {
          std::memcpy(d, s, len);
        } else if (rep0 == 0) {
          std::memset(d, *s, len);
        } else {
          for (uint32_t k = 0; k < len; ++k) d[k] = s[k];
        }
        pos += len;
      } else {
        size_t src = pos > rep0 ? pos - rep0 - 1 : pos + cap - rep0 - 1;
        for (uint32_t k = 0; k < len; ++k) {
          win[pos++] = win[src++];
          if (src == cap) src = 0;
          if (pos == cap) room();
        }
      }
    }

    rc_normalize(rc);
    if (rc.in != in_end || rc.code != 0) fail("corrupt LZMA data (chunk does not end cleanly)");
    pos_ = pos;
    total_ = total;
    state_ = state;
    rep0_ = rep0;
    rep1_ = rep1;
    rep2_ = rep2;
    rep3_ = rep3;
  }

  Reader in_;
  const XzSink& sink_;
  std::vector<unsigned char> packed_;
  std::vector<uint16_t> probs_;

  // Stream and block state.
  unsigned check_type_ = 0;
  uint32_t crc32_ = 0;
  uint64_t crc64_ = 0;
  Sha256 sha256_;
  uint64_t blocks_ = 0;
  Sha256 block_records_;
  uint64_t block_out_ = 0, total_out_ = 0;

  // Dictionary window.
  std::unique_ptr<unsigned char[]> win_;
  size_t alloc_ = 0, cap_ = 0, pos_ = 0, flushed_ = 0;
  bool wrapped_ = false;
  uint64_t dict_size_ = 0;
  uint64_t total_ = 0;  // bytes since the dictionary reset (the position for lp / pb)

  // LZMA state.
  uint32_t lc_ = 0, lp_ = 0, pb_ = 0;
  uint32_t state_ = 0, rep0_ = 0, rep1_ = 0, rep2_ = 0, rep3_ = 0;
};

}  // namespace

bool is_xz(const void* data, size_t n) { return n >= 6 && std::memcmp(data, kMagic, 6) == 0; }

uint64_t unxz(const XzSource& source, const XzSink& sink) {
  XzDecoder dec(source, sink);
  return dec.run();
}

}  // namespace psat
