#pragma once
// xz decompression (.xz container with LZMA2 filter), standard library only.
//
// Same streaming interface as gzip.hpp: compressed input is pulled from a source in chunks and the
// decompressed data is pushed to a sink in chunks. Corrupt, truncated or unsupported data throws
// XzError.

#include <cstddef>
#include <cstdint>
#include <functional>
#include <stdexcept>

namespace psat {

class XzError : public std::runtime_error {
 public:
  using std::runtime_error::runtime_error;
};

// True if the data starts with the xz magic bytes FD 37 7A 58 5A 00.
bool is_xz(const void* data, size_t n);

using XzSource = std::function<size_t(unsigned char* buf, size_t cap)>;
using XzSink = std::function<void(const char* data, size_t n)>;

// Decompresses a whole xz file (one or more streams, stream padding). Returns the bytes produced.
uint64_t unxz(const XzSource& source, const XzSink& sink);

}  // namespace psat
