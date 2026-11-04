#pragma once
// Streams an input file to a sink in chunks, decompressing gzip and xz data on the fly (detected by
// the magic bytes, whatever the file name). The path "-" reads standard input.

#include <cstddef>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <string>

namespace psat {

class InputError : public std::runtime_error {
 public:
  using std::runtime_error::runtime_error;
};

using ChunkSink = std::function<void(const char* data, size_t n)>;

// Returns the number of (decompressed) bytes delivered. Throws InputError (with the path) on I/O
// errors and corrupt compressed data.
uint64_t stream_input(const std::string& path, const ChunkSink& sink);

}  // namespace psat
