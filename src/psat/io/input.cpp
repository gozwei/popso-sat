#include "psat/io/input.hpp"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <vector>

#include "psat/io/gzip.hpp"
#include "psat/io/xz.hpp"

namespace psat {

uint64_t stream_input(const std::string& path, const ChunkSink& sink) {
  std::FILE* f = nullptr;
  std::unique_ptr<std::FILE, int (*)(std::FILE*)> guard(nullptr, &std::fclose);
  if (path == "-") {
    f = stdin;
  } else {
    f = std::fopen(path.c_str(), "rb");
    if (!f) throw InputError(path + ": cannot open file");
    guard.reset(f);
  }
  // Peek at the magic bytes, then hand them to the decoder (or the sink) first.
  unsigned char head[6];
  size_t nh = 0;
  while (nh < sizeof(head)) {
    const size_t got = std::fread(head + nh, 1, sizeof(head) - nh, f);
    if (got == 0) break;
    nh += got;
  }
  if (std::ferror(f)) throw InputError(path + ": read error");
  size_t head_pos = 0;
  auto source = [&](unsigned char* buf, size_t cap) -> size_t {
    size_t n = 0;
    while (head_pos < nh && n < cap) buf[n++] = head[head_pos++];
    if (n < cap) {
      const size_t got = std::fread(buf + n, 1, cap - n, f);
      if (got == 0 && std::ferror(f)) throw InputError(path + ": read error");
      n += got;
    }
    return n;
  };
  try {
    if (is_gzip(head, nh)) return gunzip(source, sink);
    if (is_xz(head, nh)) return unxz(source, sink);
  } catch (const GzipError& e) {
    throw InputError(path + ": gzip: " + e.what());
  } catch (const XzError& e) {
    throw InputError(path + ": xz: " + e.what());
  }
  if (nh >= 3 && std::memcmp(head, "BZh", 3) == 0) throw InputError(path + ": bzip2 input is not supported");
  std::vector<unsigned char> buf(1 << 18);
  uint64_t total = 0;
  for (;;) {
    const size_t got = source(buf.data(), buf.size());
    if (got == 0) break;
    sink(reinterpret_cast<const char*>(buf.data()), got);
    total += got;
  }
  return total;
}

}  // namespace psat
