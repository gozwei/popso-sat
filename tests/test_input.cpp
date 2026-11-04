// Input streaming (io/input.hpp): plain, gzip and xz CNF files (detected by their magic bytes,
// whatever the name) parsed by the DIMACS parser to the same clauses, and the errors for missing,
// corrupt and unsupported files. The files in tests/data are described in test_xz.cpp.

#include <cstdio>
#include <filesystem>
#include <string>
#include <vector>

#include "psat/io/dimacs.hpp"
#include "psat/io/input.hpp"
#include "test_framework.hpp"

using namespace psat;

namespace {

std::string data_path(const char* name) { return std::string(PSAT_SOURCE_DIR) + "/tests/data/" + name; }

struct Streamed {
  std::string text;
  size_t pieces = 0;
  uint64_t returned = 0;
};

Streamed stream(const std::string& path) {
  Streamed s;
  s.returned = stream_input(path, [&](const char* d, size_t n) {
    s.text.append(d, n);
    ++s.pieces;
  });
  return s;
}

struct Collect : DimacsHandler {
  int vars = -1;
  int64_t declared = -1;
  std::vector<std::vector<int>> clauses;
  void header(int v, int64_t c) override {
    vars = v;
    declared = c;
  }
  void clause(const int* lits, size_t n) override { clauses.emplace_back(lits, lits + n); }
};

// Streams a file straight into the parser, as the solver does.
Collect parse_file(const std::string& path) {
  Collect c;
  DimacsParser parser(c);
  stream_input(path, [&](const char* d, size_t n) { parser.feed(d, n); });
  parser.finish();
  return c;
}

// The clauses of tests/data/small.cnf.
std::vector<std::vector<int>> small_clauses() {
  std::vector<std::vector<int>> cl;
  for (int i = 0; i < 40; ++i) cl.push_back({i % 20 + 1, -((i * 7) % 20 + 1), (i * 3 + 5) % 20 + 1});
  return cl;
}

std::string read_bytes(const std::string& path) {
  std::FILE* f = std::fopen(path.c_str(), "rb");
  REQUIRE(f != nullptr);
  std::string s;
  char buf[65536];
  for (size_t n; (n = std::fread(buf, 1, sizeof(buf), f)) > 0;) s.append(buf, n);
  std::fclose(f);
  return s;
}

std::string temp_file(const char* name, const std::string& data) {
  const std::string p = (std::filesystem::temp_directory_path() / name).string();
  std::FILE* f = std::fopen(p.c_str(), "wb");
  REQUIRE(f != nullptr);
  std::fwrite(data.data(), 1, data.size(), f);
  std::fclose(f);
  return p;
}

// The InputError message for reading `path`, or "" if it reads fine.
std::string input_error(const std::string& path) {
  try {
    stream(path);
  } catch (const InputError& e) {
    return e.what();
  }
  return "";
}

}  // namespace

TEST(input_plain_gzip_xz_same_text) {
  const Streamed plain = stream(data_path("small.cnf"));
  REQUIRE(plain.text.size() == 467);
  CHECK(plain.returned == plain.text.size());
  CHECK(plain.text.rfind("c small CNF", 0) == 0);
  for (const char* name : {"small.cnf.gz", "small.cnf.xz"}) {
    const Streamed s = stream(data_path(name));
    CHECK(s.text == plain.text);
    CHECK(s.returned == plain.text.size());
  }
}

TEST(input_parse_compressed_cnf) {
  const std::vector<std::vector<int>> want = small_clauses();
  for (const char* name : {"small.cnf", "small.cnf.gz", "small.cnf.xz"}) {
    const Collect c = parse_file(data_path(name));
    CHECK_EQ(c.vars, 20);
    CHECK_EQ(c.declared, 40);
    CHECK(c.clauses == want);
  }
}

TEST(input_detects_by_magic_not_name) {
  const std::string text = read_bytes(data_path("small.cnf"));
  const std::string xz = temp_file("psat_test_input_xz_noext.cnf", read_bytes(data_path("small.cnf.xz")));
  const std::string gz = temp_file("psat_test_input_gz_noext.cnf", read_bytes(data_path("small.cnf.gz")));
  const std::string plain = temp_file("psat_test_input_plain.cnf.xz", text);  // plain text under an .xz name
  CHECK(stream(xz).text == text);
  CHECK(stream(gz).text == text);
  CHECK(stream(plain).text == text);
  CHECK(parse_file(xz).clauses == small_clauses());
  for (const std::string& p : {xz, gz, plain}) std::filesystem::remove(p);
  // Empty and very short files are plain text.
  const std::string empty = temp_file("psat_test_input_empty.cnf", "");
  const Streamed e = stream(empty);
  CHECK(e.text.empty() && e.returned == 0);
  const std::string tiny = temp_file("psat_test_input_tiny.cnf", "\xfd" "7");
  CHECK(stream(tiny).text == "\xfd" "7");
  std::filesystem::remove(empty);
  std::filesystem::remove(tiny);
}

TEST(input_large_xz_streams_in_pieces) {
  const Streamed s = stream(data_path("xz_big_p6.xz"));
  CHECK(s.returned == 2439102);
  CHECK(s.text.size() == 2439102);
  CHECK(s.pieces >= 4);
}

TEST(input_errors) {
  // A missing file.
  const std::string missing = data_path("no_such_file.cnf");
  const std::string m = input_error(missing);
  CHECK(m.find("no_such_file.cnf") != std::string::npos && m.find("cannot open") != std::string::npos);
  // Corrupt compressed files: the error names the path and the format.
  std::string xz = read_bytes(data_path("small.cnf.xz"));
  xz[xz.size() / 2] ^= 0x20;
  const std::string bad_xz = temp_file("psat_test_input_bad.cnf.xz", xz);
  const std::string ex = input_error(bad_xz);
  CHECK(ex.find("psat_test_input_bad.cnf.xz") != std::string::npos && ex.find(": xz: ") != std::string::npos);
  std::string gz = read_bytes(data_path("small.cnf.gz"));
  gz[gz.size() - 6] ^= 0x40;
  const std::string bad_gz = temp_file("psat_test_input_bad.cnf.gz", gz);
  const std::string eg = input_error(bad_gz);
  CHECK(eg.find("psat_test_input_bad.cnf.gz") != std::string::npos && eg.find(": gzip: ") != std::string::npos);
  // A truncated xz file.
  const std::string cut = read_bytes(data_path("small.cnf.xz")).substr(0, 100);
  const std::string trunc = temp_file("psat_test_input_trunc.cnf.xz", cut);
  CHECK(input_error(trunc).find("unexpected end") != std::string::npos);
  // bzip2 is recognised and rejected with a clear message.
  const std::string bz = temp_file("psat_test_input.cnf.bz2", "BZh91AY&SY");
  CHECK(input_error(bz).find("bzip2") != std::string::npos);
  for (const std::string& p : {bad_xz, bad_gz, trunc, bz}) std::filesystem::remove(p);
}
