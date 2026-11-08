// DIMACS push parser: layouts, chunk boundaries, strict/relaxed errors.
#include <string>
#include <vector>

#include "psat/io/dimacs.hpp"
#include "test_framework.hpp"

using namespace psat;

namespace {

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

// Parses text fed in chunks of the given size (0 = all at once).
Collect parse(const std::string& text, bool strict = true, size_t chunk = 0) {
  Collect c;
  DimacsParser p(c, strict);
  if (chunk == 0) {
    p.feed(text.data(), text.size());
  } else {
    for (size_t i = 0; i < text.size(); i += chunk) p.feed(text.data() + i, std::min(chunk, text.size() - i));
  }
  p.finish();
  return c;
}

}  // namespace

TEST(dimacs_basic) {
  const std::string text = "c a comment\np cnf 3 2\n1 -2 0\n2 3\n -1 0\n";
  for (size_t chunk : {0, 1, 2, 3, 7}) {
    Collect c = parse(text, true, chunk);
    CHECK_EQ(c.vars, 3);
    CHECK_EQ(c.declared, 2);
    REQUIRE(c.clauses.size() == 2);
    CHECK((c.clauses[0] == std::vector<int>{1, -2}));
    CHECK((c.clauses[1] == std::vector<int>{2, 3, -1}));
  }
}

TEST(dimacs_comments_whitespace_crlf) {
  Collect c = parse("c x\r\np  cnf  2  2 \r\nc mid\r\n\t1\t2 0\r\n\r\n  c indented comment\n-1 -2 0");
  REQUIRE(c.clauses.size() == 2);
  CHECK((c.clauses[1] == std::vector<int>{-1, -2}));
}

TEST(dimacs_empty_clause_and_formula) {
  Collect c = parse("p cnf 0 1\n0\n");
  REQUIRE(c.clauses.size() == 1);
  CHECK(c.clauses[0].empty());
  Collect e = parse("p cnf 5 0\n");
  CHECK(e.clauses.empty());
  CHECK_EQ(e.vars, 5);
}

TEST(dimacs_satlib_percent_marker) {
  Collect c = parse("p cnf 3 1\n 1 -3 2 0\n%\n0\n\n");
  REQUIRE(c.clauses.size() == 1);
  CHECK((c.clauses[0] == std::vector<int>{1, -3, 2}));
}

TEST(dimacs_strict_errors) {
  CHECK_THROWS(parse("1 2 0\n"), DimacsError);                      // no header
  CHECK_THROWS(parse("p cnf 2 1\n1 3 0\n"), DimacsError);           // variable too large
  CHECK_THROWS(parse("p cnf 2 2\n1 2 0\n"), DimacsError);           // too few clauses
  CHECK_THROWS(parse("p cnf 2 1\n1 2 0\n-1 0\n"), DimacsError);     // too many clauses
  CHECK_THROWS(parse("p cnf 2 1\n1 2\n"), DimacsError);             // unterminated
  CHECK_THROWS(parse("p cnf 2 1\n1 x 0\n"), DimacsError);           // garbage
  CHECK_THROWS(parse("p cnf 2 1\n1 - 2 0\n"), DimacsError);         // lone minus
  CHECK_THROWS(parse("p cnf 2 1\n1 -0 0\n"), DimacsError);          // -0
  CHECK_THROWS(parse("p cnf 2 1\np cnf 2 1\n1 0\n"), DimacsError);  // second header
  CHECK_THROWS(parse("p cnf 2\n1 0\n"), DimacsError);               // short header
  CHECK_THROWS(parse("p dnf 2 1\n1 0\n"), DimacsError);             // wrong format
  CHECK_THROWS(parse("p cnf 2 1\n1 99999999999 0\n"), DimacsError);  // overflow
  CHECK_THROWS(parse("", true), DimacsError);                       // empty input
}

TEST(dimacs_relaxed) {
  Collect c = parse("p cnf 2 1\n1 3 0\n-1 2", false);
  REQUIRE(c.clauses.size() == 2);
  CHECK((c.clauses[1] == std::vector<int>{-1, 2}));
  Collect d = parse("1 2 0\n", false);
  CHECK_EQ(d.clauses.size(), 1u);
}

// The fast path for clause text and the state machine agree at every chunk boundary: numbers,
// signs and line ends cut anywhere, other whitespace, comments between clauses, errors.
TEST(dimacs_fast_path_chunk_boundaries) {
  const std::string text =
      "c head\np cnf 12 6\n1 -2 3 0\n -4\t5 0\r\n6  -7 0\nc mid\n  c indented\n12 -11 10 9 0\n-8 0\n007 -1 0\n";
  const std::vector<std::vector<int>> want = {{1, -2, 3}, {-4, 5}, {6, -7}, {12, -11, 10, 9}, {-8}, {7, -1}};
  for (size_t chunk = 0; chunk <= text.size(); ++chunk) {
    Collect c = parse(text, true, chunk);
    CHECK(c.clauses == want);
  }
  const std::vector<std::string> bad = {"p cnf 2 1\n1 -0 0\n", "p cnf 2 1\n1 - 2 0\n",       "p cnf 2 1\n1 2x 0\n",
                                        "p cnf 2 1\n1 3 0\n",  "p cnf 2 1\n1 -\n",           "p cnf 2 1\n1 -a 0\n",
                                        "p cnf 2 1\n12345678901 0\n", "p cnf 2 1\n1 2 0\n2 0\n"};
  for (const std::string& b : bad) {
    for (size_t chunk = 0; chunk <= b.size(); ++chunk) CHECK_THROWS(parse(b, true, chunk), DimacsError);
  }
  // Relaxed: a variable above the header's count is taken.
  for (size_t chunk = 0; chunk <= 16; ++chunk) {
    Collect r = parse("p cnf 2 1\n1 -3 0\n", false, chunk);
    REQUIRE(r.clauses.size() == 1);
    CHECK((r.clauses[0] == std::vector<int>{1, -3}));
  }
}
