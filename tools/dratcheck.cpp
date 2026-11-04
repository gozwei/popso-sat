// psat_dratcheck: small forward DRAT checker (RUP, then RAT on the first literal) for fuzzing
// and tests, built on tests/rup_checker.hpp. Reads text or binary DRAT. O(database) work per
// lemma: meant for small formulas only. Not a substitute for the competition's verified checkers.
//
//   psat_dratcheck <formula.cnf[.gz|.xz]> <proof>     prints 's VERIFIED' or 's NOT VERIFIED'

#include <cstdio>
#include <fstream>
#include <iterator>
#include <sstream>
#include <string>
#include <vector>

#include "psat/io/dimacs.hpp"
#include "psat/io/input.hpp"
#include "../tests/rup_checker.hpp"

namespace {

struct Collect : psat::DimacsHandler {
  int vars = 0;
  std::vector<std::vector<int>> clauses;
  void header(int v, int64_t) override { vars = v; }
  void clause(const int* lits, size_t n) override { clauses.emplace_back(lits, lits + n); }
};

bool is_binary(const std::string& s) {
  for (unsigned char c : s) {
    if (!(c == ' ' || c == '-' || c == 'd' || c == '\n' || c == '\r' || c == '\t' || (c >= '0' && c <= '9'))) return true;
  }
  return false;
}

// Binary DRAT -> text DRAT.
bool binary_to_text(const std::string& in, std::string& out) {
  std::ostringstream o;
  size_t i = 0;
  while (i < in.size()) {
    const unsigned char tag = static_cast<unsigned char>(in[i++]);
    if (tag != 'a' && tag != 'd') return false;
    if (tag == 'd') o << "d ";
    for (;;) {
      uint64_t u = 0;
      int shift = 0;
      for (;;) {
        if (i >= in.size() || shift > 35) return false;
        const unsigned char b = static_cast<unsigned char>(in[i++]);
        u |= static_cast<uint64_t>(b & 127) << shift;
        shift += 7;
        if (!(b & 128)) break;
      }
      if (u == 0) break;
      const long long lit = static_cast<long long>(u >> 1);
      o << ((u & 1) ? -lit : lit) << ' ';
    }
    o << "0\n";
  }
  out = o.str();
  return true;
}

}  // namespace

int main(int argc, char** argv) {
  if (argc < 3) {
    std::fprintf(stderr, "usage: psat_dratcheck <formula.cnf> <proof>\n");
    return 2;
  }
  Collect f;
  try {
    psat::DimacsParser parser(f, false);
    psat::stream_input(argv[1], [&](const char* d, size_t n) { parser.feed(d, n); });
    parser.finish();
    f.vars = std::max(f.vars, parser.max_var());
  } catch (const std::exception& e) {
    std::fprintf(stderr, "c error: %s\n", e.what());
    return 2;
  }
  std::ifstream in(argv[2], std::ios::binary);
  if (!in) {
    std::fprintf(stderr, "c error: cannot read %s\n", argv[2]);
    return 2;
  }
  std::string proof((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
  if (is_binary(proof)) {
    std::string text;
    if (!binary_to_text(proof, text)) {
      std::printf("c malformed binary proof\ns NOT VERIFIED\n");
      return 1;
    }
    proof.swap(text);
  }
  psat_test::RupChecker checker(f.vars);
  bool has_empty_input = false;
  for (const auto& c : f.clauses) {
    checker.add_original(c);
    has_empty_input = has_empty_input || c.empty();
  }
  const auto r = checker.check_text_proof(proof);
  if (!r.ok) {
    std::printf("c %s\ns NOT VERIFIED\n", r.error.c_str());
    return 1;
  }
  if (!r.has_empty && !has_empty_input) {
    std::printf("c no empty clause derived\ns NOT VERIFIED\n");
    return 1;
  }
  std::printf("c %zu lemmas, %zu deletions\ns VERIFIED\n", r.lemmas, r.deletions);
  return 0;
}
