#pragma once
// DIMACS CNF push parser: feed() it the input in chunks of any size, then finish().
//
// Accepted: comment lines starting with 'c' (also between clauses), one header line
// "p cnf <vars> <clauses>", clauses spread over any number of lines, and the SATLIB end marker
// '%' (everything after it is ignored). Whitespace is space, tab, CR, LF, FF and VT.
//
// Strict mode (default) errors on: a missing header, clauses before the header, a variable
// larger than the header's, a different number of clauses than the header's, and a last clause
// without its terminating 0. Relaxed mode accepts these (the variable count grows as needed).
// Always errors on: malformed numbers and headers, a second header, variables above kMaxVar.

#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

namespace psat {

class DimacsError : public std::runtime_error {
 public:
  using std::runtime_error::runtime_error;
};

class DimacsHandler {
 public:
  virtual ~DimacsHandler() = default;
  virtual void header(int vars, int64_t clauses) = 0;
  // One clause in DIMACS literals, without the terminating 0.
  virtual void clause(const int* lits, size_t n) = 0;
};

class DimacsParser {
 public:
  explicit DimacsParser(DimacsHandler& handler, bool strict = true);

  void feed(const char* data, size_t n);
  void finish();

  bool has_header() const { return has_header_; }
  int header_vars() const { return header_vars_; }
  int64_t header_clauses() const { return header_clauses_; }
  int max_var() const { return max_var_; }
  int64_t clauses() const { return clauses_; }
  int64_t literals() const { return literals_; }

 private:
  enum class State { kLineStart, kInLine, kNumber, kMinus, kComment, kHeader, kDone };

  [[noreturn]] void error(const std::string& what) const;
  void end_number();
  void end_clause();
  void parse_header();

  DimacsHandler& handler_;
  bool strict_;
  State state_ = State::kLineStart;
  bool negative_ = false;
  int64_t number_ = 0;
  std::vector<int> clause_;
  std::string header_line_;
  bool has_header_ = false;
  int header_vars_ = 0;
  int64_t header_clauses_ = 0;
  int max_var_ = 0;
  int64_t clauses_ = 0;
  int64_t literals_ = 0;
  int64_t line_ = 1;
};

}  // namespace psat
