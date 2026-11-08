#include "psat/io/dimacs.hpp"

#include <cctype>
#include <cstring>
#include <sstream>

#include "psat/core/types.hpp"

namespace psat {

namespace {

inline bool is_space(char c) { return c == ' ' || c == '\t' || c == '\r' || c == '\f' || c == '\v'; }
inline bool is_digit(char c) { return c >= '0' && c <= '9'; }

}  // namespace

DimacsParser::DimacsParser(DimacsHandler& handler, bool strict) : handler_(handler), strict_(strict) {}

void DimacsParser::error(const std::string& what) const {
  throw DimacsError("line " + std::to_string(line_) + ": " + what);
}

void DimacsParser::end_number() {
  if (number_ == 0) {
    end_clause();
    return;
  }
  const int v = static_cast<int>(number_);
  if (has_header_ && v > header_vars_) {
    if (strict_) error("variable " + std::to_string(v) + " exceeds the header's maximum " + std::to_string(header_vars_));
  }
  if (v > max_var_) max_var_ = v;
  clause_.push_back(negative_ ? -v : v);
}

void DimacsParser::end_clause() {
  if (!has_header_ && strict_) error("clause before the 'p cnf' header");
  if (has_header_ && strict_ && clauses_ >= header_clauses_) {
    error("more clauses than the header's " + std::to_string(header_clauses_));
  }
  ++clauses_;
  literals_ += static_cast<int64_t>(clause_.size());
  handler_.clause(clause_.data(), clause_.size());
  clause_.clear();
}

void DimacsParser::parse_header() {
  if (has_header_) error("second 'p' header line");
  if (clauses_ > 0 || !clause_.empty()) {
    if (strict_) error("'p cnf' header after clauses");
  }
  std::istringstream in(header_line_);
  std::string p, fmt, extra;
  long long vars = -1, clauses = -1;
  in >> p >> fmt;
  if (p != "p" || fmt != "cnf") error("expected 'p cnf <variables> <clauses>', got '" + header_line_ + "'");
  if (!(in >> vars >> clauses)) error("malformed header '" + header_line_ + "'");
  if (in >> extra) error("trailing text in header '" + header_line_ + "'");
  if (vars < 0 || clauses < 0) error("negative numbers in header '" + header_line_ + "'");
  if (vars > kMaxVar) error("too many variables in header (maximum " + std::to_string(kMaxVar) + ")");
  has_header_ = true;
  header_vars_ = static_cast<int>(vars);
  header_clauses_ = clauses;
  if (max_var_ > header_vars_ && strict_) error("earlier variable exceeds the header's maximum");
  handler_.header(header_vars_, header_clauses_);
}

void DimacsParser::feed(const char* data, size_t n) {
  const char* p = data;
  const char* const end = data + n;
  while (p != end) {
    if (state_ == State::kNumber) {
      // Fast path: the rest of a number in a tight loop.
      int64_t num = number_;
      while (p != end && is_digit(*p)) {
        num = num * 10 + (*p++ - '0');
        if (num > kMaxVar) error("variable index too large (maximum " + std::to_string(kMaxVar) + ")");
      }
      number_ = num;
      if (p == end) return;
      const char c = *p++;
      end_number();
      if (c == '\n') {
        ++line_;
        state_ = State::kLineStart;
      } else if (is_space(c)) {
        state_ = State::kInLine;
      } else {
        error(std::string("unexpected character '") + c + "' after a number");
      }
      continue;
    }
    if (state_ == State::kInLine || state_ == State::kLineStart) {
      // Fast path for clause text: single spaces, newlines and numbers, each number read in one
      // go. Anything else (comments, the header, other whitespace, malformed text, a sign or a
      // number cut off by the end of the chunk) is left to the state machine below, which then
      // comes back here. The checks and errors are the state machine's, in the same order.
      while (p != end) {
        char c = *p;
        if (c == ' ') {
          ++p;
          state_ = State::kInLine;
          continue;
        }
        if (c == '\n') {
          ++p;
          ++line_;
          state_ = State::kLineStart;
          continue;
        }
        const char* q = p;
        bool neg = false;
        if (c == '-') {
          if (q + 1 == end || q[1] < '1' || q[1] > '9') break;
          neg = true;
          c = *++q;
        } else if (!is_digit(c)) {
          break;
        }
        int64_t num = c - '0';
        for (++q; q != end && is_digit(*q); ++q) {
          num = num * 10 + (*q - '0');
          if (num > kMaxVar) error("variable index too large (maximum " + std::to_string(kMaxVar) + ")");
        }
        negative_ = neg;
        number_ = num;
        if (q == end) {  // continued in the next chunk
          state_ = State::kNumber;
          return;
        }
        const char t = *q;
        p = q + 1;
        if (num != 0 && !(has_header_ && num > header_vars_)) {  // end_number(), the common case
          const int v = static_cast<int>(num);
          if (v > max_var_) max_var_ = v;
          clause_.push_back(neg ? -v : v);
        } else {
          end_number();
        }
        if (t == '\n') {
          ++line_;
          state_ = State::kLineStart;
        } else if (is_space(t)) {
          state_ = State::kInLine;
        } else {
          error(std::string("unexpected character '") + t + "' after a number");
        }
      }
      if (p == end) return;
    }
    const char c = *p++;
    switch (state_) {
      case State::kLineStart:
        if (c == 'c') {
          state_ = State::kComment;
        } else if (c == 'p') {
          header_line_.assign(1, 'p');
          state_ = State::kHeader;
        } else if (c == '%') {
          state_ = State::kDone;
        } else if (c == '\n') {
          ++line_;
        } else if (is_space(c)) {
          state_ = State::kInLine;
        } else if (is_digit(c)) {
          negative_ = false;
          number_ = c - '0';
          state_ = State::kNumber;
        } else if (c == '-') {
          state_ = State::kMinus;
        } else {
          error(std::string("unexpected character '") + c + "'");
        }
        break;
      case State::kInLine:
        if (c == ' ') {
        } else if (is_digit(c)) {
          negative_ = false;
          number_ = c - '0';
          state_ = State::kNumber;
        } else if (c == '-') {
          state_ = State::kMinus;
        } else if (c == '\n') {
          ++line_;
          state_ = State::kLineStart;
        } else if (is_space(c)) {
        } else if (c == 'c' && clause_.empty()) {
          state_ = State::kComment;  // comment after leading whitespace
        } else if (c == '%' && clause_.empty()) {
          state_ = State::kDone;
        } else {
          error(std::string("unexpected character '") + c + "'");
        }
        break;
      case State::kMinus:
        if (!is_digit(c) || c == '0') error("expected a nonzero digit after '-'");
        negative_ = true;
        number_ = c - '0';
        state_ = State::kNumber;
        break;
      case State::kNumber:
        break;  // handled above
      case State::kComment: {
        // Skip to the end of the line in one go.
        const void* nl = std::memchr(p - 1, '\n', static_cast<size_t>(end - (p - 1)));
        if (!nl) return;
        p = static_cast<const char*>(nl) + 1;
        ++line_;
        state_ = State::kLineStart;
        break;
      }
      case State::kHeader:
        if (c == '\n') {
          parse_header();
          ++line_;
          state_ = State::kLineStart;
        } else {
          if (header_line_.size() > 1000) error("header line too long");
          header_line_.push_back(c);
        }
        break;
      case State::kDone:
        return;
    }
  }
}

void DimacsParser::finish() {
  if (state_ == State::kNumber) end_number();
  if (state_ == State::kMinus) error("unexpected end of input after '-'");
  if (state_ == State::kHeader) parse_header();
  if (!clause_.empty()) {
    if (strict_) error("last clause is not terminated by 0");
    end_clause();
  }
  if (!has_header_) {
    if (strict_) error("missing 'p cnf' header");
    return;
  }
  if (strict_ && clauses_ != header_clauses_) {
    error("found " + std::to_string(clauses_) + " clauses but the header says " + std::to_string(header_clauses_));
  }
}

}  // namespace psat
