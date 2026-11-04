#include "psat/core/options.hpp"

#include <cerrno>
#include <cstdlib>
#include <stdexcept>

namespace psat {

namespace {

int64_t parse_value(const std::string& name, const std::string& value, int64_t lo, int64_t hi) {
  if (value == "true") return 1;
  if (value == "false") return 0;
  errno = 0;
  char* end = nullptr;
  const long long v = std::strtoll(value.c_str(), &end, 10);
  // Accept scientific shorthand like 1e6 for large limits.
  if (end && *end == 'e') {
    char* end2 = nullptr;
    const long exp = std::strtol(end + 1, &end2, 10);
    if (end2 && *end2 == '\0' && exp >= 0 && exp <= 18) {
      long double x = static_cast<long double>(v);
      for (long i = 0; i < exp; ++i) x *= 10;
      if (x < static_cast<long double>(lo) || x > static_cast<long double>(hi)) {
        throw std::invalid_argument("option --" + name + ": value " + value + " out of range");
      }
      return static_cast<int64_t>(x);
    }
  }
  if (value.empty() || errno != 0 || !end || *end != '\0') {
    throw std::invalid_argument("option --" + name + ": invalid value '" + value + "'");
  }
  if (v < lo || v > hi) {
    throw std::invalid_argument("option --" + name + ": value " + value + " out of range [" + std::to_string(lo) +
                                ", " + std::to_string(hi) + "]");
  }
  return v;
}

}  // namespace

bool Options::set(const std::string& name, const std::string& value) {
#define PSAT_OPTION_SET(n, def, lo, hi, desc) \
  if (name == #n) {                           \
    n = parse_value(name, value, lo, hi);     \
    return true;                              \
  }
  PSAT_OPTIONS(PSAT_OPTION_SET)
#undef PSAT_OPTION_SET
  return false;
}

bool Options::has(const std::string& name) const {
#define PSAT_OPTION_HAS(n, def, lo, hi, desc) \
  if (name == #n) return true;
  PSAT_OPTIONS(PSAT_OPTION_HAS)
#undef PSAT_OPTION_HAS
  return false;
}

void Options::print_help(std::FILE* out) {
#define PSAT_OPTION_HELP(n, def, lo, hi, desc) \
  std::fprintf(out, "  --%-18s %-10lld %s [%lld..%lld]\n", #n "=<n>", static_cast<long long>(def), desc, \
               static_cast<long long>(lo), static_cast<long long>(hi));
  PSAT_OPTIONS(PSAT_OPTION_HELP)
#undef PSAT_OPTION_HELP
}

void Options::print_changed(std::FILE* out) const {
#define PSAT_OPTION_CHANGED(n, def, lo, hi, desc) \
  if (n != def) std::fprintf(out, "c option --%s=%lld\n", #n, static_cast<long long>(n));
  PSAT_OPTIONS(PSAT_OPTION_CHANGED)
#undef PSAT_OPTION_CHANGED
}

}  // namespace psat
