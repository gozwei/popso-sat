// Test runner: `psat_tests [substring]` runs all tests whose name contains
// the substring. Returns nonzero if any test fails.

#include <cstring>
#include <exception>

#include "test_framework.hpp"

int main(int argc, char** argv) {
  const char* filter = argc > 1 ? argv[1] : "";
  int run = 0, failed = 0;
  for (const auto& t : psat_test::registry()) {
    if (*filter && !std::strstr(t.name, filter)) continue;
    ++run;
    const int before = psat_test::context().failures;
    try {
      t.fn();
    } catch (const psat_test::RequireFailed&) {
      // already reported
    } catch (const std::exception& e) {
      psat_test::report_failure(t.file, 0, std::string("unexpected exception: ") + e.what());
    } catch (...) {
      psat_test::report_failure(t.file, 0, "unexpected unknown exception");
    }
    const bool ok = psat_test::context().failures == before;
    if (!ok) ++failed;
    std::printf("[%s] %s\n", ok ? " OK " : "FAIL", t.name);
  }
  std::printf("\n%d tests, %d passed, %d failed (%d checks, %d failed)\n", run, run - failed, failed,
              psat_test::context().checks, psat_test::context().failures);
  if (run == 0) std::printf("no tests matched filter '%s'\n", filter);
  return failed == 0 && run > 0 ? 0 : 1;
}
