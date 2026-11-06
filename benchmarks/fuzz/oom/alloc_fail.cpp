// Allocation failure injection (testing only, not part of the solver): linked into the CLI, the
// global operator new throws std::bad_alloc at allocation number PSAT_FAIL_AT (1-based); with
// PSAT_FAIL_PERSIST set, every later allocation fails too. PSAT_ALLOC_COUNT set: prints the number
// of allocations at exit ('c allocs N' on stderr). Driven by benchmarks/fuzz/oomfuzz.py:
//   c++ -std=c++20 -O2 -DNDEBUG -DPSAT_VERSION='"oom"' -Isrc apps/popso_sat_main.cpp \
//       benchmarks/fuzz/oom/alloc_fail.cpp build/libpsat_lib.a -o build/popso-sat-oom
#include <cstdio>
#include <cstdlib>
#include <new>

namespace {
long long g_fail_at = -1;
bool g_persist = false;
long long g_count = 0;
bool g_init = false;

void report() { std::fprintf(stderr, "c allocs %lld\n", g_count); }

void init() {
  if (g_init) return;
  g_init = true;
  if (const char* s = std::getenv("PSAT_FAIL_AT")) g_fail_at = std::atoll(s);
  g_persist = std::getenv("PSAT_FAIL_PERSIST") != nullptr;
  if (std::getenv("PSAT_ALLOC_COUNT")) std::atexit(report);
}

bool should_fail() {
  init();
  ++g_count;
  return g_fail_at > 0 && (g_count == g_fail_at || (g_persist && g_count > g_fail_at));
}

void* alloc(std::size_t n) {
  if (should_fail()) throw std::bad_alloc();
  void* p = std::malloc(n ? n : 1);
  if (!p) throw std::bad_alloc();
  return p;
}

void* alloc_aligned(std::size_t n, std::align_val_t al) {
  if (should_fail()) throw std::bad_alloc();
  void* p = nullptr;
  std::size_t a = static_cast<std::size_t>(al);
  if (a < sizeof(void*)) a = sizeof(void*);
  if (posix_memalign(&p, a, n ? n : 1) != 0) throw std::bad_alloc();
  return p;
}
}  // namespace

void* operator new(std::size_t n) { return alloc(n); }
void* operator new[](std::size_t n) { return alloc(n); }
void* operator new(std::size_t n, const std::nothrow_t&) noexcept {
  try {
    return alloc(n);
  } catch (...) {
    return nullptr;
  }
}
void* operator new[](std::size_t n, const std::nothrow_t&) noexcept {
  try {
    return alloc(n);
  } catch (...) {
    return nullptr;
  }
}
void* operator new(std::size_t n, std::align_val_t al) { return alloc_aligned(n, al); }
void* operator new[](std::size_t n, std::align_val_t al) { return alloc_aligned(n, al); }
void operator delete(void* p) noexcept { std::free(p); }
void operator delete[](void* p) noexcept { std::free(p); }
void operator delete(void* p, std::size_t) noexcept { std::free(p); }
void operator delete[](void* p, std::size_t) noexcept { std::free(p); }
void operator delete(void* p, std::align_val_t) noexcept { std::free(p); }
void operator delete[](void* p, std::align_val_t) noexcept { std::free(p); }
void operator delete(void* p, std::size_t, std::align_val_t) noexcept { std::free(p); }
void operator delete[](void* p, std::size_t, std::align_val_t) noexcept { std::free(p); }
