// macOS stand-in for `ulimit -v` (setrlimit(RLIMIT_AS) fails on macOS), testing only: interposes
// the malloc family and returns NULL (ENOMEM) once the live heap bytes would exceed
// PSAT_HEAP_LIMIT_MB, so out of memory hits the real allocation paths (operator new, realloc of
// the clause arena, the C++ runtime) at a chosen size.
//   cc -O2 -dynamiclib benchmarks/fuzz/oom/heaplimit.c -o build/heaplimit.dylib
//   env DYLD_INSERT_LIBRARIES=build/heaplimit.dylib PSAT_HEAP_LIMIT_MB=1300 build/popso-sat big.cnf.xz
// (DYLD_* variables are dropped when a system binary such as nice or sh runs: set them last.)
#include <errno.h>
#include <malloc/malloc.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static _Atomic long long live = 0;
static long long limit = -1;  // bytes; -1 = not read yet, 0 = no limit
static _Atomic long long failures = 0;

static long long get_limit(void) {
  if (limit < 0) {
    const char* s = getenv("PSAT_HEAP_LIMIT_MB");
    limit = s ? atoll(s) << 20 : 0;
  }
  return limit;
}

static int over(size_t n) {
  long long l = get_limit();
  if (l > 0 && atomic_load(&live) + (long long)n > l) {
    if (atomic_fetch_add(&failures, 1) == 0) {
      static const char msg[] = "c heaplimit: allocation refused\n";
      fwrite(msg, 1, sizeof(msg) - 1, stderr);
    }
    errno = ENOMEM;
    return 1;
  }
  return 0;
}

static void* my_malloc(size_t n) {
  if (over(n)) return NULL;
  void* p = malloc(n);
  if (p) atomic_fetch_add(&live, (long long)malloc_size(p));
  return p;
}

static void* my_calloc(size_t c, size_t n) {
  if (n && c > (size_t)-1 / n) return calloc(c, n);
  if (over(c * n)) return NULL;
  void* p = calloc(c, n);
  if (p) atomic_fetch_add(&live, (long long)malloc_size(p));
  return p;
}

static void* my_realloc(void* q, size_t n) {
  size_t old = q ? malloc_size(q) : 0;
  if (n > old && over(n - old)) return NULL;
  void* p = realloc(q, n);
  if (p || n == 0) {
    atomic_fetch_sub(&live, (long long)old);
    if (p) atomic_fetch_add(&live, (long long)malloc_size(p));
  }
  return p;
}

static void my_free(void* p) {
  if (p) atomic_fetch_sub(&live, (long long)malloc_size(p));
  free(p);
}

static int my_posix_memalign(void** r, size_t a, size_t n) {
  if (over(n)) return ENOMEM;
  int e = posix_memalign(r, a, n);
  if (!e && *r) atomic_fetch_add(&live, (long long)malloc_size(*r));
  return e;
}

static void* my_aligned_alloc(size_t a, size_t n) {
  if (over(n)) return NULL;
  void* p = aligned_alloc(a, n);
  if (p) atomic_fetch_add(&live, (long long)malloc_size(p));
  return p;
}

#define INTERPOSE(repl, orig)                                                         \
  __attribute__((used)) static struct {                                              \
    const void* r;                                                                    \
    const void* o;                                                                    \
  } interpose_##orig __attribute__((section("__DATA,__interpose"))) = {(const void*)repl, \
                                                                       (const void*)orig}

INTERPOSE(my_malloc, malloc);
INTERPOSE(my_calloc, calloc);
INTERPOSE(my_realloc, realloc);
INTERPOSE(my_free, free);
INTERPOSE(my_posix_memalign, posix_memalign);
INTERPOSE(my_aligned_alloc, aligned_alloc);
