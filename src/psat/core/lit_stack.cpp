#include "psat/core/lit_stack.hpp"

#include <cstdlib>
#include <cstring>
#include <new>

namespace psat {

LitStack::~LitStack() { std::free(data_); }

void LitStack::resize(size_t n) {
  if (n > cap_) grow(n);
  if (n > size_) std::memset(data_ + size_, 0, (n - size_) * sizeof(Lit));
  size_ = n;
}

void LitStack::grow(size_t need) {
  const size_t want = 2 * cap_ + 16;
  set_capacity(want > need ? want : need);
}

void LitStack::set_capacity(size_t n) {
  void* p = std::realloc(data_, n * sizeof(Lit));
  if (!p) throw std::bad_alloc();
  data_ = static_cast<Lit*>(p);
  cap_ = n;
}

}  // namespace psat
