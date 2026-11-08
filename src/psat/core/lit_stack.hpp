#pragma once
// A stack of literals for the solver's trail: the part of std::vector's interface the trail uses,
// with push_back's growth path out of line (lit_stack.cpp). With std::vector the inlined
// reallocation path made the assignment too large to inline into propagation, which then paid a
// call per implied literal.

#include <cstddef>

#include "psat/core/types.hpp"

namespace psat {

class LitStack {
 public:
  LitStack() = default;
  LitStack(const LitStack&) = delete;
  LitStack& operator=(const LitStack&) = delete;
  ~LitStack();

  size_t size() const { return size_; }
  size_t capacity() const { return cap_; }
  bool empty() const { return size_ == 0; }
  Lit* data() { return data_; }
  const Lit* data() const { return data_; }
  Lit* begin() { return data_; }
  Lit* end() { return data_ + size_; }
  const Lit* begin() const { return data_; }
  const Lit* end() const { return data_ + size_; }
  Lit& operator[](size_t i) { return data_[i]; }
  const Lit& operator[](size_t i) const { return data_[i]; }
  Lit& back() { return data_[size_ - 1]; }

  void push_back(Lit l) {
    if (size_ == cap_) grow(size_ + 1);
    data_[size_++] = l;
  }
  void reserve(size_t n) {
    if (n > cap_) set_capacity(n);
  }
  // Truncates, or extends with zeros (as std::vector::resize).
  void resize(size_t n);
  void clear() { size_ = 0; }

 private:
  void grow(size_t need);
  void set_capacity(size_t n);

  Lit* data_ = nullptr;
  size_t size_ = 0, cap_ = 0;
};

}  // namespace psat
