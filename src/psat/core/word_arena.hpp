#pragma once
// A growable array of 32-bit words for the clause arena, grown with std::realloc instead of
// std::vector's allocate-copy-free. For large blocks the C library can grow in place (glibc remaps
// the pages with mremap), so the old and new arena do not have to coexist: with a vector, every
// growth of a multi-GB arena briefly needed 2-3 times its memory. New words are zeroed (as
// vector::resize does).

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>
#include <utility>

namespace psat {

class WordArena {
 public:
  WordArena() = default;
  WordArena(const WordArena&) = delete;
  WordArena& operator=(const WordArena&) = delete;
  WordArena(WordArena&& o) noexcept { swap(o); }
  WordArena& operator=(WordArena&& o) noexcept {
    swap(o);
    return *this;
  }
  ~WordArena() { std::free(data_); }

  uint32_t* data() { return data_; }
  const uint32_t* data() const { return data_; }
  size_t size() const { return size_; }
  size_t capacity() const { return capacity_; }
  bool empty() const { return size_ == 0; }
  uint32_t& operator[](size_t i) { return data_[i]; }
  const uint32_t& operator[](size_t i) const { return data_[i]; }

  void reserve(size_t n) {
    if (n > capacity_) set_capacity(n);
  }
  void resize(size_t n) {
    if (n > capacity_) set_capacity(n);
    if (n > size_) std::memset(data_ + size_, 0, (n - size_) * sizeof(uint32_t));
    size_ = n;
  }
  void clear() { size_ = 0; }
  void shrink_to_fit() {
    if (capacity_ > size_) set_capacity(size_);
  }

 private:
  void set_capacity(size_t n) {
    if (n == 0) {
      std::free(data_);
      data_ = nullptr;
      capacity_ = 0;
      return;
    }
    void* p = std::realloc(data_, n * sizeof(uint32_t));
    if (!p) throw std::bad_alloc();
    data_ = static_cast<uint32_t*>(p);
    capacity_ = n;
  }
  void swap(WordArena& o) noexcept {
    std::swap(data_, o.data_);
    std::swap(size_, o.size_);
    std::swap(capacity_, o.capacity_);
  }

  uint32_t* data_ = nullptr;
  size_t size_ = 0, capacity_ = 0;
};

}  // namespace psat
