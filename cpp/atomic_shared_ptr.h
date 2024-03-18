#include <atomic>
#include <cstdio>
#include <cstddef>
#include <cstdlib>
#include <cassert>

namespace ivo
{

#define FREE_BITS_MOST_SIGNIFICANT 16
#define FREE_BITS_LEAST_SIGNIFICANT 3
#define TAG_BITS (FREE_BITS_MOST_SIGNIFICANT + FREE_BITS_LEAST_SIGNIFICANT)

// Constant 'P'
#define MAX_THREADS (1 << 16)

// Constant 'C'
#define MAX_WEIGHT ((1UL << TAG_BITS) - 1)

#define MAX_REFCOUNT ((1UL<<63) - 1)

template<class T>
class atomic_shared_ptr;

template<class T>
struct ptr_control_block {
  friend class ivo::atomic_shared_ptr<T>;
  private:
    std::atomic<uint64_t> reference_count;
    T *ptr;

  public:
    ptr_control_block(uint64_t rc, T *ptr): reference_count(rc), ptr(ptr) {}

    inline void rc_increment(uint64_t count) {
      uint64_t rc = this->reference_count.fetch_add(count, std::memory_order_acquire);
      if (rc + count > MAX_REFCOUNT) {
        printf("Reference count overflow\n");
        abort();
      }
    }
    inline void rc_decrement(uint64_t count) {
      uint64_t rc = this->reference_count.fetch_sub(count, std::memory_order_release);
      if (rc == count) {
        // Load as an acquire memory barrier
        this->reference_count.load(std::memory_order_acquire);
        delete this->ptr;
        delete this;
      } else if (rc < count) {
        printf("Negative reference count\n");
        abort();
      }
    }

    // Decrements a reference count, with the assumption that the reference count remains positive
    inline void rc_decrement_live(uint64_t count) {
      uint64_t rc = this->reference_count.fetch_sub(count, std::memory_order_release);
      if (rc == count) {
        printf("Reference count is zero while object is still live\n");
        abort();
      } else if (rc < count) {
        printf("Negative reference count\n");
        abort();
      }
    }
};

template<class T>
struct shared_ptr {
  friend class ivo::atomic_shared_ptr<T>;
  private:
    T *ptr;
    ptr_control_block<T> *control_block;

    void drop() {
      if (this->control_block != nullptr) {
        this->control_block->rc_decrement(1);
      }
    }
    void forget() {
      this->control_block = nullptr;
      this->ptr = nullptr;
    }

    shared_ptr(ivo::ptr_control_block<T> *control_block, T *ptr) {
      this->control_block = control_block;
      this->ptr = ptr;
    }

  public:
    shared_ptr(): ptr(nullptr), control_block(nullptr) {}
    shared_ptr(nullptr_t): ptr(nullptr), control_block(nullptr) {}
    shared_ptr(T *ptr) {
      assert(ptr != nullptr);
      this->ptr = ptr;
      if (ptr == nullptr) {
        this->control_block = nullptr;
      } else {
        this->control_block = new ivo::ptr_control_block<T>(1, ptr);
      }
    }
    shared_ptr(const shared_ptr &other) {
      // Copy constructor (.clone() in Rust)
      if (other.control_block != nullptr) {
        other.control_block->rc_increment(1);
      }
      this->ptr = other.ptr;
      this->control_block = other.control_block;
    }
    shared_ptr(shared_ptr &&other) {
      // Move constructor. Only copy the data.
      this->ptr = other.ptr;
      this->control_block = other.control_block;

      other.ptr = nullptr;
      other.control_block = nullptr;
    }
    ~shared_ptr() {
      // Destructor (.drop() in Rust)
      this->drop();
    }
    shared_ptr& operator=(const shared_ptr& other) {
      // Copy assignment. Equivalent in Rust is .drop() on current value, and .clone() on new value.
      this->drop();
      if (other.control_block != nullptr) {
        other.control_block->rc_increment(1);
      }
      this->ptr = other.ptr;
      this->control_block = other.control_block;
      return *this;
    }
    shared_ptr& operator=(shared_ptr&& other) {
      // Move assignment. Drop the current value, and move the new value.
      this->drop();

      this->ptr = other.ptr;
      this->control_block = other.control_block;

      other.ptr = nullptr;
      other.control_block = nullptr;
      return *this;
    }

    T* get() const {
      return this->ptr;
    }
    T& operator*() const {
      return *this->ptr;
    }
    T* operator->() const {
      return this->ptr;
    }

    template<typename... Args>
    static shared_ptr make_shared(Args &&... args) {
      auto ptr = new T(std::forward<Args>(args)...);
      return shared_ptr(ptr);
    }

    explicit operator bool() const { return get() != nullptr; }
};

template<class T>
ptr_control_block<T>* unpack_ptr(size_t value) {
  size_t ptr = (((ptrdiff_t) (value << TAG_BITS)) >> FREE_BITS_MOST_SIGNIFICANT);
  return (ptr_control_block<T>*) ptr;
}

inline uint64_t unpack_weight(size_t value) {
  size_t bits = sizeof(size_t) * 8;
  return value >> (bits - TAG_BITS);
}

template<class T>
size_t pack(ptr_control_block<T>* ptr, uint64_t weight) {
  if (weight > MAX_WEIGHT) {
    printf("Weight is too large\n");
    abort();
  }
  size_t bits = sizeof(size_t) * 8;
  size_t ptr_mask = (1UL << (bits - FREE_BITS_MOST_SIGNIFICANT)) - 1;
  return (((size_t) ptr & ptr_mask) >> FREE_BITS_LEAST_SIGNIFICANT)
    | (weight << (bits - TAG_BITS));
}

inline size_t pack_weight(uint64_t weight) {
  size_t bits = sizeof(size_t) * 8;
  return weight << (bits - TAG_BITS);
}

template<class T>
void release(size_t value) {
  ptr_control_block<T> *control_block = unpack_ptr<T>(value);
  if (control_block == nullptr) return;
  uint64_t weight = unpack_weight(value);
  control_block->rc_decrement(weight);
}

inline std::memory_order memory_order_load(std::memory_order order) {
  if (order == std::memory_order_release) {
    return std::memory_order_relaxed;
  }
  if (order == std::memory_order_acq_rel) {
    return std::memory_order_acquire;
  }
  return order;
}
// Assumes that the memory orders are both for loads, or both for acquires.
// This function is incorrect if the orders are acquire and release, but that input is now not allowed
inline std::memory_order memory_order_max(std::memory_order order1, std::memory_order order2) {
  if (order1 >= order2) {
    return order1;
  } else {
    return order2;
  }
}

template<class T>
struct atomic_shared_ptr {
  private:
    std::atomic<size_t> value;

    void increase_weight(ivo::ptr_control_block<T> *control_block, uint64_t weight) {
      // Assumes control_block != nullptr
      // Increase reference count by 'MAX_WEIGHT - weight', and then attempt to increase weight by 'MAX_WEIGHT - weight'.
      control_block->rc_increment(MAX_WEIGHT - weight);

      // cas-loop to update the value in the atomic shared pointer.
      // Note that we use a strong cas (opposed to a weak cas), to make this wait-free.
      // We could as an optimistic optimisation start with weak cas, and after X spurious fails switch to strong cas.

      uint64_t current_weight = weight;
      while (true) {
        size_t expected = pack<T>(control_block, current_weight);
        size_t new_value = pack<T>(control_block, current_weight + MAX_WEIGHT - weight);
        if (this->value.compare_exchange_strong(expected, new_value, std::memory_order_relaxed, std::memory_order_relaxed)) {
          // Success!
          return;
        }
        // CAS failed, as the pointer or weight has changed
        if (unpack_ptr<T>(expected) != control_block) {
          // The atomic_shared_ptr now refers to a different object.
          // This makes this attempt to increase the weight redundant.
          break;
        }
        uint64_t new_weight = unpack_weight(expected);
        if (new_weight > current_weight) {
          // The weight was already incremented by another thread.
          // No need for this thread to increment the weight.
          break;
        }
        if (new_weight == current_weight) {
          printf("Spurious fails should be impossible with strong compare_exchange\n");
          abort();
        }
        current_weight = new_weight;
      }

      // CAS didn't succeed, because either
      // 1. Another thread changed the pointer.
      // 2. Another thread incremented the weight.
      // In both cases the weight is (or has been) above MAX_THREADS,
      // hence this thread doesn't need to increase it.

      // Revert the change of the reference_count.
      // Note that this will not lower the reference count to 0,
      // as this thread still holds a reference to the object.
      control_block->rc_decrement_live(MAX_WEIGHT - weight);
    }
  public:
    atomic_shared_ptr(): value(0) {}
    atomic_shared_ptr(shared_ptr<T> shared_pointer) {
      // `- 1` as we 'use' the existing reference of shared_pointer.
      if (shared_pointer.control_block != nullptr) {
        shared_pointer.control_block->rc_increment(MAX_WEIGHT - 1);
      }
      this->value = pack<T>(shared_pointer.control_block, MAX_WEIGHT);

      shared_pointer.forget();
    }

    ~atomic_shared_ptr() {
      size_t value = this->value.load(std::memory_order_relaxed);
      release<T>(value);
    }

    shared_ptr<T> load(std::memory_order order = std::memory_order_seq_cst) {
      size_t result = this->value.fetch_sub(pack_weight(1), order);
      ptr_control_block<T> *control_block = unpack_ptr<T>(result);
      if (control_block == nullptr) return shared_ptr<T>(nullptr, nullptr);
      uint64_t weight = unpack_weight(result);
      if (weight - 1 < MAX_THREADS) {
        // 'weight - 1' as fetch_sub returns the value *before* the increment
        this->increase_weight(control_block, weight - 1);
      }
      return shared_ptr<T>(control_block, control_block->ptr);
    }

    void store(shared_ptr<T> shared_pointer, std::memory_order order = std::memory_order_seq_cst) {
      ptr_control_block<T> *control_block = shared_pointer.control_block;
      shared_pointer.forget();
      if (control_block != nullptr) {
        // `- 1` as we 'use' the existing reference of shared_pointer.
        control_block->rc_increment(MAX_WEIGHT - 1);
      }
      size_t old = this->value.exchange(pack<T>(control_block, MAX_WEIGHT), order);
      release<T>(old);
    }

    // Variant of compare_exchange_weak that doesn't write the observed value to 'expected'.
    // In case the compare-and-set fails, you should thus probably manually read the value
    // using .load().
    bool compare_and_set(shared_ptr<T> expected, shared_ptr<T> new_ptr,
        std::memory_order success_order = std::memory_order_seq_cst,
        std::memory_order failure_order = std::memory_order_seq_cst) {
      ptr_control_block<T> *new_cb = new_ptr.control_block;
      if (new_cb != nullptr) {
        // '- 1' as we consume the reference of the shared_ptr
        new_cb->rc_increment(MAX_WEIGHT - 1);
      }
      new_ptr.forget();

      size_t observed = this->value.load(memory_order_max(memory_order_load(success_order), failure_order));
      while (true) {
        ptr_control_block<T> *observed_cb = unpack_ptr<T>(observed);
        if (observed_cb != expected.control_block) {
          // Revert change to reference count of 'new_ptr'
          if (new_cb != nullptr) {
            new_cb->rc_decrement(MAX_WEIGHT);
          }
          return false;
        }
        if (this->value.compare_exchange_weak(observed, pack<T>(new_cb, MAX_WEIGHT), success_order, failure_order)) {
          release<T>(observed);
          return true;
        }
      }
    }

    bool compare_exchange_weak(shared_ptr<T> &expected, shared_ptr<T> new_ptr,
        std::memory_order success_order = std::memory_order_seq_cst,
        std::memory_order failure_order = std::memory_order_seq_cst) {
      // We could make this weaker, as compare_and_set is strong (and requires a loop).
      if (this->compare_and_set(expected, new_ptr, success_order, failure_order)) {
        return true;
      } else {
        expected = this->load(failure_order);
        return false;
      }
    }

    bool compare_exchange_strong(shared_ptr<T> &expected, shared_ptr<T> new_ptr,
        std::memory_order success_order = std::memory_order_seq_cst,
        std::memory_order failure_order = std::memory_order_seq_cst) {
      while (true) {
        if (this->compare_and_set(expected, new_ptr, success_order, failure_order)) {
          return true;
        } else {
          shared_ptr<T> observed = this->load(failure_order);
          if (observed.control_block == expected.control_block) {
            // Unlikely, but it can happen that the compare-and-set fails as
            // the atomic shared pointer then contains a different pointer,
            // and that we now do find the expected value when we load it
            // again. If that happens, we just try again.
            continue;
          } else {
            expected = observed;
            return false;
          }
        }
      }
    }

    // Don't allow copies of atomic shared pointers
    atomic_shared_ptr(atomic_shared_ptr const&) = delete;
    atomic_shared_ptr& operator=(atomic_shared_ptr const&) = delete;
};

}
