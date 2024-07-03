use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::mem;

const FREE_BITS_MOST_SIGNIFICANT: usize = 16;
const FREE_BITS_LEAST_SIGNIFICANT: usize = 3; // Alignment of the AtomicUsize (assuming a 64-bit architecture)
const TAG_BITS: usize = FREE_BITS_MOST_SIGNIFICANT + FREE_BITS_LEAST_SIGNIFICANT;

// Constant 'P'
const MAX_THREADS: usize = 1 << 16;

// Constant 'C'
const MAX_WEIGHT: usize = (1 << TAG_BITS) - 1;

const MAX_REFCOUNT: usize = isize::MAX as usize;

#[repr(C)]
pub struct ArcObject<T> {
  reference_count: AtomicUsize,
  pub value: T
}

impl<T> ArcObject<T> {
  #[inline(always)]
  fn rc_increment(ptr: NonNull<ArcObject<T>>, count: usize) {
    let rc = unsafe { &(*ptr.as_ptr()).reference_count };
    if count == 0 { return; }
    let old = rc.fetch_add(count, Ordering::Acquire);
    if old + count > MAX_REFCOUNT {
      error_rc_overflow();
    }
  }

  #[inline(always)]
  fn rc_decrement(ptr: NonNull<ArcObject<T>>, count: usize) {
    let rc = unsafe { &(*ptr.as_ptr()).reference_count };
    if count == 0 { return; }
    let old = rc.fetch_sub(count, Ordering::Release);
    if old < count {
      error_negative_rc();
    }
    if old > count {
      return;
    }

    // old == count, so new == 0, so we can deallocate the object
    // Memory barrier on the reference count
    rc.load(Ordering::Acquire);
    unsafe {
      drop(Box::from_raw(ptr.as_ptr() as *mut ArcObject<T>));
    }
  }

  // Decrements a reference count, with the assumption that the reference count remains positive
  #[inline(always)]
  fn rc_decrement_live(ptr: NonNull<ArcObject<T>>, count: usize) {
    let rc = unsafe { &(*ptr.as_ptr()).reference_count }.fetch_sub(count, Ordering::Release);
    if rc < count {
      error_negative_rc();
    }
    if rc > count {
      return;
    }

    // rc == count, so new == 0
    panic!("Reference count is zero while object is still live.");
  }
}

pub struct Arc<T> {
  pointer: NonNull<ArcObject<T>>
}

unsafe impl<T: Send + Sync> Send for Arc<T> {}
unsafe impl<T: Send + Sync> Sync for Arc<T> {}

impl<T> Arc<T> {
  pub fn new(value: T) -> Arc<T> {
    let inner = Box::new(ArcObject{
      reference_count: AtomicUsize::new(1),
      value
    });
    Arc{
      pointer: unsafe { NonNull::new_unchecked(Box::into_raw(inner)) }
    }
  }

  pub fn into_atomic(self) -> ArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT - 1);
    let ptr = self.pointer.as_ptr();
    mem::forget(self);
    ArcCell(ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack(ptr, MAX_WEIGHT))
    })
  }

  pub fn as_atomic(&self) -> ArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT);
    ArcCell(ArcCellInternal {
      phantom: PhantomData,
      value: AtomicUsize::new(pack(self.pointer.as_ptr(), MAX_WEIGHT))
    })
  }

  pub fn into_atomic_optional(self) -> OptionalArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT - 1);
    let ptr = self.pointer.as_ptr();
    mem::forget(self);
    OptionalArcCell(ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack(ptr, MAX_WEIGHT))
    })
  }

  pub fn as_atomic_optional(&self) -> OptionalArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT);
    OptionalArcCell(ArcCellInternal {
      phantom: PhantomData,
      value: AtomicUsize::new(pack(self.pointer.as_ptr(), MAX_WEIGHT))
    })
  }

  pub fn as_arc_ptr(&self) -> NonNull<ArcObject<T>> {
    unsafe {
      NonNull::new_unchecked(self.pointer.as_ptr() as *mut ArcObject<T>)
    }
  }

  pub fn as_ptr(&self) -> NonNull<T> {
    unsafe {
      NonNull::new_unchecked(&(*self.pointer.as_ptr()).value as *const T as *mut T)
    }
  }
}

impl<T> Clone for Arc<T> {
  fn clone(&self) -> Self {
    ArcObject::rc_increment(self.pointer, 1);
    Self { pointer: self.pointer.clone() }
  }
}

impl<T> Drop for Arc<T> {
  fn drop(&mut self) {
    ArcObject::rc_decrement(self.pointer, 1);
  }
}

impl<T> Deref for Arc<T> {
  type Target = T;

  fn deref(&self) -> &T {
    unsafe {
      &(*self.pointer.as_ptr()).value
    }
  }
}

// ArcCell contains a pointer and a weight. ArcCell will
// 'reserve' MAX_WEIGHT references in ArcObject. It will hand out those
// references, and decrement its weight each time.
// When the ArcCell is dropped, it subtracts its remaining weight from the
// reference count of the object.
// When the weight is less than MAX_THREADS, it will claim
// more references in ArcInner to increase its weight.
struct ArcCellInternal<const NULLABLE: bool, T> {
  phantom: PhantomData<*mut T>,
  value: AtomicUsize
}

impl<T> ArcCellInternal<true, T> {
  #[inline(always)]
  fn null() -> ArcCellInternal<true, T> {
    ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack::<T>(std::ptr::null(), 0))
    }
  }
}

impl<const NULLABLE: bool, T> ArcCellInternal<NULLABLE, T> {
  #[inline(always)]
  fn new(value: T) -> ArcCellInternal<NULLABLE, T> {
    let inner = Box::new(ArcObject{
      reference_count: AtomicUsize::new(MAX_WEIGHT),
      value
    });
    ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack(Box::into_raw(inner), MAX_WEIGHT))
    }
  }

  // Wait-free, O(P) with P the number of threads
  // O(1) if the weight remains larger than MAX_THREADS
  #[inline(always)]
  pub fn load(&self) -> Option<Arc<T>> {
    let result = self.value.fetch_sub(pack_weight(1), Ordering::Acquire);
    let (ptr, weight) = unpack::<T>(result);
    
    if NULLABLE && ptr.is_null() {
      None
    } else {
      let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
      if weight - 1 < MAX_THREADS {
        increase_weight(&self.value, ptr_nonnull, weight - 1);
      }
      Some(Arc{
        pointer: ptr_nonnull
      })
    }
  }

  // Returns the pointer stored in this ArcCell, without incrementing the reference count.
  // This thus doens't guarantee that the object it points to is still live
  // Wait-free, O(1)
  #[inline(always)]
  pub fn peek(&self) -> *const ArcObject<T> {
    unpack(self.value.load(Ordering::Acquire)).0
  }

  // Wait-free, O(1)
  #[inline(always)]
  pub fn store_consume(&self, arc: Option<Arc<T>>) {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, MAX_WEIGHT - 1);
        mem::forget(a);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.value.swap(pack(new, MAX_WEIGHT), Ordering::AcqRel);
    release::<NULLABLE, T>(old);
  }

  // Wait-free, O(1)
  #[inline(always)]
  pub fn store(&self, arc: Option<&Arc<T>>) {
    let new = 
      if let Some(a) = arc {
        let ptr = a.pointer;
        ArcObject::rc_increment(ptr, MAX_WEIGHT);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.value.swap(pack(new, MAX_WEIGHT), Ordering::AcqRel);
    release::<NULLABLE, T>(old);
  }

  // Wait-free, O(1)
  #[inline(always)]
  pub fn swap_consume(&self, arc: Option<Arc<T>>) -> Option<Arc<T>> {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, MAX_WEIGHT - 1);
        mem::forget(a);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.value.swap(pack(new, MAX_WEIGHT), Ordering::AcqRel);
    release_to_arc::<NULLABLE, T>(old)
  }

  // Wait-free, O(1)
  #[inline(always)]
  pub fn swap(&self, arc: Option<&Arc<T>>) -> Option<Arc<T>> {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, MAX_WEIGHT);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.value.swap(pack(new, MAX_WEIGHT), Ordering::AcqRel);
    release_to_arc::<NULLABLE, T>(old)
  }

  // Lock-free
  #[inline(always)]
  pub fn compare_and_set(&self, current: Option<&Arc<T>>, new_arc: Option<&Arc<T>>) -> bool {
    // Lock-free, not wait-free. If other threads change the reference count in the pointer,
    // this function needs to retry. There is no bound on how often this may happen.

    // Note that we don't return the old value if the compare-exchange fails,
    // as we can only do that by also incrementing the reference count.
    // We could just call .load() here. Then we have to take into account that the pointer could then
    // be current_ptr, if the compare-exchange and load were interleaved by an update of another thread,
    // so this will need to happen in a loop. Hence it may be better to let the caller of this function handle this.

    let current_ptr =
      if let Some(a) = current {
        a.as_arc_ptr().as_ptr()
      } else {
        std::ptr::null()
      };

    let new =
      if let Some(a) = new_arc {
        ArcObject::rc_increment(a.pointer, MAX_WEIGHT);
        a.pointer.as_ptr()
      } else {
        std::ptr::null()
      };

    let mut observed = self.value.load(Ordering::Acquire);
    loop {
      let observed_ptr: *const ArcObject<T> = unpack(observed).0;
      if observed_ptr != current_ptr {
        // Undo change to reference count of 'new'.
        if !NULLABLE || !new.is_null() {
          ArcObject::rc_decrement(unsafe { NonNull::new_unchecked(new as *mut ArcObject<T>) }, MAX_WEIGHT);
        }
        return false;
      }
      match self.value.compare_exchange_weak(observed, pack(new, MAX_WEIGHT), Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => {
          // Decrement reference count of old value.
          release::<NULLABLE, T>(observed);
          return true;
        }
        Err(value) => {
          observed = value; // Try again
        }
      }
    }
  }
}

impl<const NULLABLE: bool, T> Drop for ArcCellInternal<NULLABLE, T> {
  fn drop(&mut self) {
    release::<NULLABLE, T>(self.value.load(Ordering::Relaxed));
  }
}

pub struct ArcCell<T>(ArcCellInternal<false, T>);
pub struct OptionalArcCell<T>(ArcCellInternal<true, T>);

impl<T> ArcCell<T> {
  pub fn new(value: T) -> ArcCell<T> {
    ArcCell(ArcCellInternal::new(value))
  }
  pub fn load(&self) -> Arc<T> {
    unsafe {
      self.0.load().unwrap_unchecked()
    }
  }
  pub fn peek(&self) -> NonNull<ArcObject<T>> {
    unsafe {
      NonNull::new_unchecked(self.0.peek() as *mut ArcObject<T>)
    }
  }
  pub fn store_consume(&self, arc: Arc<T>) {
    self.0.store_consume(Some(arc));
  }
  pub fn store(&self, arc: &Arc<T>) {
    self.0.store(Some(arc));
  }
  pub fn swap_consume(&self, arc: Arc<T>) -> Arc<T> {
    unsafe {
      self.0.swap_consume(Some(arc)).unwrap_unchecked()
    }
  }
  pub fn swap(&self, arc: &Arc<T>) -> Arc<T> {
    unsafe {
      self.0.swap(Some(arc)).unwrap_unchecked()
    }
  }
  pub fn compare_and_set(&self, current: &Arc<T>, new: &Arc<T>) -> bool {
    self.0.compare_and_set(Some(current), Some(new))
  }

  pub fn update<F: FnMut(&Arc<T>) -> Result<(Arc<T>, A), B>, A, B>(&self, mut f: F) -> Result<A, B> {
    loop {
      let arc = self.load();
      let (new_arc, result) = f(&arc)?;
      // Since the object pointed to by arc remains live during the compare-exchange,
      // we prevent the ABA problem.
      if self.compare_and_set(&arc, &new_arc) {
        return Ok(result);
      }

      // self.value points to a different pointer.
      // Continue outer loop to invoke f again.
    }
  }
}

impl<T> OptionalArcCell<T> {
  pub fn new(value: T) -> OptionalArcCell<T> {
    OptionalArcCell(ArcCellInternal::new(value))
  }
  pub fn null() -> OptionalArcCell<T> {
    OptionalArcCell(ArcCellInternal::null())
  }
  pub fn load(&self) -> Option<Arc<T>> {
    self.0.load()
  }
  pub fn peek(&self) -> *const ArcObject<T> {
    self.0.peek()
  }
  pub fn store_consume(&self, arc: Option<Arc<T>>) {
    self.0.store_consume(arc);
  }
  pub fn store(&self, arc: Option<&Arc<T>>) {
    self.0.store(arc);
  }
  pub fn swap_consume(&self, arc: Option<Arc<T>>) -> Option<Arc<T>> {
    self.0.swap_consume(arc)
  }
  pub fn swap(&self, arc: Option<&Arc<T>>) -> Option<Arc<T>> {
    self.0.swap(arc)
  }
  pub fn compare_and_set(&self, current: Option<&Arc<T>>, new: Option<&Arc<T>>) -> bool {
    self.0.compare_and_set(current, new)
  }

  pub fn update<F: FnMut(Option<&Arc<T>>) -> Result<(Option<Arc<T>>, A), B>, A, B>(&self, mut f: F) -> Result<A, B> {
    loop {
      let arc = self.load();
      let (new_arc, result) = f(arc.as_ref())?;
      // Since the object pointed to by arc remains live during the compare-exchange,
      // we prevent the ABA problem.
      if self.compare_and_set(arc.as_ref(), new_arc.as_ref()) {
        return Ok(result);
      }

      // self.value points to a different pointer.
      // Continue outer loop to invoke f again.
    }
  }
}

#[inline(always)]
fn release<const NULLABLE: bool, T>(value: usize) {
  let (ptr, weight) = unpack::<T>(value);
  if NULLABLE && ptr.is_null() {
    return;
  }
  ArcObject::rc_decrement(unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) }, weight);
}

#[inline(always)]
fn release_to_arc<const NULLABLE: bool, T>(value: usize) -> Option<Arc<T>> {
  let (ptr, weight) = unpack::<T>(value);
  if NULLABLE && ptr.is_null() {
    return None;
  }
  let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
  ArcObject::rc_decrement_live(ptr_nonnull, weight - 1);
  Some(Arc{ pointer: ptr_nonnull })
}

#[inline(always)]
fn increase_weight<T>(value: &AtomicUsize, ptr: NonNull<ArcObject<T>>, weight: usize) {
  assert!(2 * MAX_THREADS <= MAX_WEIGHT);
  // Increase weight of the object by 'MAX_WEIGHT - weight'

  // Ordering::Acquire to prevent the compare-and-swap being reordered to before this instruction.
  // That would let other threads observe a lower reference count.
  ArcObject::rc_increment(ptr, MAX_WEIGHT - weight);

  // cas-loop to update the value
  let mut current_weight = weight;

  loop {
    let expected = pack(ptr.as_ptr(), current_weight);
    let new_value = pack(ptr.as_ptr(), current_weight + MAX_WEIGHT - weight);
    match value.compare_exchange(expected, new_value, Ordering::Relaxed, Ordering::Relaxed) {
      Ok(_) => {
        // Success!
        return;
      },
      Err(new_value) => {
        let (new_ptr, new_weight) = unpack::<T>(new_value);
        if new_ptr != ptr.as_ptr() {
          // The ArcCell now refers to a different pointer.
          // This makes this attempt to increase the weight redundant.
          break;
        }
        if new_weight > current_weight {
          // The weight was already increased by another thread.
          // No need for this thread to increment the weight.
          break;
        }
        if new_weight == current_weight {
          panic!("Spurious fails should be impossible with strong compare_exchange");
        }
        current_weight = new_weight;
      }
    }
  }

  // CAS didn't succeed, because either
  // 1. Another thread changed the pointer.
  // 2. Another thread increased the weight.
  // In both cases the weight is (or has been) above MAX_THREADS,
  // hence we don't need to decrement it.

  // Revert the change of the reference_count.
  ArcObject::rc_decrement_live(ptr, MAX_WEIGHT - weight);
}

#[inline(always)]
fn pack<T>(ptr: *const ArcObject<T>, weight: usize) -> usize {
  // Store weight in most-significant bits,
  // pointer in least-significant bits.
  assert!(weight <= MAX_WEIGHT);

  // Mask to clear unused most-significant bits
  let ptr_mask = (1 << (usize::BITS as usize - FREE_BITS_MOST_SIGNIFICANT)) - 1;

  // Mask pointer and shift to drop unused least-significant bits of the pointer
  ((ptr as usize & ptr_mask) >> FREE_BITS_LEAST_SIGNIFICANT)
    | (weight << (usize::BITS as usize - TAG_BITS))
}
#[inline(always)]
fn pack_weight(weight: usize) -> usize {
  weight << (usize::BITS as usize - TAG_BITS)
}
#[inline(always)]
fn unpack<T>(value: usize) -> (*const ArcObject<T>, usize) {
  let weight = value >> (usize::BITS as usize - TAG_BITS);

  // Shift pointer to the left to start at the most-significant bit of a word,
  // and then shift over the unused bits with sign-extension.
  // The latter is needed as the free most-significant bits should be the same
  // as the most-significant used bit.
  let pointer_value = ((value << TAG_BITS) as isize >> FREE_BITS_MOST_SIGNIFICANT) as usize;

  (pointer_value as *const ArcObject<T>, weight)
}

fn error_negative_rc() -> ! {
  panic!("Reference count is negative");
}

fn error_rc_overflow() -> ! {
  panic!("Reference count overflow");
}
