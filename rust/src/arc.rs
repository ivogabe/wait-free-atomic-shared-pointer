use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::mem;

// Use 16 most-significant bits for weight
const WEIGHT_BITS: usize = 16;

// Use 3 least-significant bits for tag
const TAG_BITS: usize = 3;

// Constant 'P'
const MAX_THREADS: usize = 1 << (WEIGHT_BITS - 1) - 1;

// Constant 'C'
const MAX_WEIGHT: usize = (1 << WEIGHT_BITS) - 1;

const MAX_REFCOUNT: usize = isize::MAX as usize;

const TAG_MASK: usize = (1 << TAG_BITS) - 1;

#[repr(C)]
pub struct ArcObject<T> {
  reference_count: AtomicUsize,
  pub value: T
}

impl<T> ArcObject<T> {
  fn rc_increment(ptr: NonNull<ArcObject<T>>, count: usize) {
    let rc = unsafe { &(*ptr.as_ptr()).reference_count };
    if count == 0 { return; }
    let old = rc.fetch_add(count, Ordering::Acquire);
    if old + count > MAX_REFCOUNT {
      error_rc_overflow();
    }
  }

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
    self.into_atomic_with_tag(0)
  }
  pub fn into_atomic_with_tag(self, tag: usize) -> ArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT - 1);
    let ptr = self.pointer.as_ptr();
    mem::forget(self);
    ArcCell(ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack(ptr, MAX_WEIGHT, tag))
    })
  }

  pub fn as_atomic(&self) -> ArcCell<T> {
    self.as_atomic_with_tag(0)
  }
  pub fn as_atomic_with_tag(&self, tag: usize) -> ArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT);
    ArcCell(ArcCellInternal {
      phantom: PhantomData,
      value: AtomicUsize::new(pack(self.pointer.as_ptr(), MAX_WEIGHT, tag))
    })
  }

  pub fn into_atomic_optional(self) -> OptionalArcCell<T> {
    self.into_atomic_optional_with_tag(0)
  }
  pub fn into_atomic_optional_with_tag(self, tag: usize) -> OptionalArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT - 1);
    let ptr = self.pointer.as_ptr();
    mem::forget(self);
    OptionalArcCell(ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack(ptr, MAX_WEIGHT, tag))
    })
  }

  pub fn as_atomic_optional(&self) -> OptionalArcCell<T> {
    self.as_atomic_optional_with_tag(0)
  }
  pub fn as_atomic_optional_with_tag(&self, tag: usize) -> OptionalArcCell<T> {
    ArcObject::rc_increment(self.pointer, MAX_WEIGHT);
    OptionalArcCell(ArcCellInternal {
      phantom: PhantomData,
      value: AtomicUsize::new(pack(self.pointer.as_ptr(), MAX_WEIGHT, tag))
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
  fn null(tag: usize) -> ArcCellInternal<true, T> {
    ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack::<T>(std::ptr::null(), 0, tag))
    }
  }
}

impl<const NULLABLE: bool, T> ArcCellInternal<NULLABLE, T> {
  fn new(value: T, tag: usize) -> ArcCellInternal<NULLABLE, T> {
    let inner = Box::new(ArcObject{
      reference_count: AtomicUsize::new(MAX_WEIGHT),
      value
    });
    ArcCellInternal{
      phantom: PhantomData,
      value: AtomicUsize::new(pack(Box::into_raw(inner), MAX_WEIGHT, tag))
    }
  }

  // Wait-free, O(P) with P the number of threads,
  // O(1) if the weight remains higher than MAX_WEIGHT.
  pub fn load(&self) -> (Option<Arc<T>>, usize) {
    let result = self.value.fetch_sub(pack_weight(1), Ordering::Acquire);
    let (ptr, weight, tag) = unpack::<T>(result);

    if NULLABLE && ptr.is_null() {
      (None, tag)
    } else {
      let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
      if weight - 1 < MAX_THREADS {
        increase_weight(&self.value, ptr_nonnull, weight - 1, tag);
      }
      (
        Some(Arc{
          pointer: ptr_nonnull
        }),
        tag
      )
    }
  }

  pub fn fetch_and_update_tag<A, B, F: FnMut(usize) -> Result<(usize, A), B>>(&self, mut f: F) -> Result<(Option<Arc<T>>, A), B> {
    // Similar to load(), but the fetch-and-add is now replaced by a compare-and-swap loop.
    let mut observed = self.value.load(Ordering::Relaxed);
    loop {
      let (ptr, weight, observed_tag) = unpack::<T>(observed);
      let (new_tag, result) = f(observed_tag)?;
      let new = pack::<T>(ptr, weight - 1, new_tag);
      match self.value.compare_exchange_weak(observed, new, Ordering::Acquire, Ordering::Relaxed) {
        Ok(_) => {
          if NULLABLE && ptr.is_null() {
            return Ok((None, result));
          } else {
            let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
            if weight - 1 < MAX_THREADS {
              increase_weight(&self.value, ptr_nonnull, weight - 1, new_tag);
            }
            return Ok((
              Some(Arc{
                pointer: ptr_nonnull
              }),
              result
            ));
          }
        },
        Err(value) => {
          observed = value; // Try again
        }
      }
    }
  }

  // Returns the pointer stored in this ArcCell, without incrementing the reference count.
  // This thus doens't guarantee that the object it points to is still live
  // Wait-free, O(1)
  pub fn peek(&self) -> (*const ArcObject<T>, usize) {
    let (ptr, _, tag) = unpack(self.value.load(Ordering::Acquire));
    (ptr, tag)
  }

  // Wait-free, O(1)
  pub fn store_consume(&self, arc: Option<Arc<T>>, tag: usize) {
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

    let old = self.value.swap(pack(new, MAX_WEIGHT, tag), Ordering::AcqRel);
    release::<NULLABLE, T>(old);
  }

  // Wait-free, O(1)
  pub fn store(&self, arc: Option<&Arc<T>>, tag: usize) {
    let new = 
      if let Some(a) = arc {
        let ptr = a.pointer;
        ArcObject::rc_increment(ptr, MAX_WEIGHT);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.value.swap(pack(new, MAX_WEIGHT, tag), Ordering::AcqRel);
    release::<NULLABLE, T>(old);
  }

  // Wait-free, O(1)
  pub fn swap_consume(&self, arc: Option<Arc<T>>, tag: usize) -> (Option<Arc<T>>, usize) {
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

    let old = self.value.swap(pack(new, MAX_WEIGHT, tag), Ordering::AcqRel);
    (release_to_arc::<NULLABLE, T>(old), unpack::<T>(tag).2)
  }

  // Wait-free, O(1)
  pub fn swap(&self, arc: Option<&Arc<T>>, tag: usize) -> (Option<Arc<T>>, usize) {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, MAX_WEIGHT);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.value.swap(pack(new, MAX_WEIGHT, tag), Ordering::AcqRel);
    (release_to_arc::<NULLABLE, T>(old), unpack::<T>(tag).2)
  }

  // Lock-free
  pub fn compare_and_set<const CHECK_TAG: bool>(&self, current: Option<&Arc<T>>, current_tag: usize, new_arc: Option<&Arc<T>>, new_tag: usize) -> bool {
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
      let (observed_ptr, _, observed_tag) = unpack(observed);
      if observed_ptr != current_ptr || (CHECK_TAG && observed_tag != current_tag) {
        // Undo change to reference count of 'new'.
        if !NULLABLE || !new.is_null() {
          ArcObject::rc_decrement(unsafe { NonNull::new_unchecked(new as *mut ArcObject<T>) }, MAX_WEIGHT);
        }
        return false;
      }
      match self.value.compare_exchange_weak(observed, pack(new, MAX_WEIGHT, new_tag), Ordering::AcqRel, Ordering::Acquire) {
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

  pub fn compare_and_swap_tag<const CHECK_TAG: bool>(&self, current: Option<&Arc<T>>, current_tag: usize, new_tag: usize) -> CompareAndSwapTag {
    let mut did_increase_weight = false; 

    let current_ptr =
      if let Some(a) = current {
        a.as_arc_ptr().as_ptr()
      } else {
        std::ptr::null()
      };
    let mut observed = self.value.load(Ordering::Acquire);
    loop {
      let (observed_ptr, observed_weight, observed_tag) = unpack(observed);
      if observed_ptr != current_ptr || (CHECK_TAG && observed_tag != current_tag) {
        if did_increase_weight && (!NULLABLE || !current_ptr.is_null()) {
          ArcObject::rc_decrement_live(unsafe { NonNull::new_unchecked(current_ptr as *mut ArcObject<T>) }, MAX_WEIGHT - MAX_THREADS);
        }
        if observed_ptr != current_ptr {
          return CompareAndSwapTag::DifferentPointer(observed_tag);
        } else {
          return CompareAndSwapTag::DifferentTag(observed_tag);
        }
      }
      if observed_weight < MAX_THREADS && !did_increase_weight {
        // Although not needed for correctness, we will increase the weight of
        // this cell here. This will make load() wait-free:
        // Updates to the weight will cause increase_weight(), helper function
        // for load(), to retry in its CAS loop. By increasing the weight here,
        // we allow increase_weight to exit.
        ArcObject::rc_increment(unsafe { NonNull::new_unchecked(current_ptr as *mut ArcObject<T>) }, MAX_WEIGHT - MAX_THREADS);
        did_increase_weight = true;
      }
      let new = pack(
        current_ptr,
        if observed_weight < MAX_THREADS { observed_weight + MAX_WEIGHT - MAX_THREADS } else { observed_weight },
        new_tag
      );
      match self.value.compare_exchange_weak(observed, new, Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => {
          return CompareAndSwapTag::Ok;
        },
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CompareAndSwapTag {
  Ok,
  // We can only return the tag, as we would need to change the weight to
  // acquire an Arc to the observed object.
  DifferentPointer(usize),
  DifferentTag(usize)
}

pub struct ArcCell<T>(ArcCellInternal<false, T>);
pub struct OptionalArcCell<T>(ArcCellInternal<true, T>);

impl<T> ArcCell<T> {
  pub fn new(value: T) -> ArcCell<T> {
    ArcCell(ArcCellInternal::new(value, 0))
  }
  pub fn new_with_tag(value: T, tag: usize) -> ArcCell<T> {
    ArcCell(ArcCellInternal::new(value, tag))
  }
  pub fn load(&self) -> Arc<T> {
    unsafe {
      self.0.load().0.unwrap_unchecked()
    }
  }
  pub fn load_with_tag(&self) -> (Arc<T>, usize) {
    let (arc, tag) = self.0.load();
    unsafe { (arc.unwrap_unchecked(), tag) }
  }
  pub fn fetch_and_update_tag<A, B, F: FnMut(usize) -> Result<(usize, A), B>>(&self, f: F) -> Result<(Arc<T>, A), B> {
    match self.0.fetch_and_update_tag(f) {
      Ok((arc, result)) => unsafe { 
        Ok((arc.unwrap_unchecked(), result))
      },
      Err(err) => Err(err)
    }
  }
  pub fn peek(&self) -> NonNull<ArcObject<T>> {
    unsafe {
      NonNull::new_unchecked(self.0.peek().0 as *mut ArcObject<T>)
    }
  }
  pub fn peek_with_tag(&self) -> (NonNull<ArcObject<T>>, usize) {
    let (ptr, tag) = self.0.peek();
    unsafe {
      (NonNull::new_unchecked(ptr as *mut ArcObject<T>), tag)
    }
  }
  pub fn store_consume(&self, arc: Arc<T>) {
    self.0.store_consume(Some(arc), 0);
  }
  pub fn store_consume_with_tag(&self, arc: Arc<T>, tag: usize) {
    self.0.store_consume(Some(arc), tag);
  }
  pub fn store(&self, arc: &Arc<T>) {
    self.0.store(Some(arc), 0);
  }
  pub fn store_with_tag(&self, arc: &Arc<T>, tag: usize) {
    self.0.store(Some(arc), tag);
  }
  pub fn swap_consume(&self, arc: Arc<T>) -> Arc<T> {
    unsafe {
      self.0.swap_consume(Some(arc), 0).0.unwrap_unchecked()
    }
  }
  pub fn swap_consume_with_tag(&self, arc: Arc<T>, tag: usize) -> (Arc<T>, usize) {
    let (ptr, tag) = self.0.swap_consume(Some(arc), tag);
    unsafe {
      (ptr.unwrap_unchecked(), tag)
    }
  }
  pub fn swap(&self, arc: &Arc<T>) -> Arc<T> {
    unsafe {
      self.0.swap(Some(arc), 0).0.unwrap_unchecked()
    }
  }
  pub fn swap_with_tag(&self, arc: &Arc<T>, tag: usize) -> (Arc<T>, usize) {
    let (ptr, tag) = self.0.swap(Some(arc), tag);
    unsafe {
      (ptr.unwrap_unchecked(), tag)
    }
  }
  pub fn compare_and_set(&self, current: &Arc<T>, new: &Arc<T>) -> bool {
    self.0.compare_and_set::<false>(Some(current), 0, Some(new), 0)
  }
  pub fn compare_and_set_with_tag(&self, current: &Arc<T>, current_tag: usize, new: &Arc<T>, new_tag: usize) -> bool {
    self.0.compare_and_set::<true>(Some(current), current_tag, Some(new), new_tag)
  }
  pub fn compare_and_swap_tag(&self, current: &Arc<T>, current_tag: usize, new_tag: usize) -> CompareAndSwapTag {
    self.0.compare_and_swap_tag::<true>(Some(current), current_tag, new_tag)
  }
  // Sets the tag to the specified tag, if this cell refers to the given object.
  pub fn set_tag(&self, current: &Arc<T>, new_tag: usize) -> bool {
    match self.0.compare_and_swap_tag::<false>(Some(current), 0, new_tag) {
      CompareAndSwapTag::Ok => true,
      _ => false
    }
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
  pub fn update_with_tag<F: FnMut(&Arc<T>, usize) -> Result<(Arc<T>, usize, A), B>, A, B>(&self, mut f: F) -> Result<A, B> {
    loop {
      let (arc, tag) = self.load_with_tag();
      let (new_arc, new_tag, result) = f(&arc, tag)?;
      // Since the object pointed to by arc remains live during the compare-exchange,
      // we prevent the ABA problem.
      if self.compare_and_set_with_tag(&arc, tag, &new_arc, new_tag) {
        return Ok(result);
      }

      // self.value points to a different pointer.
      // Continue outer loop to invoke f again.
    }
  }
}

impl<T> OptionalArcCell<T> {
  pub fn new(value: T) -> OptionalArcCell<T> {
    OptionalArcCell(ArcCellInternal::new(value, 0))
  }
  pub fn new_with_tag(value: T, tag: usize) -> OptionalArcCell<T> {
    OptionalArcCell(ArcCellInternal::new(value, tag))
  }
  pub fn null() -> OptionalArcCell<T> {
    OptionalArcCell(ArcCellInternal::null(0))
  }
  pub fn null_with_tag(tag: usize) -> OptionalArcCell<T> {
    OptionalArcCell(ArcCellInternal::null(tag))
  }
  pub fn load(&self) -> Option<Arc<T>> {
    self.0.load().0
  }
  pub fn load_with_tag(&self) -> (Option<Arc<T>>, usize) {
    self.0.load()
  }
  pub fn fetch_and_update_tag<A, B, F: FnMut(usize) -> Result<(usize, A), B>>(&self, f: F) -> Result<(Option<Arc<T>>, A), B> {
    self.0.fetch_and_update_tag(f)
  }
  pub fn peek(&self) -> *const ArcObject<T> {
    self.0.peek().0
  }
  pub fn peek_with_tag(&self) -> (*const ArcObject<T>, usize) {
    self.0.peek()
  }
  pub fn store_consume(&self, arc: Option<Arc<T>>) {
    self.0.store_consume(arc, 0);
  }
  pub fn store_consume_with_tag(&self, arc: Option<Arc<T>>, tag: usize) {
    self.0.store_consume(arc, tag);
  }
  pub fn store(&self, arc: Option<&Arc<T>>) {
    self.0.store(arc, 0);
  }
  pub fn store_with_tag(&self, arc: Option<&Arc<T>>, tag: usize) {
    self.0.store(arc, tag);
  }
  pub fn swap_consume(&self, arc: Option<Arc<T>>) -> Option<Arc<T>> {
    self.0.swap_consume(arc, 0).0
  }
  pub fn swap_consume_with_tag(&self, arc: Option<Arc<T>>, tag: usize) -> (Option<Arc<T>>, usize) {
    self.0.swap_consume(arc, tag)
  }
  pub fn swap(&self, arc: Option<&Arc<T>>) -> Option<Arc<T>> {
    self.0.swap(arc, 0).0
  }
  pub fn swap_with_tag(&self, arc: Option<&Arc<T>>, tag: usize) -> (Option<Arc<T>>, usize) {
    self.0.swap(arc, tag)
  }
  pub fn compare_and_set(&self, current: Option<&Arc<T>>, new: Option<&Arc<T>>) -> bool {
    self.0.compare_and_set::<false>(current, 0, new, 0)
  }
  pub fn compare_and_set_with_tag(&self, current: Option<&Arc<T>>, current_tag: usize, new: Option<&Arc<T>>, new_tag: usize) -> bool {
    self.0.compare_and_set::<true>(current, current_tag, new, new_tag)
  }
  pub fn compare_and_swap_tag(&self, current: Option<&Arc<T>>, current_tag: usize, new_tag: usize) -> CompareAndSwapTag {
    self.0.compare_and_swap_tag::<true>(current, current_tag, new_tag)
  }
  // Sets the tag to the specified tag, if this cell refers to the given object.
  pub fn set_tag(&self, current: Option<&Arc<T>>, new_tag: usize) -> bool {
    match self.0.compare_and_swap_tag::<false>(current, 0, new_tag) {
      CompareAndSwapTag::Ok => true,
      _ => false
    }
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
  pub fn update_with_tag<F: FnMut(Option<&Arc<T>>, usize) -> Result<(Option<Arc<T>>, usize, A), B>, A, B>(&self, mut f: F) -> Result<A, B> {
    loop {
      let (arc, tag) = self.load_with_tag();
      let (new_arc, new_tag, result) = f(arc.as_ref(), tag)?;
      // Since the object pointed to by arc remains live during the compare-exchange,
      // we prevent the ABA problem.
      if self.compare_and_set_with_tag(arc.as_ref(), tag, new_arc.as_ref(), new_tag) {
        return Ok(result);
      }

      // self.value points to a different pointer.
      // Continue outer loop to invoke f again.
    }
  }
}

#[inline(always)]
fn release<const NULLABLE: bool, T>(value: usize) {
  let (ptr, weight, _) = unpack::<T>(value);
  if NULLABLE && ptr.is_null() {
    return;
  }
  ArcObject::rc_decrement(unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) }, weight);
}

#[inline(always)]
fn release_to_arc<const NULLABLE: bool, T>(value: usize) -> Option<Arc<T>> {
  let (ptr, weight, _) = unpack::<T>(value);
  if NULLABLE && ptr.is_null() {
    return None;
  }
  let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
  ArcObject::rc_decrement_live(ptr_nonnull, weight - 1);
  Some(Arc{ pointer: ptr_nonnull })
}

#[inline(always)]
fn increase_weight<T>(value: &AtomicUsize, ptr: NonNull<ArcObject<T>>, weight: usize, tag: usize) {
  assert!(2 * MAX_THREADS <= MAX_WEIGHT);
  // Increase weight of the object by 'MAX_WEIGHT - weight'

  // Ordering::Acquire to prevent the compare-and-swap being reordered to before this instruction.
  // That would let other threads observe a lower reference count.
  ArcObject::rc_increment(ptr, MAX_WEIGHT - weight);

  // cas-loop to update the value
  let mut current_tag = tag;
  let mut current_weight = weight;

  loop {
    let expected = pack(ptr.as_ptr(), current_weight, current_tag);
    let new_value = pack(ptr.as_ptr(), current_weight + MAX_WEIGHT - weight, current_tag);
    match value.compare_exchange(expected, new_value, Ordering::Relaxed, Ordering::Relaxed) {
      Ok(_) => {
        // Success!
        return;
      },
      Err(new_value) => {
        let (new_ptr, new_weight, new_tag) = unpack::<T>(new_value);
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
        if current_tag == new_tag && new_weight == current_weight {
          panic!("Spurious fails should be impossible with strong compare_exchange");
        }
        current_tag = new_tag;
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

fn pack<T>(ptr: *const ArcObject<T>, weight: usize, tag: usize) -> usize {
  // Store weight in most-significant bits,
  // tag in least-significant bits,
  // and the pointer in its usual bits.
  assert!(weight <= MAX_WEIGHT);
  assert_eq!(tag & !TAG_MASK, 0);

  // Mask to clear unused most-significant bits
  let ptr_mask = (1 << (usize::BITS as usize - WEIGHT_BITS)) - 1;

  // Mask pointer
  (ptr as usize & ptr_mask)
    | (weight << (usize::BITS as usize - WEIGHT_BITS))
    | tag
}
fn pack_weight(weight: usize) -> usize {
  weight << (usize::BITS as usize - WEIGHT_BITS)
}
fn unpack<T>(value: usize) -> (*const ArcObject<T>, usize, usize) {
  let weight = value >> (usize::BITS as usize - WEIGHT_BITS);

  // Shift pointer to the left to start at the most-significant bit of a word,
  // and then shift over the unused bits with sign-extension.
  // The latter is needed as the free most-significant bits should be the same
  // as the most-significant used bit.
  let pointer_value = ((value << WEIGHT_BITS) as isize >> WEIGHT_BITS) as usize;

  ((pointer_value & !TAG_MASK) as *const ArcObject<T>, weight, pointer_value & TAG_MASK)
}

fn error_negative_rc() -> ! {
  panic!("Reference count is negative");
}

fn error_rc_overflow() -> ! {
  panic!("Reference count overflow");
}
