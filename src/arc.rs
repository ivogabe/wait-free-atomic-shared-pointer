use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::mem;

const FREE_BITS_MOST_SIGNIFICANT: usize = 16;
const FREE_BITS_LEAST_SIGNIFICANT: usize = 3; // Alignment of the AtomicUsize (assuming a 64-bit architecture)
const TAG_BITS: usize = FREE_BITS_MOST_SIGNIFICANT + FREE_BITS_LEAST_SIGNIFICANT;

const MAX_REFCOUNT: usize = isize::MAX as usize;
const MAX_LOCAL_REFCOUNT: usize = (1 << TAG_BITS) - 1;

const MAX_THREADS: usize = 1 << 16;

// The reference count that an AtomicArc claims. This is one reference for the AtomicArc itself,
// and MAX_LOCAL_REFCOUNT for pre-claimed references.
const COMBINED_COUNT: usize = MAX_LOCAL_REFCOUNT + 1;

// When at least DANGER_ZONE references have been handed out in .load(),
// we have to claim new references before we can continue.
const DANGER_ZONE: usize = MAX_LOCAL_REFCOUNT - MAX_THREADS;

#[repr(C)]
pub struct ArcObject<T> {
  reference_count: AtomicUsize,
  pub value: T
}

impl<T> ArcObject<T> {
  fn rc_increment(ptr: NonNull<ArcObject<T>>, count: usize) {
    let rc = unsafe { &(*ptr.as_ptr()).reference_count };
    if count == 0 { return; }
    let old = rc.fetch_add(count, Ordering::Relaxed);
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
    let rc = unsafe { &(*ptr.as_ptr()).reference_count };
    if count == 0 { return; }
    let old = rc.fetch_sub(count, Ordering::Release);
    if old < count {
      error_negative_rc();
    }
    if old > count {
      return;
    }

    // old == count, so new == 0
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

  pub fn into_atomic(self) -> AtomicArc<T> {
    ArcObject::rc_increment(self.pointer, COMBINED_COUNT - 1);
    let ptr = self.pointer.as_ptr();
    mem::forget(self);
    AtomicArc(AtomicArcInternal{
      phantom: PhantomData,
      tagged_pointer: AtomicUsize::new(pack(ptr, 0))
    })
  }

  pub fn as_atomic(&self) -> AtomicArc<T> {
    ArcObject::rc_increment(self.pointer, COMBINED_COUNT);
    AtomicArc(AtomicArcInternal {
      phantom: PhantomData,
      tagged_pointer: AtomicUsize::new(pack(self.pointer.as_ptr(), 0))
    })
  }

  pub fn into_atomic_optional(self) -> AtomicOptionalArc<T> {
    ArcObject::rc_increment(self.pointer, COMBINED_COUNT - 1);
    let ptr = self.pointer.as_ptr();
    mem::forget(self);
    AtomicOptionalArc(AtomicArcInternal{
      phantom: PhantomData,
      tagged_pointer: AtomicUsize::new(pack(ptr, 0))
    })
  }

  pub fn as_atomic_optional(&self) -> AtomicOptionalArc<T> {
    ArcObject::rc_increment(self.pointer, COMBINED_COUNT);
    AtomicOptionalArc(AtomicArcInternal {
      phantom: PhantomData,
      tagged_pointer: AtomicUsize::new(pack(self.pointer.as_ptr(), 0))
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

// AtomicArc contains a pointer, and a reference count. AtomicArc will
// 'reserve' PRECLAIM_COUNT references in ArcInner. It will hand out those
// references, and keep track of the number of handed out references in the tag
// of the pointer.
// When the AtomicArc is dropped, it corrects the reference count of ArcInner.
// When the number in the tag is close to PRECLAIM_COUNT, it will claim
// more references in ArcInner to get sufficient space.
struct AtomicArcInternal<const NULLABLE: bool, T> {
  phantom: PhantomData<*mut T>,
  tagged_pointer: AtomicUsize
}

impl<T> AtomicArcInternal<true, T> {
  fn null() -> AtomicArcInternal<true, T> {
    AtomicArcInternal{
      phantom: PhantomData,
      tagged_pointer: AtomicUsize::new(pack::<T>(std::ptr::null(), 0))
    }
  }
}

impl<const NULLABLE: bool, T> AtomicArcInternal<NULLABLE, T> {
  fn new(value: T) -> AtomicArcInternal<NULLABLE, T> {
    let inner = Box::new(ArcObject{
      reference_count: AtomicUsize::new(COMBINED_COUNT),
      value
    });
    AtomicArcInternal{
      phantom: PhantomData,
      tagged_pointer: AtomicUsize::new(pack(Box::into_raw(inner), 0))
    }
  }

  // Wait-free, O(P) with P the number of threads
  // O(1) if the tag remains less than DANGER_ZONE
  pub fn load(&self) -> Option<Arc<T>> {
    let result = self.tagged_pointer.fetch_add(pack_tag(1), Ordering::Acquire);
    let (ptr, tag) = unpack::<T>(result);

    if NULLABLE && ptr.is_null() {
      None
    } else {
      let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
      if tag >= DANGER_ZONE {
        shift_references(&self.tagged_pointer, ptr_nonnull, tag + 1);
      }
      Some(Arc{
        pointer: ptr_nonnull
      })
    }
  }

  // Returns the pointer stored in this AtomicArc, without incrementing the reference count.
  // This thus doens't guarantee that the object it points to is still live
  // Wait-free, O(1)
  pub fn peek(&self) -> *const ArcObject<T> {
    unpack(self.tagged_pointer.load(Ordering::Acquire)).0
  }

  // Wait-free, O(1)
  pub fn store_consume(&self, arc: Option<Arc<T>>) {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, COMBINED_COUNT - 1);
        mem::forget(a);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.tagged_pointer.swap(pack(new, 0), Ordering::AcqRel);
    release::<NULLABLE, T>(old);
  }

  // Wait-free, O(1)
  pub fn store(&self, arc: Option<&Arc<T>>) {
    let new = 
      if let Some(a) = arc {
        let ptr = a.pointer;
        ArcObject::rc_increment(ptr, COMBINED_COUNT);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.tagged_pointer.swap(pack(new, 0), Ordering::AcqRel);
    release::<NULLABLE, T>(old);
  }

  // Wait-free, O(1)
  pub fn swap_consume(&self, arc: Option<Arc<T>>) -> Option<Arc<T>> {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, COMBINED_COUNT - 1);
        mem::forget(a);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.tagged_pointer.swap(pack(new, 0), Ordering::AcqRel);
    release_to_arc::<NULLABLE, T>(old)
  }

  // Wait-free, O(1)
  pub fn swap(&self, arc: Option<&Arc<T>>) -> Option<Arc<T>> {
    let new =
      if let Some(a) = arc {
        let ptr = a.pointer;
        // Subtract 1, as the arc already was present in the reference count
        ArcObject::rc_increment(ptr, COMBINED_COUNT);
        ptr.as_ptr()
      } else {
        std::ptr::null()
      };

    let old = self.tagged_pointer.swap(pack(new, 0), Ordering::AcqRel);
    release_to_arc::<NULLABLE, T>(old)
  }

  // Lock-free
  pub fn compare_exchange(&self, current: Option<&Arc<T>>, new_arc: Option<&Arc<T>>) -> bool {
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
        ArcObject::rc_increment(a.pointer, COMBINED_COUNT);
        a.pointer.as_ptr()
      } else {
        std::ptr::null()
      };

    let mut observed = self.tagged_pointer.load(Ordering::Relaxed);
    loop {
      let observed_ptr: *const ArcObject<T> = unpack(observed).0;
      if observed_ptr != current_ptr {
        // Undo change to reference count of 'new'.
        if !NULLABLE || !new.is_null() {
          ArcObject::rc_decrement(unsafe { NonNull::new_unchecked(new as *mut ArcObject<T>) }, COMBINED_COUNT);
        }
        return false;
      }
      match self.tagged_pointer.compare_exchange_weak(observed, pack(new, 0), Ordering::AcqRel, Ordering::Acquire) {
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

impl<const NULLABLE: bool, T> Drop for AtomicArcInternal<NULLABLE, T> {
  fn drop(&mut self) {
    release::<NULLABLE, T>(self.tagged_pointer.load(Ordering::Relaxed));
  }
}

pub struct AtomicArc<T>(AtomicArcInternal<false, T>);
pub struct AtomicOptionalArc<T>(AtomicArcInternal<true, T>);

impl<T> AtomicArc<T> {
  pub fn new(value: T) -> AtomicArc<T> {
    AtomicArc(AtomicArcInternal::new(value))
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
  pub fn compare_exchange(&self, current: &Arc<T>, new: &Arc<T>) -> bool {
    self.0.compare_exchange(Some(current), Some(new))
  }

  pub fn update<F: FnMut(&Arc<T>) -> Result<(Arc<T>, A), B>, A, B>(&self, mut f: F) -> Result<A, B> {
    loop {
      let arc = self.load();
      let (new_arc, result) = f(&arc)?;
      // Since the object pointed to by arc remains live during the compare-exchange,
      // we prevent the ABA problem.
      if self.compare_exchange(&arc, &new_arc) {
        return Ok(result);
      }

      // self.tagged_pointer points to a different pointer.
      // Continue outer loop to invoke f again.
    }
  }
}

impl<T> AtomicOptionalArc<T> {
  pub fn new(value: T) -> AtomicOptionalArc<T> {
    AtomicOptionalArc(AtomicArcInternal::new(value))
  }
  pub fn null() -> AtomicOptionalArc<T> {
    AtomicOptionalArc(AtomicArcInternal::null())
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
  pub fn compare_exchange(&self, current: Option<&Arc<T>>, new: Option<&Arc<T>>) -> bool {
    self.0.compare_exchange(current, new)
  }

  pub fn update<F: FnMut(Option<&Arc<T>>) -> Result<(Option<Arc<T>>, A), B>, A, B>(&self, mut f: F) -> Result<A, B> {
    loop {
      let arc = self.load();
      let (new_arc, result) = f(arc.as_ref())?;
      // Since the object pointed to by arc remains live during the compare-exchange,
      // we prevent the ABA problem.
      if self.compare_exchange(arc.as_ref(), new_arc.as_ref()) {
        return Ok(result);
      }

      // self.tagged_pointer points to a different pointer.
      // Continue outer loop to invoke f again.
    }
  }
}

#[inline(always)]
fn release<const NULLABLE: bool, T>(tagged_ptr: usize) {
  let (ptr, tag) = unpack::<T>(tagged_ptr);
  if NULLABLE && ptr.is_null() {
    return;
  }
  // We had reserved COMBINED_COUNT references for the old object.
  // 'tag' references were handed out, when reading from the AtomicArc.
  // Hence we remove COMBINED_COUNT - old_tag references to make
  // everything consistent again.
  ArcObject::rc_decrement(unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) }, COMBINED_COUNT - tag);
}

fn release_to_arc<const NULLABLE: bool, T>(tagged_ptr: usize) -> Option<Arc<T>> {
  let (ptr, tag) = unpack::<T>(tagged_ptr);
  if NULLABLE && ptr.is_null() {
    return None;
  }
  let ptr_nonnull = unsafe { NonNull::new_unchecked(ptr as *mut ArcObject<T>) };
  // We had reserved COMBINED_COUNT references for the old object.
  // 'tag' references were handed out, when reading from the AtomicArc.
  // We need 1 reference to return an Arc.
  // Hence we remove COMBINED_COUNT - old_tag - 1 references to make
  // everything consistent again.
  ArcObject::rc_decrement_live(ptr_nonnull, COMBINED_COUNT - tag - 1);
  Some(Arc{ pointer: ptr_nonnull })
}

#[inline(always)]
fn shift_references<T>(tagged_pointer: &AtomicUsize, ptr: NonNull<ArcObject<T>>, tag: usize) {
  println!("Shift references");
  // Move references from AtomicArc.
  // Move 'tag' references from the AtomicArc to the ArcInner.
  let inner = unsafe { &*ptr.as_ptr() };
  // Ordering::Acquire to prevent the compare-and-swap being reordered to before this instruction.
  // That would let other threads observe a lower reference count.
  inner.reference_count.fetch_add(tag, Ordering::Acquire);

  // cas-loop to update the tagged pointer.
  let mut current_tag = tag;

  loop {
    match tagged_pointer.compare_exchange(pack(ptr.as_ptr(), current_tag), pack(ptr.as_ptr(), current_tag - tag), Ordering::Relaxed, Ordering::Relaxed) {
      Ok(_) => {
        // Success!
        return;
      },
      Err(new_value) => {
        let (new_ptr, new_tag) = unpack::<T>(new_value);
        if new_ptr != ptr.as_ptr() {
          // The AtomicArc now refers to a different pointer.
          // This makes this attempt to move references redundant.
          break;
        } else if new_tag < current_tag {
          // The tag was already lowered by another thread.
          // No need for this thread to lower the tag.
          break;
        } else if new_tag == current_tag {
          panic!("Spurious fails should be impossible with strong compare_exchange");
        } else {
          current_tag = new_tag;
        }
      }
    }
  }

  // CAS didn't succeed, because either
  // 1. Another thread changed the pointer.
  // 2. Another thread lowered the tag.
  // In both cases the tag is (or has been) below DANGER_ZONE,
  // hence we don't need to decrement it.

  // Revert the change of the reference_count.
  let count = inner.reference_count.fetch_sub(tag, Ordering::Relaxed);

  // Note that this will not lower the reference count to 0,
  // as this thread still holds a reference to the object.
  assert_ne!(count - tag, 0);
}

fn pack<T>(ptr: *const ArcObject<T>, tag: usize) -> usize {
  // Store tag in most-significant bits,
  // pointer in least-significant bits.
  assert!(tag < MAX_LOCAL_REFCOUNT);
  // ((ptr as usize) << FREE_BITS_MOST_SIGNIFICANT) | tag

  // Mask to clear unused most-significant bits
  let ptr_mask = (1 << (usize::BITS as usize - FREE_BITS_MOST_SIGNIFICANT)) - 1;

  // Mask pointer and shift to drop unused least-significant bits of the pointer
  ((ptr as usize & ptr_mask) >> FREE_BITS_LEAST_SIGNIFICANT)
    | (tag << (usize::BITS as usize - TAG_BITS))
}
fn pack_tag(tag: usize) -> usize {
  tag << (usize::BITS as usize - TAG_BITS)
}
fn unpack<T>(value: usize) -> (*const ArcObject<T>, usize) {
  /* let tag_mask = MAX_LOCAL_REFCOUNT;
  // Shift with sign-extension
  let shifted = (value as isize) >> FREE_BITS_MOST_SIGNIFICANT;
  // Clear the least significant bits. These must be zero, for alignment
  let pointer_mask = !((1 << FREE_BITS_LEAST_SIGNIFICANT) - 1);
  let pointer = (shifted as usize) & pointer_mask;
  (pointer as *const ArcObject<T>, value & tag_mask) */

  let tag = value >> (usize::BITS as usize - TAG_BITS);
  
  // Shift pointer to the left to start at the most-significant bit of a word,
  // and then shift over the unused bits with sign-extension.
  // The latter is needed as the free most-significant bits should be the same
  // as the most-significant used bit.
  let pointer_value = ((value << TAG_BITS) as isize >> FREE_BITS_MOST_SIGNIFICANT) as usize;

  (pointer_value as *const ArcObject<T>, tag)
}

fn error_negative_rc() -> ! {
  panic!("Reference count is negative");
}

fn error_rc_overflow() -> ! {
  panic!("Reference count overflow");
}
