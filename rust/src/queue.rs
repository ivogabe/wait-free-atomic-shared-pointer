use std::mem::MaybeUninit;

// Michael-Scott queue implemented using the (Atomic)Arc primitives.
use crate::arc::*;

pub struct Queue<T> {
  head: ArcCell<Node<T>>,
  tail: ArcCell<Node<T>>
}
struct Node<T> {
  value: MaybeUninit<T>,
  next: OptionalArcCell<Node<T>>
}

impl<T> Queue<T> {
  pub fn new() -> Queue<T> {
    let node = Arc::new(Node{ value: MaybeUninit::<T>::uninit(), next: OptionalArcCell::null() });
    Queue {
      head: node.as_atomic(),
      tail: node.into_atomic()
    }
  }

  pub fn enqueue(&self, value: T) {
    let node = Arc::new(Node{
      value: MaybeUninit::new(value),
      next: OptionalArcCell::null()
    });
    // Keep trying until Enqueue is done
    loop {
      let tail = self.tail.load();
      let next = tail.next.load();
      // Are tail and next consistent?
      if tail.as_arc_ptr() == self.tail.peek() {
        match next {
          // Was tail pointing to the last node?
          None => {
            // Try to link node at the end of the linked list
            if tail.next.compare_and_set(None, Some(&node)) {
              // Enqueue is done.
              // Try to swing Tail to the inserted node
              self.tail.compare_and_set(&tail, &node);
              // Exit loop
              break;
            }
          },
          // Tail was not pointing to the last node
          Some(next_ptr) => {
            // Try to swing Tail to the next node
            self.tail.compare_and_set(&tail, &next_ptr);
          }
        }
      }
    }
  }

  pub fn dequeue(&self) -> Option<T> {
    loop {
      let head = self.head.load();
      let tail = self.tail.load();
      let next = head.next.load();
      if head.as_arc_ptr() == self.head.peek() {
        if head.as_arc_ptr() == tail.as_arc_ptr() {
          match next {
            None => return None,
            Some(n) => {
              self.tail.compare_and_set(&tail, &n);
            }
          }
        } else {
          match next {
            None => panic!("Corrupted queue"),
            Some(n) => {
              if self.head.compare_and_set(&head, &n) {
                return Some(unsafe { n.value.assume_init_read() });
              }
            }
          }
        }
      }
    }
  }
}

impl<T> Drop for Queue<T> {
  fn drop(&mut self) {
    while self.dequeue().is_some() {}
  }
}
