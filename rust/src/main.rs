pub mod arc;
pub mod queue;

use arc::*;

fn main() {
  println!("1");
  let a = AtomicOptionalArc::new(LogDrop{ value: 2903 });
  let b = Arc::new(LogDrop{ value: 12345678 });
  println!("2");
  for i in 0 .. (1<<19) + (1<<18) {
    drop(a.load());
    if (i & 0xFFFF) == 0 {
      println!("  {}", i);
    }
  }
  println!("3");
  println!("cas {}",
    a.compare_and_set(Some(&b), Some(&Arc::new(LogDrop { value: 20000 })))
  );
  a.store(Some(&Arc::new(LogDrop { value: 20001 })));
  a.store_consume(Some(Arc::new(LogDrop { value: 20002 })));
  println!("4");
  drop(a);
  println!("5");

  let queue = queue::Queue::<LogDrop>::new();
  println!("{:?}", queue.dequeue());
  queue.enqueue(LogDrop{ value: 10001 });
  queue.enqueue(LogDrop{ value: 10002 });
  queue.enqueue(LogDrop{ value: 10003 });
  queue.enqueue(LogDrop{ value: 10004 });
  println!("{:?}", queue.dequeue());
  println!("{:?}", queue.dequeue());
  println!("{:?}", queue.dequeue());

  println!("6");
  drop(queue);
  println!("7");
}

#[derive(Debug)]
struct LogDrop {
  value: u64
}

impl Drop for LogDrop {
  fn drop(&mut self) {
    println!("Drop {}", self.value);
  }
}
