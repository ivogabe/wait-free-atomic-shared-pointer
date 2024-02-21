#include "atomic_shared_ptr.h"

struct LogDrop {
  public:
    int value;
    ~LogDrop() {
      printf("Drop %d\n", this->value);
    }
    void log() {
      printf("Hello %d\n", this->value);
    }
};


int main() {
  auto a = shared_ptr<LogDrop>(new LogDrop{ .value = 42 });
  atomic_shared_ptr<LogDrop> b(a);
  a = shared_ptr<LogDrop>();
  b.store(shared_ptr<LogDrop>(new LogDrop{ .value = 101 }));
  for (int i = 0; i < (1<<19) + (1<<18); i++) {
    b.load();
  }
  auto c = b.load();
  c->log();
  printf("compare_and_set %d\n",
    b.compare_and_set(c, shared_ptr<LogDrop>(new LogDrop{ .value = 102 })));
  printf("compare_and_set %d\n",
    b.compare_and_set(c, shared_ptr<LogDrop>(new LogDrop{ .value = 103 })));
  
  auto expected = shared_ptr<LogDrop>(new LogDrop{ .value = 104 });
  printf("compare_exchange %d\n",
    b.compare_exchange_strong(expected, shared_ptr<LogDrop>(new LogDrop{ .value = 105 })));
  printf("compare_exchange %d\n",
    b.compare_exchange_weak(expected, shared_ptr<LogDrop>(new LogDrop{ .value = 106 })));
  

  return 0;
}

