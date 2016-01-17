#include "pred.h"

int main() {
  for(uint64_t data = 0; data < 100; ++data) {
    pred p = { .k = 3,
               .arity = 3,
               .data = data
    };
    pred_print(stdout, &p);
    printf("\n");
  }
  return 0;
}
