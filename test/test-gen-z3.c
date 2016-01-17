#include <stdio.h>
#include <stdlib.h>

#include "z3/gen.h"

int main() {
  FILE *fd = stdout;
  int k = 3;
  
  gen_header(fd, k);
  struct token preds[] =
    { { .arity = 2,
        .name  = "p1",
      },
      { .arity = 2,
        .name  = "p2",
      },
      { .arity = 2,
        .name  = "p",
      },
    };
  int num_preds = 3;
  
  for(int i = 0; i < num_preds; ++i) {
    gen_pred(fd, k, &preds[i]);
  }

  struct token fun =
    { .arity = 15,
      .name  = "f"
    };
  gen_fun(fd, k, &fun);
  
  gen_preserve(fd, 0, k, &preds[0], &fun);
  gen_preserve(fd, 0, k, &preds[1], &fun);
  gen_preserve(fd, 1, k, &preds[2], &fun);

  fprintf(fd, "\n(check-sat)\n)");
  fprintf(fd, "(get-model)\n");
}

