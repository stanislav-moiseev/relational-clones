/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "z3/gen.h"
#include "utils.h"
#include "pred.h"
#include "clone.h"

void gen_header(FILE *fd, int k) {
  fprintf(fd, "(declare-datatypes () ((E%d ", k);
  for(int i = 0; i < k; ++i) {
    fprintf(fd, "V%d ", i);
  }
  fprintf(fd, ")))\n");
}

void gen_pred(FILE *fd, int k, const token *tk, const pred *pred) {
  fprintf(fd, "(declare-fun %s (", tk->name);
  for(int i = 0; i < tk->arity; ++i) {
    fprintf(fd, "E%d ", k);
  }
  fprintf(fd, ") Bool)\n");


  int max = 1;
  for(int i = 0; i < tk->arity; ++i) {
    max *= k;
  }
  /* max == k^arity */

  for(int i = 0; i < max; ++i) {
    fprintf(fd, "(assert (= (%s", tk->name);
    /* represent `i` in the ternary form,
     * with digits[0] being the highest digit. */
    char digits[tk->arity];
    int ii = i;
    for(int j = tk->arity - 1; j >= 0; --j) {
      digits[j] = ii % 3;
      ii /= 3;
    }
    for(int j = 0; j < tk->arity; ++j) {
      fprintf(fd, " V%d", digits[j]);
    }
    if(pred->data & ((uint64_t)1 << i)) {
      fprintf(fd, ") true)");
    } else {
      fprintf(fd, ") false)");
    }
    fprintf(fd, ")\n");
  }
}

void gen_fun(FILE *fd, int k, const token *f) {
  fprintf(fd, "(declare-fun %s (", f->name);
  for(int i = 0; i < f->arity; ++i) {
    fprintf(fd, "E%d ", k);
  }
  fprintf(fd, ") E%d)\n", k);
}


void gen_preserve(FILE *fd, int if_not, int k, const token *pred, const token *fun) {
  if(if_not) {
    fprintf(fd, "(assert (not (forall (");
  } else {
    fprintf(fd, "(assert (forall (");
  }
  
  for(int i = 0; i < fun->arity; ++i) {
    for(int j = 0; j < pred->arity; ++j) {
      fprintf(fd, "(x%d_%d E%d) ", i, j, k);
    }
  }
  fprintf(fd, ")\n");
  fprintf(fd, "\t\t(implies (and ");
  for(int i = 0; i < fun->arity; ++i) {
    fprintf(fd, "(%s", pred->name);
    for(int j = 0; j < pred->arity; ++j) {
      fprintf(fd, " x%d_%d", i, j);  
    }
    fprintf(fd, ")");
  }
  fprintf(fd, ")");
  fprintf(fd, " (%s", pred->name);
  for(int j = 0; j < pred->arity; ++j) {
    fprintf(fd, " (%s", fun->name);
    for(int i = 0; i < fun->arity; ++i) {
      fprintf(fd, " x%d_%d", i, j);  
    }
    fprintf(fd, ")");
  }

  if(if_not) {
    fprintf(fd, ")))))\n");
  } else {
    fprintf(fd, "))))\n");
  }
}

void gen_assert_discr_fun(FILE *fd, const clone *clone, const pred *pred, int fun_arity) {
  gen_header(fd, K);
  
  int num_preds = clone_cardinality(clone);
  struct pred pred_list[num_preds];
  token tokens[num_preds];
  uint64_t card;
  assert(clone_get_predicates(clone, pred_list, num_preds, &card));
  
  for(int i = 0; i < card; ++i) {
    tokens[i].name = malloc(16);
    sprintf(tokens[i].name, "p%d", i);
    tokens[i].arity = pred_list[i].arity;
    gen_pred(fd, K, &tokens[i], &pred_list[i]);
  }

  struct token fun =
    { .arity = fun_arity,
      .name  = "f"
    };
  gen_fun(fd, K, &fun);

  for(int i = 0; i < card; ++i) {
    gen_preserve(fd, 0, K, &tokens[i], &fun);
  }

  
  struct token tk =
    { .arity = pred->arity,
      .name = "p"
    };
  
  gen_pred(fd, K, &tk, pred);
  gen_preserve(fd, 1, K, &tk, &fun);

  fprintf(fd, "\n(check-sat)\n");
  /* fprintf(fd, "(get-model)\n"); */
}

