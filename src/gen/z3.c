/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "gen/z3.h"
#include "utils.h"
#include "pred.h"
#include "clone.h"
#include "clone-iterator.h"

void gen_header(FILE *fd, int k) {
  fprintf(fd, "(declare-datatypes () ((E%d ", k);
  for(int i = 0; i < k; ++i) {
    fprintf(fd, "V%d ", i);
  }
  fprintf(fd, ")))\n\n");
}

void gen_pred1(FILE *fd, int k, const token *tk, const pred *pred) {
  fprintf(fd, "(declare-fun %s (", tk->name);
  for(int i = 0; i < tk->arity; ++i) {
    fprintf(fd, " E%d", k);
  }
  fprintf(fd, ") Bool)\n");

  int max = int_pow(k, pred->arity);
  
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
  fprintf(fd, "\n");
}


void gen_pred(FILE *fd, int k, const token *tk, const pred *pred) {
  gen_pred1(fd, k, tk, pred);
}

void gen_fun(FILE *fd, int k, const token *f) {
  fprintf(fd, "(declare-fun %s (", f->name);
  for(int i = 0; i < f->arity; ++i) {
    fprintf(fd, "E%d ", k);
  }
  fprintf(fd, ") E%d)\n\n", k);
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
    fprintf(fd, ")))))\n\n");
  } else {
    fprintf(fd, "))))\n\n");
  }
}

void gen_assert_discr_fun(FILE *fd, const class *class, const pred *pred, int fun_arity) {
  gen_header(fd, K);

  /* the basis of the clone */
  struct pred *pred_list;
  uint64_t num_preds;
  clone_get_predicates(&class->basis, &pred_list, &num_preds);

  /* write a definition for all predicates */
  token tokens[num_preds];
  for(int i = 0; i < num_preds; ++i) {
    tokens[i].arity = pred_list[i].arity;
    assert(asprintf(&tokens[i].name, "p%d", i) >= 0);
    gen_pred(fd, K, &tokens[i], &pred_list[i]);
  }
  struct token tk =
    { .arity = pred->arity,
      .name = "p"
    };
  
  gen_pred(fd, K, &tk, pred);

  /* declare a discriminating function */
  struct token fun =
    { .arity = fun_arity,
      .name  = "f"
    };
  gen_fun(fd, K, &fun);

  /* write assertions about function preservation */
  for(int i = 0; i < num_preds; ++i) {
    gen_preserve(fd, 0, K, &tokens[i], &fun);
  }
  gen_preserve(fd, 1, K, &tk, &fun);


  /* write final commands */
  fprintf(fd, "\n(check-sat)\n");
  fprintf(fd, "(get-model)\n");
  
  free(pred_list);
  for(int i = 0; i < num_preds; ++i) {
    free(tokens[i].name);
  }
}

void gen_assert_discr_fun_two_classes(FILE *fd, const class *class1, const class *class2, int fun_arity) {
  /* select any predicate discriminating two clones */
  clone diff;
  clone_diff(&class2->clone, &class1->clone, &diff);

  clone_iterator it = clone_iterator_begin(&diff);
  assert(!clone_iterator_end(&diff, &it));
  
  pred pred = clone_iterator_deref(&it);

  
  gen_assert_discr_fun(fd, class1, &pred, fun_arity);
}

