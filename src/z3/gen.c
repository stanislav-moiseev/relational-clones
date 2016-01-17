/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <stdio.h>
#include <stdlib.h>

#include "z3/gen.h"

void gen_header(FILE *fd, int k) {
  fprintf(fd, "(declare-datatypes () ((E%d ", k);
  for(int i = 0; i < k; ++i) {
    fprintf(fd, "V%d ", i);
  }
  fprintf(fd, ")))\n");
}

void gen_pred(FILE *fd, int k, const token *pred) {
  fprintf(fd, "(declare-fun %s (", pred->name);
  for(int i = 0; i < pred->arity; ++i) {
    fprintf(fd, "E%d ", k);
  }
  fprintf(fd, ") Bool)\n");


  int max = 1;
  for(int i = 0; i < pred->arity; ++i) {
    max *= k;
  }
  /* max == k^arity */

  for(int i = 0; i < max; ++i) {
    fprintf(fd, "(assert (= (%s", pred->name);
    /* represent `i` in the ternary form,
     * with digits[0] being the highest digit. */
    char digits[pred->arity];
    int ii = i;
    for(int j = pred->arity - 1; j >= 0; --j) {
      digits[j] = ii % 3;
      ii /= 3;
    }
    for(int j = 0; j < pred->arity; ++j) {
      fprintf(fd, " V%c", digits[j]);
    }
    fprintf(fd, ") ))\n");
  }
}

void gen_fun(FILE *fd, int k, const token * f) {
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
  fprintf(fd, ") (and ");
  fprintf(fd, "(%s", pred->name);
  for(int j = 0; j < pred->arity; ++j) {
    fprintf(fd, " (%s", fun->name);
    for(int i = 0; i < fun->arity; ++i) {
      fprintf(fd, " x%d_%d", i, j);  
    }
    fprintf(fd, ")");
  }

  if(if_not) {
    fprintf(fd, "))))))\n");
  } else {
    fprintf(fd, ")))))\n");
  }
}

