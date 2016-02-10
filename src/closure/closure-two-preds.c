/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure-straightforward.h"
#include "closure/closure-two-preds.h"
#include "binary/bin-closure-two-preds.h"

static inline clone *closure_table_two_preds_lookup(const closure_table_two_preds *table, const pred *p1, const pred *p2) {
  assert(p1->arity <= 2 && p2->arity <= 2);
  /* assert(pred_is_essential(p1)); */
  /* assert(pred_is_essential(p2)); */
  
  uint64_t num2 = int_pow2(int_pow(K, p2->arity));
  uint64_t idx = p1->data*num2 + p2->data;
  return &table->data[p1->arity][p2->arity][idx];
}

void clop_two_preds_closure_clone_ex(void *internals, const clone *base, const clone *suppl, clone *closure) {
  clone new_base;
  clone diff;
  clone_copy(suppl, &diff);

  /* we will store base and suppl predicates here*/
  pred preds[2 + int_pow2(K) + int_pow2(K*K)];
  /* predicates in [0 .. base_sz-1] are current base predicates */
  size_t base_sz;
  /* predicates in [base_sz .. sz-1] are current supplement predicates */
  size_t sz = 0;

  /* copy base predicates */
  for(clone_iterator it2 = clone_iterator_begin(base); !clone_iterator_end(base, &it2); clone_iterator_next(&it2)) {
    preds[sz] = clone_iterator_deref(&it2);
    ++sz;
  }
  
  do {
    /* consider all predicates in the array to be base,
     * and copy new predicates to the end of the array */
    base_sz = sz;
    for(clone_iterator it = clone_iterator_begin(&diff); !clone_iterator_end(&diff, &it); clone_iterator_next(&it)) {
      preds[sz] = clone_iterator_deref(&it);
      ++sz;
    }
    
    clone recruit;
    clone_init(&recruit);

    /* scan all supplement predicates */
    for(pred *pred1 = preds + base_sz; pred1 < preds + sz; ++pred1) {
      /* We only need to apply closure to pairs of predicates (not to one predicate).
       * The first predicate is taken from the supplement,
       * while the second — from the supplement set and from the base set */
      for(pred *pred2 = preds; pred2 < preds + sz; ++pred2) {
        clone *cl = closure_table_two_preds_lookup((const closure_table_two_preds *)internals, pred1, pred2);
        clone_union(&recruit, cl, &recruit);
      }
    }

    clone_union(base, suppl, &new_base);
    clone_diff(&recruit, &new_base, &diff);
    base  = &new_base;
    suppl = &diff;
  } while(!clone_is_empty(&diff));
  
  clone_copy(&new_base, closure);
}

static void clop_two_preds_internals_free(void *internals) {
  closure_table_two_preds_free((closure_table_two_preds *)internals);
}

closure_operator *clop_two_preds_read(const char *fname) {
  closure_operator *clop = malloc(sizeof(closure_operator));
  assert(clop);
  
  FILE *fd = fopen(fname, "rb");
  assert(fd);
  
  closure_table_two_preds *table2p = closure_table_two_preds_alloc();
  closure_two_preds_read(fd, table2p);

  clop->internals            = (void *)table2p;
  clop->ops.closure_clone_ex = clop_two_preds_closure_clone_ex;
  clop->ops.internals_free   = clop_two_preds_internals_free;

  fclose(fd);
  return clop;
}


