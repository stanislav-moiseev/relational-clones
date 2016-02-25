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

struct clop_two_preds_internals {
  closure_table_two_preds *table2p;
  clone cl_uniq;
};
typedef struct clop_two_preds_internals clop_two_preds_internals;

static inline clone *closure_table_two_preds_lookup(const clop_two_preds_internals *internals, const pred *p1, const pred *p2) {
  assert(p1->arity <= 2 && p2->arity <= 2);
  assert(clone_test_pred(&internals->cl_uniq, p1) && "clop_two_preds is defined for closure-unique essential predicates only");
  assert(clone_test_pred(&internals->cl_uniq, p2) && "clop_two_preds is defined for closure-unique essential predicates only");
  
  uint64_t num2 = int_pow2(int_pow(K, p2->arity));
  uint64_t idx  = p1->data*num2 + p2->data;
  return &internals->table2p->data[p1->arity][p2->arity][idx];
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
        clone *cl = closure_table_two_preds_lookup((const clop_two_preds_internals *)internals, pred1, pred2);
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
  closure_table_two_preds_free(((clop_two_preds_internals *)internals)->table2p);
  free(internals);
}

closure_operator *clop_two_preds_read(const char *fname) {
  closure_operator *clop = malloc(sizeof(closure_operator));
  assert(clop);
  
  FILE *fd = fopen(fname, "rb");
  assert(fd);
  
  closure_table_two_preds *table2p = closure_table_two_preds_alloc();
  closure_two_preds_read(fd, table2p);

  clop->ops.closure_clone_ex = clop_two_preds_closure_clone_ex;
  clop->ops.internals_free   = clop_two_preds_internals_free;
  clop->internals            = malloc(sizeof(struct clop_two_preds_internals));
  ((struct clop_two_preds_internals *)clop->internals)->table2p = table2p;
  closure_uniq_ess_preds(2, &((struct clop_two_preds_internals *)clop->internals)->cl_uniq);


  fclose(fd);
  return clop;
}


/******************************************************************************/
/** Table of closure of all pairs of predicates of arity <= 2 */

closure_table_two_preds *closure_table_two_preds_alloc() {
  closure_table_two_preds *table = malloc(sizeof(closure_table_two_preds));
  assert(table);
  return table;
}

void closure_table_two_preds_free(closure_table_two_preds *table) {
  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      free(table->data[ar1][ar2]);
    }
  }
  free(table);
}

void closure_table_two_preds_construct(closure_table_two_preds *table) {
  closure_operator *clop = clop_alloc_straightforward();

  clone cl_uniq;
  closure_uniq_ess_preds(2, &cl_uniq);

  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      /* number of predicates of the given arity */
      uint64_t num1 = int_pow2(int_pow(K, ar1));
      uint64_t num2 = int_pow2(int_pow(K, ar2));
      
      table->data[ar1][ar2] = aligned_alloc(32, num1 * num2 * sizeof(clone));
      assert(table->data[ar1][ar2] != NULL);
      
      /* initialize the table with empty clones */
      memset(table->data[ar1][ar2], 0, num1 * num2 * sizeof(clone));
      
      for(uint64_t data1 = 0; data1 < num1; ++data1) {
        pred p1 = { .arity = ar1, .data = data1 };
        /* skip if p1 is not a closure-unique essential predicate */
        if(!clone_test_pred(&cl_uniq, &p1)) continue;
        
        for(uint64_t data2 = 0; data2 < num2; ++data2) {
          pred p2 = { .arity = ar2, .data = data2 };
          /* skip if p2 is not a closure-unique essential predicate */
          if(!clone_test_pred(&cl_uniq, &p2)) continue;
          
          clone cl;
          clone_init(&cl);
          clone_insert_dummy_preds(&cl);
          clone_insert_pred(&cl, &p1);
          clone_insert_pred(&cl, &p2);

          /* Compute the full closure (= containing all essential predicates
           * derivable from `cl`. ) */
          clone closure;
          closure_clone(clop, &cl, &closure);
          /* After we've computed the full closure, we leave unique predicates
           * only. */
          clone_intersection(&closure, &cl_uniq, &table->data[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
  clop_free(clop);
}
