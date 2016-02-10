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


/******************************************************************************/
/** Table of closure of all pairs of predicates of arity <= 2 */

void closure_uniq_ess_preds(clone *cl) {
  pred *uniq_preds;
  size_t uniq_sz;
  construct_closure_uniq_ess_preds(&uniq_preds, &uniq_sz);

  clone_init(cl);
  for(pred *p = uniq_preds; p < uniq_preds + uniq_sz; ++p) {
    clone_insert_pred(cl, p);
  }
  free(uniq_preds);
}

void construct_closure_uniq_ess_preds(pred **_uniq_preds, size_t *_uniq_sz) {
  closure_operator *clop = clop_alloc_straightforward();

  clone closure_zero;
  closure_dummy_clone(clop, &closure_zero);

  /* compute the closure of all essential predicates */
  pred *ess_preds;
  size_t num_ess_preds;
  uint32_t max_arity = 2;
  get_essential_predicates(max_arity, &ess_preds, &num_ess_preds);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  size_t uniq_sz = 0;
  pred uniq_preds[num_ess_preds];
  clone uniq_closures[num_ess_preds];

  for(pred *p = ess_preds; p < ess_preds + num_ess_preds; ++p) {
    clone p_closure;
    closure_one_pred(clop, p, &p_closure);

    /* we omit predicates equivalent to the top class {false(0), true(1), eq(2)} */
    if(clone_eq(&p_closure, &closure_zero)) continue;

    size_t j;
    for(j = 0; j < uniq_sz; ++j) {
      if(clone_eq(&p_closure, &uniq_closures[j])) break;
    }
    
    /* if not found, add to the list of unique clones */
    if(j == uniq_sz) {
      uniq_preds[uniq_sz] = *p;
      clone_copy(&p_closure, &uniq_closures[uniq_sz]);
      ++uniq_sz;
    }
  }
  
  /* copy the result */
  *_uniq_preds = malloc(uniq_sz * sizeof(pred));
  assert(_uniq_preds);
  memcpy(*_uniq_preds, uniq_preds, uniq_sz * sizeof(pred));
  *_uniq_sz = uniq_sz;

  free(ess_preds);
  clop_free(clop);
}

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

void closure_uniq_ess_preds(clone *cl);

void closure_table_two_preds_construct(closure_table_two_preds *table) {
  closure_operator *clop = clop_alloc_straightforward();

  clone cl_uniq;
  closure_uniq_ess_preds(&cl_uniq);

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
        /* if p1 is not essential, write empty clones */
        if(!pred_is_essential(&p1)) continue;
        
        for(uint64_t data2 = 0; data2 < num2; ++data2) {
          pred p2 = { .arity = ar2, .data = data2 };
          /* if p2 is not essential, write empty clone */
          if(!pred_is_essential(&p2)) continue;
          
          clone cl;
          clone_init(&cl);
          clone_insert_dummy_preds(&cl);
          clone_insert_pred(&cl, &p1);
          clone_insert_pred(&cl, &p2);

          /* leave only closure-unique predicates */
          clone closure;
          closure_clone(clop, &cl, &closure);
          clone_intersection(&closure, &cl_uniq, &table->data[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
  clop_free(clop);
}
