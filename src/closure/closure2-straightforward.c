/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure2-straightforward.h"


/******************************************************************************/
/** Closure operator that computes elementary operation directly.
 */

void clop2_straightforward_closure_clone_ex(void *internals, const clone *base, const clone *suppl, struct clone *closure) {
  clone recruit;
  clone_init(&recruit);
  
  for(clone_iterator it1 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it1); clone_iterator_next(&it1)) {
    pred p1 = clone_iterator_deref(&it1);
    
    /* apply ops of arity 1 for supplement predicates */
    pred q = op_perm2(&p1);
    clone_insert_pred(&recruit, &q);

    /* apply ops of arity 2:
     * the first predicate is taken from  the supplement,
     * while the second — from the supplement set and from the base set */
    for(clone_iterator it2 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it2); clone_iterator_next(&it2)) {
      pred p2 = clone_iterator_deref(&it2);
      pred q;
      q = op_conj2(&p1, &p2);
      clone_insert_pred(&recruit, &q);
      q = op_comp2(&p1, &p2);
      clone_insert_pred(&recruit, &q);
    }
    for(clone_iterator it3 = clone_iterator_begin(base); !clone_iterator_end(base, &it3); clone_iterator_next(&it3)) {
      pred p3 = clone_iterator_deref(&it3);
      pred q;
      q = op_conj2(&p1, &p3);
      clone_insert_pred(&recruit, &q);
      q = op_comp2(&p1, &p3);
      clone_insert_pred(&recruit, &q);
    }
  }

  clone new_base;
  clone_union(base, suppl, &new_base);

  clone diff;
  clone_diff(&recruit, &new_base, &diff);
  
  if(!clone_is_empty(&diff)) {
    /* if we've found new predicates, recursively continue computation */
    clop2_straightforward_closure_clone_ex(internals, &new_base, &diff, closure);
  } else {
    /* if we haven't found new predicates, the computation is finished */
    clone_copy(&new_base, closure);
  }
}

static void clop2_straightforward_internals_free(void *internals) {
}

closure_operator *clop2_alloc_straightforward() {
  closure_operator *clop2 = malloc(sizeof(closure_operator));
  assert(clop2);
  clop2->internals            = NULL;
  clop2->ops.closure_clone_ex = clop2_straightforward_closure_clone_ex;
  clop2->ops.internals_free   = clop2_straightforward_internals_free;
  return clop2;
}


/******************************************************************************/
/** Elementary operations over predicates */

pred op_perm2(const pred *pred) {
  assert(pred->arity == 2 && "predicate operations have been implemented for pred->arity == 2 only");

  struct pred resp;
  pred_init(&resp, 2);        /* set to zero */

  /* resp(x1,x0) = pred(x0,x1) */
  for(uint32_t x1 = 0; x1 < K; ++x1) {
    for(uint32_t x0 = 0; x0 < K; ++x0) {
      uint64_t pred_tuple = x1*K + x0;
      uint64_t resp_tuple = x0*K + x1;
      if(pred_compute(pred, pred_tuple)) {
        pred_set(&resp, resp_tuple);
      }
    }
  }
  
  return resp;
}

pred op_conj2(const pred *pred1, const pred *pred2) {
  assert(pred1->arity == 2 && "predicate operations have been implemented for pred->arity == 2 only");
  assert(pred2->arity == 2 && "predicate operations have been implemented for pred->arity == 2 only");
      
  pred resp;
  pred_init(&resp, 2);        /* set to zero */
  
  /* resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1,x0) */
  for(uint64_t tuple = 0; tuple < K*K; ++tuple) {
    if(pred_compute(pred1, tuple) && pred_compute(pred2, tuple)) {
      pred_set(&resp, tuple);
    }
  }

  return resp;
}

pred op_comp2(const pred *pred1, const pred *pred2) {
  assert(pred1->arity == 2 && "predicate operations have been implemented for pred->arity == 2 only");
  assert(pred2->arity == 2 && "predicate operations have been implemented for pred->arity == 2 only");

  pred resp;
  pred_init(&resp, 2);
  
  /* resp(x1,x0) = ∃x (pred1(x1,x) ∧ pred2(x,x0)) */
  for(uint32_t x1 = 0; x1 < K; ++x1) {
    for(uint32_t x0 = 0; x0 < K; ++x0) {
      uint64_t resp_tuple = x1*K + x0;
      for(uint32_t x = 0; x < K; ++x) {
        uint64_t pred1_tuple = x1*K + x;
        uint64_t pred2_tuple = x*K + x0;
        if(pred_compute(pred1, pred1_tuple) && pred_compute(pred2, pred2_tuple)) {
          pred_set(&resp, resp_tuple);
          break;
        }
      }
    }
  }

  return resp;
}


