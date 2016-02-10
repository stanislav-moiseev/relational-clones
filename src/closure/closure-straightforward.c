/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure-straightforward.h"

void clop_straightforward_closure_clone_ex(void *internals, const clone *base, const clone *suppl, struct clone *closure) {
  clone recruit;
  clone_init(&recruit);
  
  for(clone_iterator it1 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it1); clone_iterator_next(&it1)) {
    pred p1 = clone_iterator_deref(&it1);
    
    /* apply ops of arity 1 for supplement predicates */
    op_permut(&p1, &recruit);
    op_proj(&p1, &recruit);
    op_ident(&p1, &recruit);

    /* apply ops of arity 2:
     * the first predicate is taken from  the supplement,
     * while the second — from the supplement set and from the base set */
    for(clone_iterator it2 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it2); clone_iterator_next(&it2)) {
      pred p2 = clone_iterator_deref(&it2);
      op_conj(&p1, &p2, &recruit);
      op6(&p1, &p2, &recruit);
      op_trans(&p1, &p2, &recruit);
    }
    for(clone_iterator it3 = clone_iterator_begin(base); !clone_iterator_end(base, &it3); clone_iterator_next(&it3)) {
      pred p3 = clone_iterator_deref(&it3);
      op_conj(&p1, &p3, &recruit);
      op6(&p1, &p3, &recruit);
      op_trans(&p1, &p3, &recruit);
    }
  }

  clone new_base;
  clone_union(base, suppl, &new_base);

  clone diff;
  clone_diff(&recruit, &new_base, &diff);
  
  if(!clone_is_empty(&diff)) {
    /* if we've found new predicates, recursively continue computation */
    clop_straightforward_closure_clone_ex(internals, &new_base, &diff, closure);
  } else {
    /* if we haven't found new predicates, the computation is finished */
    clone_copy(&new_base, closure);
  }
}

static void clop_straightforward_internals_free(void *internals) {
}

closure_operator *clop_alloc_straightforward() {
  closure_operator *clop = malloc(sizeof(closure_operator));
  assert(clop);
  clop->internals            = NULL;
  clop->ops.closure_clone_ex = clop_straightforward_closure_clone_ex;
  clop->ops.internals_free   = clop_straightforward_internals_free;
  return clop;
}



/******************************************************************************/
/** Elementary operations over predicates */

static void op_permut(const pred *pred, clone *clone) {
  assert(pred->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");
  
  if(pred->arity != 2) return;

  /* resp(x1,x0) = pred(x0,x1) */
  struct pred resp;
  pred_init(&resp, 2);        /* set to zero */
  for(uint32_t x1 = 0; x1 < K; ++x1) {
    for(uint32_t x0 = 0; x0 < K; ++x0) {
      uint64_t pred_tuple = x1*K + x0;
      uint64_t resp_tuple = x0*K + x1;
      if(pred_compute(pred, pred_tuple)) {
        pred_set(&resp, resp_tuple);
      }
    }
  }
  clone_insert_pred(clone, &resp);
}

static void op_proj(const pred *pred, clone *clone) {
  assert(pred->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");
  
  if(pred->arity != 2) return;
    
  struct pred resp;

  /* resp0(y0) = ∃x0 pred(y0,x0) */
  pred_init(&resp, 1);        /* set to zero */
  for(uint32_t y0 = 0; y0 < K; ++y0) {
    uint64_t resp_tuple = y0;
    for(uint32_t x0 = 0; x0 < K; ++x0) {
      uint64_t tuple = y0*K + x0;
      if(pred_compute(pred, tuple)) {
        pred_set(&resp, resp_tuple);
        break;
      }
    }
  }
  if(pred_is_essential(&resp)) {
    clone_insert_pred(clone, &resp);
  }
}

static void op_ident(const pred *pred, clone *clone) {
  assert(pred->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");

  if(pred->arity != 2) return;

  /* resp(x0) = pred(x0,x0) */
  struct pred resp;
  pred_init(&resp, 1);        /* set to zero */
  for(uint32_t x0 = 0; x0 < K; ++x0) {
    uint64_t resp_tuple = x0;
    uint64_t pred_tuple = x0*K + x0;
    if(pred_compute(pred, pred_tuple)) {
      pred_set(&resp, resp_tuple);
    }
  }
  if(pred_is_essential(&resp)) {
    clone_insert_pred(clone, &resp);
  }
}

static void op_conj(const pred *pred1, const pred *pred2, clone *clone) {
  assert(pred1->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");
  assert(pred2->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");

  if(pred2->arity > pred1->arity) {
    const pred *tmp = pred1;
    pred1 = pred2;
    pred2 = tmp;
  }
  assert(pred1->arity >= pred2->arity);

  if(pred1->arity != 2) return;
  
  switch(pred2->arity) {
    case 0:
      return;
      
    case 1: {
      pred resp;
      pred_init(&resp, 2);
      /* resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1) */
      for(uint32_t x1 = 0; x1 < K; ++x1) {
        for(uint32_t x0 = 0; x0 < K; ++x0) {
          uint64_t resp_tuple = x1*K + x0;
          uint64_t pred2_tuple = x1;
          if(pred_compute(pred1, resp_tuple) && pred_compute(pred2, pred2_tuple)) {
            pred_set(&resp, resp_tuple);
          }
        }
      }
      if(pred_is_essential(&resp)) {
        clone_insert_pred(clone, &resp);
      }
    }
      
    case 2: {
      pred resp;
      pred_init(&resp, 2);
      /* resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1,x0) */
      for(uint64_t tuple = 0; tuple < K*K; ++tuple) {
        if(pred_compute(pred1, tuple) && pred_compute(pred2, tuple)) {
          pred_set(&resp, tuple);
        }
      }
      if(pred_is_essential(&resp)) {
        clone_insert_pred(clone, &resp);
      }
      return;
    }}
}

static void op6(const pred *pred1, const pred *pred2, clone *clone) {
  assert(pred1->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");
  assert(pred2->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");

  if(pred2->arity > pred1->arity) {
    const pred *tmp = pred1;
    pred1 = pred2;
    pred2 = tmp;
  }
  assert(pred1->arity >= pred2->arity);
  
  if(pred1->arity != 2 || pred2->arity != 1) return;
  
  pred resp;
  pred_init(&resp, 1);
  /* resp(x0) = ∃x1 (pred1(x1,x0) ∧ pred2(x1)) */
  for(uint32_t x0 = 0; x0 < K; ++x0) {
    uint64_t resp_tuple = x0;
    for(uint32_t x1 = 0; x1 < K; ++x1) {
      uint64_t pred1_tuple = x1*K + x0;
      uint64_t pred2_tuple = x1;
      if(pred_compute(pred1, pred1_tuple) && pred_compute(pred2, pred2_tuple)) {
        pred_set(&resp, resp_tuple);
        break;
      }
    }
  }
  if(pred_is_essential(&resp)) {
    clone_insert_pred(clone, &resp);
  }
  return;
}

static void op_trans(const pred *pred1, const pred *pred2, clone *clone) {
  assert(pred1->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");
  assert(pred2->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");

  if(pred1->arity != 2 || pred2->arity != 2) return;

  pred resp;
  pred_init(&resp, 2);
  /* resp(x1,x0) = ∃x (pred1(x,x1) ∧ pred2(x,x0)) */
  for(uint32_t x1 = 0; x1 < K; ++x1) {
    for(uint32_t x0 = 0; x0 < K; ++x0) {
      uint64_t resp_tuple = x1*K + x0;
      for(uint32_t x = 0; x < K; ++x) {
        uint64_t pred1_tuple = x*K + x1;
        uint64_t pred2_tuple = x*K + x0;
        if(pred_compute(pred1, pred1_tuple) && pred_compute(pred2, pred2_tuple)) {
          pred_set(&resp, resp_tuple);
          break;
        }
      }
    }
  }
  if(pred_is_essential(&resp)) {
    clone_insert_pred(clone, &resp);
  }
}
