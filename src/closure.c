/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "closure.h"

void op_permut(const pred *pred, clone *clone) {
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

void op_proj(const pred *pred, clone *clone) {
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

void op_ident(const pred *pred, clone *clone) {
  assert(pred->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");

  if(pred->arity != 2) return;

  /* resp(x0) = pred(x0,x0) */
  struct pred resp;
  pred_init(&resp, 2);        /* set to zero */
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

void op_conj(const pred *pred1, const pred *pred2, clone *clone) {
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

void op6(const pred *pred1, const pred *pred2, clone *clone) {
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

void op_trans(const pred *pred1, const pred *pred2, clone *clone) {
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

static void clone_closure_ex(const clone *base, const clone *suppl, clone *closure) {
  clone recruit;
  clone_init(&recruit);
  
  /* apply ops of arity 1 for supplement predicates */
  for(clone_iterator it = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    op_permut(&pred, &recruit);
    op_proj(&pred, &recruit);
    op_ident(&pred, &recruit);
  }

  /* apply ops of arity 2:
   * the first predicate is taken from the base set, and the second — from the supplement set. */
  for(clone_iterator it1 = clone_iterator_begin(base); !clone_iterator_end(base, &it1); clone_iterator_next(&it1)) {
    pred pred1 = clone_iterator_deref(&it1);
    for(clone_iterator it2 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it2); clone_iterator_next(&it2)) {
      pred pred2 = clone_iterator_deref(&it2);
      op_conj(&pred1, &pred2, &recruit);
      op6(&pred1, &pred2, &recruit);
      op_trans(&pred1, &pred2, &recruit);
    }
  }
  
  /* apply ops of arity 2:
   * both predicates are taken from the supplement set */
  for(clone_iterator it1 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it1); clone_iterator_next(&it1)) {
    pred pred1 = clone_iterator_deref(&it1);
    for(clone_iterator it2 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it2); clone_iterator_next(&it2)) {
      pred pred2 = clone_iterator_deref(&it2);
      op_conj(&pred1, &pred2, &recruit);
      op6(&pred1, &pred2, &recruit);
      op_trans(&pred1, &pred2, &recruit);
    }
  }

  clone new_base;
  clone_union(base, suppl, &new_base);

  clone diff;
  clone_diff(&recruit, &new_base, &diff);
  
  if(!clone_is_empty(&diff)) {
    /* if we've found new predicates, recursively continue computation */
    clone_closure_ex(&new_base, &diff, closure);
  } else {
    /* if we haven't found new predicates, the computation is finished */
    clone_copy(&new_base, closure);
  }
}

void clone_closure(const clone *clone, struct clone *closure) {
  clone_init(closure);
  
  struct clone empty;
  clone_init(&empty);
  clone_closure_ex(&empty, clone, closure);
}
