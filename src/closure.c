/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure.h"

closure_operator *clop_alloc_straight_forward() {
  closure_operator *clop = malloc(sizeof(closure_operator));
  assert(clop);

  clop->type    = clop_straight_forward_t;
  clop->table2p = NULL;

  return clop;
}

closure_operator *clop_alloc_table_two_preds(const closure_table_two_preds *table2p) {
  closure_operator *clop = malloc(sizeof(closure_operator));
  assert(clop);

  clop->type    = clop_table_two_preds_t;
  clop->table2p = table2p;

  return clop;
}

void clop_free(closure_operator *clop) {
  free(clop);
}

void closure_ops1(const closure_operator *clop, const pred *p1, clone *recruit) {
  switch(clop->type) {
  case clop_straight_forward_t:
    op_permut(p1, recruit);
    op_proj(p1, recruit);
    op_ident(p1, recruit);
    break;
    
  case clop_table_two_preds_t: {
    clone *cl = closure_table_two_preds_lookup(clop->table2p, p1, p1);
    clone_union(recruit, cl, recruit);
    break;
  }}
}

void closure_ops2(const closure_operator *clop, const pred *p1, const pred *p2, clone *recruit) {
  switch(clop->type) {
  case clop_straight_forward_t:
    op_conj(p1, p2, recruit);
    op6(p1, p2, recruit);
    op_trans(p1, p2, recruit);
    break;
    
  case clop_table_two_preds_t: {
    clone *cl = closure_table_two_preds_lookup(clop->table2p, p1, p2);
    clone_union(recruit, cl, recruit);
    break;
  }}
}

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

static void clone_closure_ex(const closure_operator *clop, const clone *base, const clone *suppl, clone *closure) {
  clone recruit;
  clone_init(&recruit);
  
  /* apply ops of arity 1 for supplement predicates */
  for(clone_iterator it = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    closure_ops1(clop, &pred, &recruit);
  }

  /* apply ops of arity 2:
   * the first predicate is taken from the base set, and the second — from the supplement set. */
  for(clone_iterator it1 = clone_iterator_begin(base); !clone_iterator_end(base, &it1); clone_iterator_next(&it1)) {
    pred pred1 = clone_iterator_deref(&it1);
    for(clone_iterator it2 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it2); clone_iterator_next(&it2)) {
      pred pred2 = clone_iterator_deref(&it2);
      closure_ops2(clop, &pred1, &pred2, &recruit);
    }
  }
  
  /* apply ops of arity 2:
   * both predicates are taken from the supplement set */
  for(clone_iterator it1 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it1); clone_iterator_next(&it1)) {
    pred pred1 = clone_iterator_deref(&it1);
    for(clone_iterator it2 = clone_iterator_begin(suppl); !clone_iterator_end(suppl, &it2); clone_iterator_next(&it2)) {
      pred pred2 = clone_iterator_deref(&it2);
      closure_ops2(clop, &pred1, &pred2, &recruit);
    }
  }

  clone new_base;
  clone_union(base, suppl, &new_base);

  clone diff;
  clone_diff(&recruit, &new_base, &diff);
  
  if(!clone_is_empty(&diff)) {
    /* if we've found new predicates, recursively continue computation */
    clone_closure_ex(clop, &new_base, &diff, closure);
  } else {
    /* if we haven't found new predicates, the computation is finished */
    clone_copy(&new_base, closure);
  }
}

void clone_closure(const closure_operator *clop, const clone *clone, struct clone *closure) {
  clone_init(closure);
  
  struct clone empty;
  clone_init(&empty);
  clone_closure_ex(clop, &empty, clone, closure);
}


/******************************************************************************/
void clone_insert_dummy_preds(clone *cl) {
  pred p_false, p_true, p_eq;
  pred_construct(0, "0", &p_false);
  pred_construct(0, "1", &p_true);
  pred_construct(2, "100010001", &p_eq);

  clone_insert_pred(cl, &p_false);
  clone_insert_pred(cl, &p_true);
  clone_insert_pred(cl, &p_eq);
}

void closure_zero_preds(const closure_operator *clop, clone *closure) {
  clone_init(closure);
  
  clone cl;
  clone_init(&cl);
  
  clone_insert_dummy_preds(&cl);

  clone_closure(clop, &cl, closure);
}

void closure_one_pred(const closure_operator *clop, const pred *p, clone *closure) {
  clone_init(closure);

  clone cl;
  clone_init(&cl);
  
  clone_insert_dummy_preds(&cl);
  clone_insert_pred(&cl, p);

  clone_closure(clop, &cl, closure);
}

void closure_pred_clone(const closure_operator *clop, const pred *p, const clone *cl, clone *closure) {
  clone union_cl;
  clone_copy(cl, &union_cl);
  clone_insert_pred(&union_cl, p);

  clone_closure(clop, &union_cl, closure);
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

void closure_table_two_preds_construct(closure_table_two_preds *table) {
  closure_operator *clop = clop_alloc_straight_forward();

  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      /* number of predicates of the given arity */
      uint64_t num1 = int_pow2(int_pow(K, ar1));
      uint64_t num2 = int_pow2(int_pow(K, ar2));
      
      table->data[ar1][ar2] = malloc(num1 * num2 * sizeof(clone));
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
          
          clone_closure(clop, &cl, &table->data[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
  clop_free(clop);
}
