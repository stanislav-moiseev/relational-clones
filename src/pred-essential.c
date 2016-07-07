/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "globals.h"
#include "pred-essential.h"
#include "closure/closure-straightforward.h"

static int pred_test_essential(const pred *pred) {
  if(pred->arity == 0) return 1;
  
  for(uint64_t tuple = 0; tuple < int_pow(K, pred->arity); ++tuple) {
    if(!pred_compute(pred, tuple)) {
      uint32_t digits[pred->arity];
      get_K_digits(digits, pred->arity, tuple);
      /* test that for each `i` we can modify the i-th position of `tuple`
       * to make the predicate true */
      int flag0 = 1;
      for(uint32_t i = 0; i < pred->arity; ++i) {
        int flag = 0;
        for(uint32_t t = 0; t < K; ++t) {
          uint32_t digits2[pred->arity];
          memcpy(digits2, digits, sizeof(pred->arity * sizeof(uint32_t)));
          digits2[i] = t;

          uint64_t tuple2 = get_K_tuple(digits2, pred->arity);
          if(pred_compute(pred, tuple2)) { flag = 1; break; }
        }
        if(!flag) { flag0 = 0; break; }
      }
      if(flag0) { return 1; }
    }
  }
  
  return 0;
}

static void pred_is_essential_construct_tables(int **table1, int **table2) {
  (*table1) = malloc(int_pow2(K) * sizeof(int));
  assert((*table1) != NULL);
  for(uint64_t data1 = 0; data1 < int_pow2(K); ++data1) {
    struct pred p = { .arity = 1, .data = data1 };
    if(pred_test_essential(&p)) {
      (*table1)[data1] = 1;
    } else {
      (*table1)[data1] = 0;
    }
  }
    
  (*table2) = malloc(int_pow2(K*K) * sizeof(int));
  assert((*table2) != NULL);
  for(uint64_t data2 = 0; data2 < int_pow2(K*K); ++data2) {
    struct pred p = { .arity = 2, .data = data2 };
    if(pred_test_essential(&p)) {
      (*table2)[data2] = 1;
    } else {
      (*table2)[data2] = 0;
    }
  }
}

int pred_is_essential(const pred *pred) {
  /* membership tables for predicates of arity 1 and 2 */
  static int tables_ready = 0;
  static int *table1, *table2;
  if(!tables_ready) {
    tables_ready = 1;
    pred_is_essential_construct_tables(&table1, &table2);
  }

  /* check membership to precomputed tables of essential predicates */
  switch(pred->arity) {
  case 0:  return 1;
  case 1:  return table1[pred->data];
  case 2:  return table2[pred->data];
  default: return pred_test_essential(pred);
  }
}

void get_essential_predicates(uint32_t max_arity, pred **ess_preds, size_t *size) {
  size_t capacity = 0;
  for(uint32_t ar = 0; ar <= max_arity; ++ar) {
    capacity += int_pow2(int_pow(K, ar));
  }
  *ess_preds = malloc(capacity * sizeof(pred));
  assert(*ess_preds);

  *size = 0;
  for(uint32_t ar = 0; ar <= max_arity; ++ar) {
    for(uint64_t data = 0; data < int_pow2(int_pow(K, ar)); ++data) {
      pred p = { .arity = ar, .data = data };
      if(pred_is_essential(&p)) {
        (*ess_preds)[*size] = p;
        ++(*size);
      }
    }
  }
}


/******************************************************************************/
/** Closure-unique essential predicates */

void closure_uniq_ess_preds(uint32_t max_arity, clone *cl) {
  static int flag = 0;
  static clone clone[3];
  if(!flag) {
    flag = 1;
    pred *uniq_preds;
    size_t uniq_sz;
    for(uint32_t max_ar = 0; max_ar <= 2; ++max_ar) {
      construct_closure_uniq_ess_preds(max_ar, &uniq_preds, &uniq_sz);
      clone_init(clone + max_ar);
      for(pred *p = uniq_preds; p < uniq_preds + uniq_sz; ++p) {
        clone_insert_pred(clone + max_ar, p);
      }
      free(uniq_preds);
    }
  }

  switch(max_arity) {
  case 0: clone_copy(clone + 0, cl); break;
  case 1: clone_copy(clone + 1, cl); break;
  case 2: clone_copy(clone + 2, cl); break;
  default: {
    pred *uniq_preds;
    size_t uniq_sz;
    construct_closure_uniq_ess_preds(max_arity, &uniq_preds, &uniq_sz);
    clone_init(cl);
    for(pred *p = uniq_preds; p < uniq_preds + uniq_sz; ++p) {
      clone_insert_pred(cl, p);
    }
    free(uniq_preds);
  }}
}

void closure_one_pred(const closure_operator *clop, const pred *p, clone *closure) {
  clone_init(closure);

  clone cl = *top_clone();
  clone_insert_pred(&cl, p);

  closure_clone(clop, &cl, closure);
}

void construct_closure_uniq_ess_preds(uint32_t max_arity, pred **_uniq_preds, size_t *_uniq_sz) {
  closure_operator *clop = clop_alloc_straightforward();

  /* compute the closure of all essential predicates */
  pred *ess_preds;
  size_t num_ess_preds;
  get_essential_predicates(max_arity, &ess_preds, &num_ess_preds);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  size_t uniq_sz = 0;
  pred uniq_preds[num_ess_preds];
  clone uniq_closures[num_ess_preds];

  for(pred *p = ess_preds; p < ess_preds + num_ess_preds; ++p) {
    clone p_closure;
    closure_one_pred(clop, p, &p_closure);

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

