/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "algorithm/alg-closure-two-preds.h"
#include "closure/closure-straightforward.h"
#include "closure/closure-two-preds.h"
#include "binary/bin-closure-two-preds.h"


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
