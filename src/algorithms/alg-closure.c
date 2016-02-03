/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "algorithms/alg-closure.h"

void closure_two_preds_table_free(closure_two_preds_table *table) {
  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      free(table->data[ar1][ar2]);
    }
  }
}

void clone_closure_two_preds_construct_table(closure_two_preds_table *table) {
  /* we insert these predicates to every clone */
  pred p_false, p_true, p_eq;
  pred_construct(0, "0", &p_false);
  pred_construct(0, "1", &p_true);
  pred_construct(2, "100010001", &p_eq);

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
          clone_insert_pred(&cl, &p_false);
          clone_insert_pred(&cl, &p_true);
          clone_insert_pred(&cl, &p_eq);
          clone_insert_pred(&cl, &p1);
          clone_insert_pred(&cl, &p2);
          
          clone_closure(&cl, &table->data[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
}
