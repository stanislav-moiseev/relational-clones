/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>

#include "binary/common.h"
#include "binary/closure-two-preds.h"

void closure_two_preds_write(FILE *fd, const closure_two_preds_table *table) {
  uint32_write(fd, K);
  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      /* number of predicates of the given arity */
      uint64_t num1 = int_pow2(int_pow(K, ar1));
      uint64_t num2 = int_pow2(int_pow(K, ar2));

      for(uint64_t data1 = 0; data1 < num1; ++data1) {
        for(uint64_t data2 = 0; data2 < num2; ++data2) {
          clone_write(fd, &table->data[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
}

void closure_two_preds_read(FILE *fd, closure_two_preds_table *table) {
  uint32_t k = uint32_read(fd);
  assert(k == K);

  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      /* number of predicates of the given arity */
      uint64_t num1 = int_pow2(int_pow(K, ar1));
      uint64_t num2 = int_pow2(int_pow(K, ar2));
      
      table->data[ar1][ar2] = malloc(num1 * num2 * sizeof(clone));
      assert(table->data[ar1][ar2] != NULL);
      
      for(uint64_t data1 = 0; data1 < num1; ++data1) {
        for(uint64_t data2 = 0; data2 < num2; ++data2) {
          clone_read(fd, &table->data[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
}

