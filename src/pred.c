/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "utils.h"
#include "pred.h"

int pred_construct(uint32_t arity, const char *str, pred *pred) {
  pred->arity      = arity;
  pred->data       = 0;

  for(int pos = int_pow(K, arity) - 1; pos >= 0; --pos) {
    pred->data <<= 1;
    switch(*str) {
    case 0:     return 0;
    case '0':   break;
    case '1':   pred->data |= 1; break;
    default:    return 0;
    }
    ++str;
  }

  /* if the string have not finished yet */
  if(*str) return 0;
  return 1;
}

int pred_consistent(const pred *pred) {
  uint64_t shift = int_pow(K, pred->arity);
  /* check that the `struct pred` has enough bits to store the predicate's
   * content */
  if(shift > 64) return 0;

  /* check that all unnecessary bits in pred->data are set to zero */
  if(pred->data >= (uint64_t)1 << shift) return 0;
  
  return 1;
}

size_t pred_fingerprint_size() {
  return (7             /* for "pred__" string */
          + 2           /* for K */
          + 3           /* for pred->arity */
          + 16          /* for pred->data */
          + 1);         /* for terminating null byte */
}

void pred_print_fingerprint(char *str, const pred *pred) {
  assert(K < 100);
  assert(pred->arity < 1000);
  sprintf(str, "pred%u_%lu_%lx", K, pred->arity, pred->data);
}

size_t pred_print_extensional_size() {
  return 65;            /* 64 bytes + terminating null byte */
}

void pred_print_extensional(char *str, const pred *pred) {
  for(int64_t shift = int_pow(K, pred->arity) - 1; shift >= 0; --shift) {
    if(pred_compute(pred, shift)) {
      str += sprintf(str, "1");
    } else {
      str += sprintf(str, "0");
    }
  }
}

void pred_extensional(const pred *pred, uint32_t **ext, size_t *size) {
  *ext = malloc(int_pow(K, pred->arity) * sizeof(uint32_t));
  assert(*ext != NULL);
  size_t _size = 0;
  for(int64_t shift = int_pow(K, pred->arity) - 1; shift >= 0; --shift) {
    if(pred_compute(pred, shift)) {
      (*ext)[_size] = shift;
      ++_size;
    }
  }
  *size = _size;
}

int64_t pred_cardinality(const pred *pred) {
  return popcount64(pred->data);
}

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

