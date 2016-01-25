/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

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

int pred_compute(const pred *pred, uint64_t tuple) {
  if(pred->data & ((uint64_t)1 << tuple)) {
    return 1;
  } else {
    return 0;
  }
}

