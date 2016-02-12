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

#define PRED_FINGERPRINT_SIZE                    \
  (7             /* for "pred__" string */       \
   + 2           /* for K */                     \
   + 3           /* for pred->arity */           \
   + 16          /* for pred->data */            \
   + 1)          /* for terminating null byte */ \

const char *pred_print_fingerprint(const pred *pred) {
  assert(K < 100);
  assert(pred->arity < 1000);
  static char str[PRED_FINGERPRINT_SIZE];
  sprintf(str, "pred%u_%lu_%lx", K, pred->arity, pred->data);
  return str;
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

const char *pred_print_extensional_ex(const pred *p) {
  assert(p->arity <= 2);
  static char _str[64];
  char *str = _str;
  
  /* treat predicates of zero arity specially */
  if(p->arity == 0) {
    if(p->data != 0) sprintf(str, "true(0)");
    else sprintf(str, "false(0)");
    return str;
  }

  str += sprintf(str, "{");
  int flag = 0; /* if we've written at least one tuple. */
  for(int64_t shift = int_pow(K, p->arity) - 1; shift >= 0; --shift) {
    if(pred_compute(p, shift)) {
      if(flag) str += sprintf(str, ", ");
      uint32_t digits[p->arity];
      get_K_digits(digits, p->arity, shift);
      for(size_t i = 0; i < p->arity; ++i) {
        str += sprintf(str, "%u", digits[i]);
      }
      flag = 1;
    }
  }
  str += sprintf(str, "}");
  
  return _str;
}


/******************************************************************************/
/** basic operations */

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
