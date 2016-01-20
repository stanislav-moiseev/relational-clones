/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "pred.h"
#include "utils.h"

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

size_t pred_extensional_size() {
  return 65;            /* 64 bytes + terminating null byte */
}

void pred_print_extensional(char *str, const pred *pred) {
  uint64_t shift = int_pow(K, pred->arity);
    
  for(int s = shift-1; s >= 0; --s) {
    if(pred->data & ((uint64_t)1 << s)) {
      str += sprintf(str, "1");
    } else {
      str += sprintf(str, "0");
    }
  }
}

void pred_read(FILE *fd, pred *pred) {
  uint64_t k = read_uint64(fd);
  assert(k == K);
  
  pred->arity = read_uint64(fd);
  pred->data = read_uint64(fd);

  /* DBG */
  /* char str[pred_extensional_size()]; */
  /* pred_print_extensional(str, pred); */
  /* printf("pred: \t%s\n", str); */
}

