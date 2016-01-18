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

void pred_print(FILE *fd, const pred *pred) {
  fprintf(fd, "pred%u_%lu_%lx", K, pred->arity, pred->data);
}

void pred_print_extensional(FILE *fd, const pred *pred) {
  uint64_t shift = int_pow(K, pred->arity);
    
  for(int s = shift-1; s >= 0; --s) {
    if(pred->data & ((uint64_t)1 << s)) {
      fprintf(fd, "1");
    } else {
      fprintf(fd, "0");
    }
  }
}

