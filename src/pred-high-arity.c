/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include "pred.h"

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

void pred_construct(uint32_t k, uint32_t arity, const char *str, pred *p) {
  p->k         = k;
  p->arity     = arity;
  for(int i = PRED_DATA_SIZE-1; i >= 0; --i) {
    p->data[i] = 0;
  }

  int max_data, max_shift;
  pred_max_data(k, arity, &max_data, &max_shift);
  int pos = max_shift-1;  /* current position in `str` modulo 64*/
  int d   = max_data; /* current position in pred->data */
  while(*str) {
    if(pos < 0) {
      --d;
      pos = 63;
    }
    assert(*str == '0' || *str == '1');
    assert(d >= 0 && "string is too long");
    
    p->data[d] <<= 1;
    if(*str == '1') { p->data[d] |= 1; }

    ++str;
    --pos;
  }
}

int pred_consistent(const pred *pred) {
  /* check that PRED_DATA_SIZE is large enough */
  int max_bits;
  pred_max_bits(pred->k, pred->arity, &max_bits);
  if(max_bits > 64*PRED_DATA_SIZE) return 0;

  /* check that all unnecessary bits in pred->data are set to zero */
  int max_data, max_shift;
  pred_max_data(pred->k, pred->arity, &max_data, &max_shift);
  assert(max_data <= PRED_DATA_SIZE);
  if(max_data == PRED_DATA_SIZE) { assert(max_shift == 0); return 1; }
  
  for(int d = PRED_DATA_SIZE-1; d > max_data; --d) {
    if(pred->data[d] != 0) return 0;
  }
  if(pred->data[max_data] >= (uint64_t)1 << max_shift) return 0;
  
  return 1;
}

void pred_print(FILE *fd, const pred *pred) {
  fprintf(fd, "pred%u_%u_", pred->k, pred->arity);
  int flag = 1; /* 1 means not to print preceding zeros */
  for(int i = PRED_DATA_SIZE-1; i >= 0; --i) {
    if(flag) {
      if(pred->data[i] == 0) continue;
      flag = 0;
      fprintf(fd, "%lx", pred->data[i]);
    } else {
      /* print `pred->data[i]` with all preceding zeros (up to 8 zeors) */
      fprintf(fd, "%.8lx", pred->data[i]);
    }
  }
}

void pred_print_extensional(FILE *fd, const pred *pred) {
  int max_data, max_shift;
  pred_max_data(pred->k, pred->arity, &max_data, &max_shift);

  /* print high bits */
  for(int i = max_shift-1; i >= 0; --i) {
    if(pred->data[max_data] & ((uint64_t)1 << i)) {
      fprintf(fd, "1");
    } else {
      fprintf(fd, "0");
    }
  }

  /* print low bits */
  for(int d = max_data-1; d >= 0; --d) {
    for(int i = 63; i >= 0; --i) {
      if(pred->data[d] & ((uint64_t)1 << i)) {
        fprintf(fd, "1");
      } else {
        fprintf(fd, "0");
      }
    }
  }
}

