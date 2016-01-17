/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include "pred.h"

#include <stdlib.h>
#include <stdio.h>

void pred_construct(uint32_t k, uint32_t arity, const char *data, pred *p) {
  p->k          = k;
  p->arity      = arity;
  p->data       = 0;
  while(*data) {
    p->data <<= 1;
    if(*data == '1') p->data |= 1;
  }
}

int pred_check(const pred *p) {
  uint32_t max = 1;
  for(uint32_t i = p->arity; i > 0; --i) {
    max *= p->k;
    if(max > 64) return 0;
  }
  /* max == k^arity */

  if(p->data >= (uint64_t)1 << max) return 0;
  return 1;
}

void pred_print(FILE *file, const pred *p) {
  fprintf(file, "pred%u_%u_%lx", p->k, p->arity, p->data);
}

void pred_prettyprint(FILE *file, const pred *p) {
  fprintf(file, "pred%u_%u_{", p->k, p->arity);
  
  int max = 1;
  for(int i = p->arity; i > 0; --i) {
    max *= p->k;
  }
  /* max == k^arity */
  
  for(int i = max-1; i >= 0; --i) {
    if(p->data & ((uint64_t)1 << i)) {
      fprintf(file, "1");
    } else {
      fprintf(file, "0");
    }
  }
  fprintf(file, "}");
}

