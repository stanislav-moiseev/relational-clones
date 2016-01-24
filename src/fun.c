/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "fun.h"

static void fun_offset_shift_mask(uint64_t xs, uint64_t *offset, uint64_t *shift, uint64_t *mask) {
  assert((64 % INT_LOG2K) == 0);
  *offset = (INT_LOG2K * xs) / 64;
  *shift  = (INT_LOG2K * xs) % 64;
  *mask   = (((uint64_t)1<<INT_LOG2K) - 1) << *shift;
}

int fun_consistent(const fun *fun) {
  uint64_t shift = INT_LOG2K * int_pow(K, fun->arity);
  if(shift > 64*FUN_DATA_SIZE) return 0;
  return 1;
}

uint32_t fun_compute(const fun *fun, uint32_t args[]) {
  uint64_t xs = 0;
  for(size_t i = 0; i < fun->arity; ++i) {
    xs = K*xs + args[i];
  }
  uint64_t offset, shift, mask;
  fun_offset_shift_mask(xs, &offset, &shift, &mask);

  return (fun->data[offset] & mask) >> shift;
}

void fun_set_zero(fun *fun, uint32_t arity) {
  fun->arity = arity;
  for(size_t i = 0; i < FUN_DATA_SIZE; ++i) {
    fun->data[i] = 0;
  }
}

void fun_set_val(fun *fun, uint64_t xs, uint64_t y) {
  uint64_t offset, shift, mask;
  fun_offset_shift_mask(xs, &offset, &shift, &mask);

  fun->data[offset] |= (y << shift);
}

static size_t fun_print_size(const fun *fun) {
  assert(K <= 9);               /* use one char per digit in str */
  assert(fun->arity <= 9);
  return 1 + 7 + int_pow(K, fun->arity);
}

char *fun_print(const fun *fun) {
  char *_str = malloc(fun_print_size(fun) * sizeof(char));
  
  char *str = _str;
  str += sprintf(str, "fun%u_%lu_", K, fun->arity);
  for(int64_t xs = int_pow(K, fun->arity) - 1; xs >= 0; --xs) {
    uint64_t offset, shift, mask;
    fun_offset_shift_mask(xs, &offset, &shift, &mask);
    uint64_t y = (fun->data[offset] & mask) >> shift;
    str += sprintf(str, "%ld", y);
  }
  return _str;
}

