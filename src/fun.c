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

uint32_t fun_compute(const fun *fun, uint64_t tuple) {
  uint64_t offset, shift, mask;
  fun_offset_shift_mask(tuple, &offset, &shift, &mask);

  return (fun->data[offset] & mask) >> shift;
}

void fun_init(fun *fun, uint32_t arity) {
  fun->arity = arity;
  for(size_t i = 0; i < FUN_DATA_SIZE; ++i) {
    fun->data[i] = 0;
  }
}

void fun_set_val(fun *fun, uint64_t xs, uint64_t y) {
  assert(y < K);
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

void fun_print_verbosely(FILE *fd, const fun *fun) {
  for(int64_t tuple = int_pow(K, fun->arity) - 1; tuple >= 0; --tuple) {
    uint32_t val = fun_compute(fun, tuple);
    if(val) {
      uint32_t digits[fun->arity];
      get_K_digits(digits, fun->arity, tuple);
      for(int i = 0; i < fun->arity; ++i) {
        fprintf(fd, "%d", digits[i]);
      }
      fprintf(fd, " :-> %d\n", val);
    }
  }
}

void fun_scan(const char *str, fun *fun) {
  unsigned k, ar;
  sscanf(str, "fun%u_%u_", &k, &ar);
  str += 7;
  assert(k == K);
  fun_init(fun, ar);
  for(int64_t tuple = int_pow(K, fun->arity) - 1; tuple >= 0; --tuple) {
    fun_set_val(fun, tuple, *str-'0');
    ++str;
  }
}

int fun_preserves_pred(const fun *fun, const pred *pred) {
  uint32_t *pred_ext;
  size_t size;
  pred_extensional(pred, &pred_ext, &size);
  if(size == 0) { free(pred_ext); return 1; }

  /* take fun->arity tuples from the predicate;
   * the tuples are encoded as uint64.
   * the value of `pred_tuple[i]` is a position in `pred_ext` */
  uint64_t pred_tuples[fun->arity];
  for(int i = 0; i < fun->arity; ++i) {
    pred_tuples[i] = 0;
  }
  for(;;) {
    /* extract digits from uint64_t encoding of tuples */
    uint32_t digits[fun->arity][pred->arity];
    for(int i = 0; i < fun->arity; ++i) {
      get_K_digits(digits[i], pred->arity, pred_ext[pred_tuples[i]]);
    }
    
    /* transpose the matrix and form `pred->arity` tuples for further function
     * application */
    uint32_t fun_tuples[pred->arity];
    for(int j = 0; j < pred->arity; ++j) {
      fun_tuples[j] = 0;
      for(int i = 0; i < fun->arity; ++i) {
        fun_tuples[j] *= K;
        fun_tuples[j] += digits[i][j];
      }
    }
    
    /* calculate the function on that tuples */
    uint32_t fun_result[pred->arity];
    for(int j = 0; j < pred->arity; ++j) {
      fun_result[j] = fun_compute(fun, fun_tuples[j]);
    }
    
    /* calculate the predicate value on the result of function application,
     * and check that the resultant tuple is from the predicate's extensional */
    if(pred_compute(pred, get_K_tuple(fun_result, pred->arity)) == 0) { free(pred_ext); return 0; }
    
    /* get next tuples */
    int i;
    for(i = fun->arity - 1; i >= 0; --i) {
      pred_tuples[i]++;
      if(pred_tuples[i] == size) {
        pred_tuples[i] = 0;
        continue;
      } else {
        break;
      }
    }
    if(i == -1) break;
  }

  free(pred_ext);
  return 1;
}
