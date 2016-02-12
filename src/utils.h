/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef UTILS_H
#define UTILS_H

#include <stdint.h>
#include <stdio.h>

#include "globals.h"


/** `popcount32`, and `popcount64` returns the number of 1-bits in `x`.
 */
static int popcount32(uint32_t x) {
  return __builtin_popcountl(x);
}
static int popcount64(uint64_t x) {
  return __builtin_popcountll(x);
}

/** `int_log` computes the integer logarithm (rounded to ceiling).
 */
static uint64_t int_log(uint64_t base, uint64_t x) {
  uint64_t log = 0;
  uint64_t y = 1;
  while(y < x) {
    ++log;
    y *= base;;
  }
  return log;
}

/** `int_pow` computes the integer power:
 *      int_pow(k, arity) == k^arity
 */
static uint64_t int_pow(uint32_t k, uint32_t arity) {
  uint64_t pow = 1;
  for(uint32_t i = arity; i > 0; --i) {
    pow *= k;
  }
  return pow;
}

/**
 *      int_pow2(x) == 2^x
 */
static uint64_t int_pow2(uint32_t x) {
  return (uint64_t)1 << x;
}

static void get_offset_shift(uint64_t data, uint64_t *offset, uint64_t *shift) {
  *offset = data / 64;
  *shift  = data % 64;
}

/** `get_digits` represents `x` in the K-ary form, with digits[0] being the
 * highest digit.
 *
 * `digits` should be at least of size `arity` */
static void get_K_digits(uint32_t digits[], uint32_t arity, size_t x) {
  for(int j = arity - 1; j >= 0; --j) {
    digits[j] = x % K;
    x /= K;
  }
}

static uint64_t get_K_tuple(uint32_t digits[], uint32_t arity) {
  uint64_t tuple = 0;
  for(size_t i = 0; i < arity; ++i) {
    tuple = K*tuple + digits[i];
  }
  return tuple;
}

#endif
