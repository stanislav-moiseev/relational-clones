/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef UTILS_H
#define UTILS_H

#include <stdint.h>
#include <stdio.h>

/** `popcount32`, and `popcount64` returns the number of 1-bits in `x`.
 */
static int popcount32(uint32_t x) {
  return __builtin_popcountl(x);
}
static int popcount64(uint64_t x) {
  return __builtin_popcountll(x);
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


/** K-valued logic. Global constant
 */
static const uint32_t K = 3;

static uint32_t read_uint32(FILE *fd) {
  uint32_t u;
  char c[4];
  assert(fread(&c, 1, 4, fd) == 4);
  
  for (int i = 3; i >= 0; --i) {
    ((char *)&u)[3-i] = c[i];
  }

  return u;

}

static uint64_t read_uint64(FILE *fd) {
  uint64_t u;
  char c[8];
  assert(fread(&c, 1, 8, fd) == 8);
  
  for (int i = 7; i >= 0; --i) {
    ((char *)&u)[7-i] = c[i];
  }

  return u;
}


#endif
