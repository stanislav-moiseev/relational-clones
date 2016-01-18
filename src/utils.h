/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef UTILS_H
#define UTILS_H

#include <stdint.h>

/** `pow` computes the integer power:
 *      pow(k, arity) == k^arity
 */
inline uint64_t int_pow(uint32_t k, uint32_t arity) {
  uint64_t pow = 1;
  for(uint32_t i = arity; i > 0; --i) {
    pow *= k;
  }
  return pow;
}

/** K-valued logic. Global constant
 */
static const uint32_t K = 3;

#endif
