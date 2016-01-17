/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef PREDICATE_H
#define PREDICATE_H

#include <stdint.h>
#include <stdio.h>

/**
 * Possible combinations of `k` and `arity`
 * PRED_DATA_SIZE == 1
 *      k:              2       3       4       5       6
 *      max pred arity: 6       3       3       2       2
 * PRED_DATA_SIZE == 2
 *      k:              2       3       4       5       6
 *      max pred arity: 7       4       3       2       2
 * PRED_DATA_SIZE == 4
 *      k:              2       3       4       5       6
 *      max pred arity: 8       5       4       3       3
 */
#define PRED_DATA_SIZE 4

struct pred {
  uint32_t k;
  uint32_t arity;
  uint64_t data[PRED_DATA_SIZE];
};

typedef struct pred pred;

/** `pred_max_bits` returns the number of bits needed to store the predicate of
 * the given arity,
 *      max_bits == k^arity
 */
inline void pred_max_bits(uint32_t k, uint32_t arity, int *max_bits) {
  int max = 1;
  for(int i = arity; i > 0; --i) {
    max *= k;
  }
  *max_bits = max;
}

inline void pred_max_data(uint32_t k, uint32_t arity, int *max_data, int *max_shift) {
  int max_bits;
  pred_max_bits(k, arity, &max_bits);
  *max_data = max_bits / 64;
  *max_shift = max_bits % 64;
}


/** `pred_construct` constructs a predicate from a string representing its
    extensional.
 */
void pred_construct(uint32_t k, uint32_t arity, const char *str, pred *p);

/** `pred_consistent` returns non-zero if the internal structure of `p` is
 * consistent. In particular, it checks that `struct pred` contains enough bits
 * to store all `k^arity` values of the predicate.
 */
int pred_consistent(const pred *pred);

/** `pred_print` prints the short name of the predicate.
 * The short name contains `k`, `pred->arity` and a string representation
 * of `pred->data` (in hexadecimal format, without preceding zeros).
 */
void pred_print(FILE *file, const pred *pred);

/** `pred_print_extensional` prints the predicate's extensional.
 */
void pred_print_extensional(FILE *file, const pred *pred);

#endif
