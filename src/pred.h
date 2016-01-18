/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef PREDICATE_H
#define PREDICATE_H

#include <stdint.h>
#include <stdio.h>

/**
 * Possible combinations of `k` and `arity`
 *      k:              2       3       4       5       6
 *      max pred arity: 6       3       3       2       2
 */
struct pred {
  uint64_t arity;
  uint64_t data;
};

typedef struct pred pred;

/** `pred_construct` constructs a predicate from a string representing its
 * extensional.
 * `pred_construct` returns non-zero if the construction have proceeded well;
 * otherwise, it returns zero (e.g. when `str` is too short or too long).
 */
int pred_construct(uint32_t arity, const char *str, pred *pred);

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
