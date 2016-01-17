/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef PREDICATE_H
#define PREDICATE_H

#include <stdint.h>
#include <stdio.h>

/**
 * Possible combinations of `k` and `arity`:
 * k    arity
 * 2    6
 * 3    3
 * 4    3
 * 5    2
 * ...
 */
struct pred {
  uint32_t k;
  uint32_t arity;
  uint64_t data;
};

typedef struct pred pred;


/** `pred_construct` construct a predicate from a string representing its
    extensional.
 */
void pred_construct(uint32_t k, uint32_t arity, const char *data, pred *p);

/** `pred_check` returns non-zero if the internal structure of `p` is
 * consistent. In particular, it checks that `struct pred` contains enough bits
 * to store all `k^arity` values of the predicate.
 */
int pred_check(const pred *p);

/** `pred_print` prints the short name of the predicate.
 */
void pred_print(FILE *file, const pred *p);

/** `pred_prettyprint` prints the predicate's extensional.
 */
void pred_prettyprint(FILE *file, const pred *p);

#endif
