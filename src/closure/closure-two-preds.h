/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Closure operator for closure-unique essential predicates of arity <= 2.
 ******************************************************************************/

#ifndef CLOSURE_TWO_PREDS_H
#define CLOSURE_TWO_PREDS_H

#include <stdint.h>
#include <stdio.h>

#include "closure.h"
#include "pred-essential.h"
#include "clone.h"

/** Closure operator that uses a precomputed table of closure of pairs of
 * predicates to efficiently compute the closure of the given clone.
 *
 * For a pair of predicates p1, p2 it first computes the the closure of the set
 *      { false(0), true(0), eq(2), p1, p2 }
 * and then keeps closure-unique essential predicates only.
 */
closure_operator *clop_two_preds_read(const char *fname);


/******************************************************************************/
/** Table of closure for all pairs of closure-unique essential predicates of
 * arity <= 2. */

struct closure_table_two_preds {
  clone *data[3][3];
};
typedef struct closure_table_two_preds closure_table_two_preds;

closure_table_two_preds *closure_table_two_preds_alloc();

void closure_table_two_preds_free(closure_table_two_preds *table);

/** `closure_table_two_preds_construct` computes the closure of
 *      { false(0), true(0), eq(2), p1, p2 }
 * for all pairs of closure-unique essential predicates (p1, p2) and writes the
 * result to the table. The closure set will contain closure-unique predicates
 * only, all other predicates will be filtered out from the result.
 *
 * If either p1 or p2 is not a closure-unique essential predicate, the functions
 * writes the empty clone.
 *
 * The function allocates memory to store the table.
 * Memory should be freed by calling `closure_table_two_preds_free`.
 */
void closure_table_two_preds_construct(closure_table_two_preds *);

#endif
