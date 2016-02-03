/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ALGORITHMS_ALG_MAJ_H
#define ALGORITHMS_ALG_MAJ_H

#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "closure.h"

/** `all_essential_predicates` returns a clone containing the set of all
 * essential predicates of arity <= max_arity.
 */
void all_essential_predicates(clone *cl, uint32_t max_arity);

/** `closure_zero_preds` computes the closure of
 *      { false(0), true(0), eq(2) }
 * and write the result to `closure`.
 */
void closure_zero_preds(clone *closure);

/** `closure_one_pred` computes the closure of
 *      { false(0), true(0), eq(2), p }
 * and write the result to `closure`.
 */
void closure_one_pred(const pred *p, clone *closure);


void closure_pred_clone(const pred *p, const clone *cl, clone *closure);

struct closure_two_preds_table {
  clone *data[3][3];
};

typedef struct closure_two_preds_table closure_two_preds_table;

/** `clone_closure_two_preds_construct_table` computes the closure of
 *      { false(0), true(0), eq(2), p1, p2 }
 * for all pairs of essential predicates (p1, p2)
 * and writes the result to the table.
 *
 * If either p1 or p2 is not essential, the functions writes the empty clone.
 *
 * The function allocates memory to store the table.
 * Memory should be freed by calling closure_two_preds_table_free.
 */
void clone_closure_two_preds_construct_table(closure_two_preds_table *table);

void closure_two_preds_table_free(closure_two_preds_table *table);

/* /\** `closure_two_preds` computes the closure of */
/*  *      { false(0), true(0), eq(2), p1, p2 } */
/*  * and inserts the predicates obtained to `closure`. */
/*  *\/ */
/* void closure_two_preds(const pred *p1, const pred *p2, clone *closure); */

#endif
