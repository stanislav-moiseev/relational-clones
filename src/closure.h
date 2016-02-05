/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Closure operator for predicates of arity <= 2.
 ******************************************************************************/

#ifndef CLOSURE_H
#define CLOSURE_H

#include <stdint.h>
#include <stdio.h>

#include "utils.h"
#include "fun.h"
#include "pred.h"
#include "clone.h"

/** Permutation of variables:
 *      resp(x1,x0) = pred(x0,x1)
 */
void op_permut(const pred *pred, clone *clone);

/** Striking of rows:
 *      resp0(y0) = ∃x0 pred(y0,x0)
 */
void op_proj(const pred *pred, clone *clone);

/** Identifying of variables:
 *      resp(x0) = pred(x0,x0)
 */
void op_ident(const pred *pred, clone *clone);

/** Conjunction of two predicates, pred1 being of arity 2 and
 * pred2 of arity 2 or 1 (or vice versa).
 *
 *      resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1,x0)       (for arity 2)
 *      resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1)          (for arity 1)
 */
void op_conj(const pred *pred1, const pred *pred2, clone *clone);

/** Conjunction  with predicate of arity 1 with striking.
 * The operation takes two predicates, pred1 of arity 2 and pred2 of arity 1
 * (or vise versa):
 *      resp(x0) = ∃x1 (pred1(x1,x0) ∧ pred2(x1))
 */
void op6(const pred *pred1, const pred *pred2, clone *clone);

/** Transitivity.
 * The operation takes two predicates of arity 2:
 *      resp(x1, x0) = ∃x (pred1(x,x1) ∧ pred2(x,x0))
 */
void op_trans(const pred *pred1, const pred *pred2, clone *clone);

/** `clone_closure` computes the closure of the given clone under the above
 * operation, selects all essential predicates, and writes the result to
 * `closure`.
 * 
 * Assumptions over `clone`:
 * 1) the clone contains the following predicates:
 *      false(0), true(0), eq(2);
 * 2) the clone consists of essential predicates only.
 *
 * The current implementation supports predicates of arity <= 2 only.
 */
void clone_closure(const clone *clone, struct clone *closure);


/******************************************************************************/
/** `clone_insert_dummy_preds` inserts predicates false(0), true(0), eq(2)
 * to the clone.
 */
void clone_insert_dummy_preds(clone *cl);

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

struct closure_table_two_preds {
  clone *data[3][3];
};

typedef struct closure_table_two_preds closure_table_two_preds;


closure_table_two_preds *closure_table_two_preds_alloc();

void closure_table_two_preds_free(closure_table_two_preds *table);

/** `closure_table_two_preds_construct_table` computes the closure of
 *      { false(0), true(0), eq(2), p1, p2 }
 * for all pairs of essential predicates (p1, p2)
 * and writes the result to the table.
 *
 * If either p1 or p2 is not essential, the functions writes the empty clone.
 *
 * The function allocates memory to store the table.
 * Memory should be freed by calling closure_table_two_preds_free.
 */
void closure_table_two_preds_construct(closure_table_two_preds *);


/* /\** `closure_two_preds` computes the closure of */
/*  *      { false(0), true(0), eq(2), p1, p2 } */
/*  * and inserts the predicates obtained to `closure`. */
/*  *\/ */
/* void closure_two_preds(const pred *p1, const pred *p2, clone *closure); */

/** `closure_pred_clone` computes a closure of the union
 * {p} ∪ cl
 */
void closure_pred_clone(const pred *p, const clone *cl, clone *closure);


#endif


