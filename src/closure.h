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

/******************************************************************************/
enum closure_operator_type {
  clop_straight_forward_t,
  clop_table_two_preds_t
};
typedef enum closure_operator_type closure_operator_type;

struct closure_operator {
  closure_operator_type type;
  const struct closure_table_two_preds *table2p;
};
typedef struct closure_operator closure_operator;

closure_operator *clop_alloc_straight_forward();

closure_operator *clop_alloc_table_two_preds(const struct closure_table_two_preds *table2p);

void clop_free(closure_operator *clop);


/** `closure_ops1` and `closure_ops2` compute all elementary operations
 * of arity 1 and 2. The exact meaning of "elementary operations" depends on the
 * type of the closure operator.
 *
 * [] clot_straight_forward_t computes the following operations:
 *     - op_permut(1), op_proj(1), op_ident(1);
 *     - op_conj(2), op6(2), op_trans(2).
 *
 * [] clot_table_two_preds_t computes the closure of
 *      { false(0), true(0), eq(2), p1, p2 }
 */
void closure_ops1(const closure_operator *clop, const pred *p1, clone *recruit);
void closure_ops2(const closure_operator *clop, const pred *p1, const pred *p2, clone *recruit);


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
void clone_closure(const closure_operator *clop, const clone *clone, struct clone *closure);

void clone_closure_ex(const closure_operator *clop, const clone *base, const clone *suppl, clone *closure);

/******************************************************************************/
/** Operations over predicates */

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


/******************************************************************************/
/** `clone_insert_dummy_preds` inserts predicates false(0), true(0), eq(2)
 * to the clone.
 */
void clone_insert_dummy_preds(clone *cl);

/** `closure_zero_preds` computes the closure of
 *      { false(0), true(0), eq(2) }
 * and write the result to `closure`.
 */
void closure_zero_preds(const closure_operator *clop, clone *closure);

/** `closure_one_pred` computes the closure of
 *      { false(0), true(0), eq(2), p }
 * and write the result to `closure`.
 */
void closure_one_pred(const closure_operator *clop, const pred *p, clone *closure);

struct closure_table_two_preds {
  clone *data[3][3];
};


typedef struct closure_table_two_preds closure_table_two_preds;

static inline clone *closure_table_two_preds_lookup(const closure_table_two_preds *table, const pred *p1, const pred *p2) {
  assert(p1->arity <= 2 && p2->arity <= 2);
  /* assert(pred_is_essential(p1)); */
  /* assert(pred_is_essential(p2)); */
  uint64_t num2 = int_pow2(int_pow(K, p2->arity));

  uint64_t idx = p1->data*num2 + p2->data;
  return &table->data[p1->arity][p2->arity][idx];
}

closure_table_two_preds *closure_table_two_preds_alloc();

void closure_table_two_preds_free(closure_table_two_preds *table);

/** `closure_table_two_preds_construct` computes the closure of
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


#endif

