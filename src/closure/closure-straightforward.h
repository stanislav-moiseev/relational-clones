/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Closure operator for predicates of arity <= 2.
 ******************************************************************************/

#ifndef CLOSURE_STRAIGTFORWARD_H
#define CLOSURE_STRAIGTFORWARD_H

#include <stdint.h>
#include <stdio.h>

#include "closure.h"
#include "pred-essential.h"

/** Closure operator that computes elementary operation directly:
 *     - op_permut(1), op_proj(1), op_ident(1);
 *     - op_conj(2), op6(2), op_trans(2).
 */
closure_operator *clop_alloc_straightforward();


/******************************************************************************/
/** Elementary operations over essential predicates */

/** Permutation of variables:
 *      resp(x1,x0) = pred(x0,x1)
 */
static void op_permut(const pred *pred, clone *clone);

/** Striking of rows:
 *      resp0(y0) = ∃x0 pred(y0,x0)
 */
static void op_proj(const pred *pred, clone *clone);

/** Identifying of variables:
 *      resp(x0) = pred(x0,x0)
 */
static void op_ident(const pred *pred, clone *clone);

/** Conjunction of two predicates, pred1 being of arity 2 and
 * pred2 of arity 2 or 1 (or vice versa).
 *
 *      resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1,x0)       (for arity 2)
 *      resp(x1,x0) = pred1(x1,x0) ∧ pred2(x1)          (for arity 1)
 */
static void op_conj(const pred *pred1, const pred *pred2, clone *clone);

/** Conjunction  with predicate of arity 1 with striking.
 * The operation takes two predicates, pred1 of arity 2 and pred2 of arity 1
 * (or vise versa):
 *      resp(x0) = ∃x1 (pred1(x1,x0) ∧ pred2(x1))
 */
static void op6(const pred *pred1, const pred *pred2, clone *clone);

/** Transitivity.
 * The operation takes two predicates of arity 2:
 *      resp(x1, x0) = ∃x (pred1(x,x1) ∧ pred2(x,x0))
 */
static void op_trans(const pred *pred1, const pred *pred2, clone *clone);


#endif
