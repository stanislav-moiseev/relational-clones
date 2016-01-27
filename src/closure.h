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
#include "pred.h"
#include "clone.h"
#include "clone-iterator.h"

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

#endif
