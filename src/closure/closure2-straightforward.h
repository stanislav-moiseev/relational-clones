/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Closure operator for predicates of arity = 2.
 ******************************************************************************/

#ifndef CLOSURE2_H
#define CLOSURE2_H

#include <stdint.h>
#include <stdio.h>

#include "closure.h"

/******************************************************************************/
/** Elementary operations over predicates of arity 2.
 * The predicates are non necessary to be essential.
 *
 * The following functions compute the corresponding operations and add the
 * result to `clone`.
 */

/** Permutation of variables:
 *  (op_perm p) x1 x2 ≡ p x2 x1
 */
static void op_perm(const pred *p, clone *clone);

/** Conjunction of two predicates:
 *  (op_conj p1 p2) x1 x2 ≡ (p1 x1 x2 ∧ p2 x1 x2)
 */
static void op_conj(const pred *p1, const pred *p2, clone *clone);

/** General composition:
 *  (op_comp p1 p2) x1 x2 ≡ (∃y. p1 x1 y ∧ p2 y x2)
 */
static void op_comp(const pred *p1, const pred *p2, clone *clone);


/******************************************************************************/
/** Closure operator that computes elementary operation directly:
 *     - op_perm(1), op_conj(2), op_comp(2).
 */
closure_operator *clop2_alloc_straightforward();

#endif
