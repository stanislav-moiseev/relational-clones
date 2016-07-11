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
pred op_perm2(const pred *p);

/** Conjunction of two predicates:
 *  (op_conj p1 p2) x1 x2 ≡ (p1 x1 x2 ∧ p2 x1 x2)
 */
pred op_conj2(const pred *p1, const pred *p2);

/** General composition:
 *  (op_comp p1 p2) x1 x2 ≡ (∃y. p1 x1 y ∧ p2 y x2)
 */
pred op_comp2(const pred *p1, const pred *p2);


/******************************************************************************/
/** Closure operator that computes elementary operation directly:
 *     - op_perm(1), op_conj(2), op_comp(2).
 */
closure_operator *clop2_alloc_straightforward();

#endif

