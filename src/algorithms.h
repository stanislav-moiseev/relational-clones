/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * @brief       Algorithms to construct lattice of all clones in P3(2).
 ******************************************************************************/

#ifndef ALGORITHMS_ALG_CONSTRUCT_LATTICE_H
#define ALGORITHMS_ALG_CONSTRUCT_LATTICE_H

#include "maj-lattice.h"
#include "lattice.h"
#include "closure.h"
#include "z3/z3-search.h"

/******************************************************************************/
/** Lattice of all clones containing a majority operation */

void find_classes_with_one_subclass(const maj_lattice *lattice, maj_class ***classes, uint64_t *num_classes);

/** `find_discr_function` searches for a function `fun` of arity <= max_fun_arity,
 * such that `fun` preserves the `class1` and does not preserve the `class2`.
 *
 * On success (rc==Z3_L_TRUE), the discriminating function of the smallest arity
 * will be stored to `fun`.
 */
Z3_lbool find_discr_function(const maj_class *class1, const maj_class *class2, int max_fun_arity, fun *fun);

/** `clone_contains_majority` returns true if there is at least one minimal
 * majority operation `maj` such that `maj` preserves all the predicates from
 * `clone`.
 */
int clone_contains_majority(const clone *cl);

/* `pred_preserves_majority` return true if there is a minimal majority
 * operation preserving the predicate */
int pred_preserves_majority(const pred *p);

/******************************************************************************/
/** Lattice of all clones in P3(2) */

/** `closure_uniq_ess_preds` returns a clone contain all closure-unique
 * essential predicates of arity <= 2 except predicates that are equivalient
 * to dummy clone {false(0), true(1), eq(2)}.
 *
 * Two essential predicates p1 and p2 are called /closure-equivalent/
 * if <false(0), true(1), eq(2), p1}> == <false(0), true(1), eq(2), p2}>.
 */
void closure_uniq_ess_preds(clone *cl);

void construct_uniq_ess_preds(pred **uniq_preds, size_t *uniq_sz);

void latice_construct(const closure_operator *clop, lattice *lt);

#endif
