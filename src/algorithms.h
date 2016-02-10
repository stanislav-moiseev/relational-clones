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

/******************************************************************************/
/** Lattice of all clones in P3(2) */

/** The main algorithm.
 * Construct the lattice P3(2) of predicates of arity <= 2.
 */
void latice_construct(const closure_operator *clop, lattice *lt);

#endif
