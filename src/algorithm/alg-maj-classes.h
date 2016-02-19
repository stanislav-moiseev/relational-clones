/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * @brief       Algorithms to construct lattice of all clones in R3(2).
 ******************************************************************************/

#ifndef ALG_MAJ_CLASSES_H
#define ALG_MAJ_CLASSES_H

#include "maj-lattice.h"
#include "z3/z3-search.h"

/******************************************************************************/
/** Lattice of all clones containing a majority operation */

void find_classes_with_one_subclass(const majlattice *lattice, majclass ***classes, uint64_t *num_classes);

/** `find_discr_function` searches for a function `fun` of arity <= max_fun_arity,
 * such that `fun` preserves the `class1` and does not preserve the `class2`.
 *
 * On success (rc==Z3_L_TRUE), the discriminating function of the smallest arity
 * will be stored to `fun`.
 */
Z3_lbool find_discr_function(const majclass *class1, const majclass *class2, int max_fun_arity, fun *fun);

#endif
