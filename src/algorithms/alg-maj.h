/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ALGORITHMS_ALG_MAJ_H
#define ALGORITHMS_ALG_MAJ_H

#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "binary/maj-lattice.h"
#include <z3.h>

void find_classes_with_one_subclass(const maj_lattice *lattice, maj_class ***classes, uint64_t *num_classes);

/** `find_discr_function` searches for a function `fun` of arity <= max_fun_arity,
 * such that `fun` preserves the `class1` and does not preserve the `class2`.
 *
 * On success (rc==Z3_L_TRUE), the discriminating function of the smallest arity
 * will be stored to `fun`.
 */
Z3_lbool find_discr_function(const maj_class *class1, const maj_class *class2, int max_fun_arity, fun *fun);

#endif
