/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ALGORITHMS_H
#define ALGORITHMS_H

#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "class.h"
#include "lattice.h"
#include <z3.h>

void find_classes_with_one_subclass(const lattice *lattice, class ***classes, uint64_t *num_classes);

/** `find_discr_function` searches for a function `fun` of arity <= max_fun_arity,
 * such that `fun` preserves the `class1` and does not preserve the `class2`.
 *
 * On success (rc==Z3_L_TRUE), the discriminating function of the smallest arity
 * will be stored to `fun`.
 */
Z3_lbool find_discr_function(const class *class1, const class *class2, int max_fun_arity, fun *fun);

void write_classes_with_one_subclass_discr_fun(FILE *fd, const lattice *lattice, class * const *classes, size_t num_classes, const fun *fun);

void read_classes_with_one_subclass_discr_fun(FILE *fd, const lattice *lattice, class ***classes, size_t *num_classes, fun **funs);

#endif