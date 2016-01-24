/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef Z3_GEN_SPEC_H
#define Z3_GEN_SPEC_H

#include "utils.h"
#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "clone-iterator.h"
#include "class.h"

#include "z3/wrapper.h"

void gen_assert_discr_fun_two_classes(z3_wrapper *z3, const class *class1, const class *class2, int fun_arity);


/** `z3_find_function` invokes Z3 solver to search for a function of arity
 * `fun_arity` discriminating two classes in the following sense:
 * `fun` preserves `class1`, but does not preserve `class2`.
 *
 * On success, it writes the result to `fun`.
 */
Z3_lbool z3_find_discr_function(const class *class1, const class *class2, uint32_t fun_arity, fun *fun);

#endif
