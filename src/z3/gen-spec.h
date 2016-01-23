/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef Z3_GEN_SPEC_H
#define Z3_GEN_SPEC_H

#include "utils.h"
#include "pred.h"
#include "clone.h"
#include "clone-iterator.h"
#include "class.h"

#include "z3/wrapper.h"

void gen_assert_discr_fun_two_classes(z3_wrapper *z3, const class *class1, const class *class2, int fun_arity);

#endif
