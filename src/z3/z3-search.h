/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/
 
#ifndef Z3_SEARCH_H
#define Z3_SEARCH_H
 
#include "utils.h"
#include "fun.h"
#include "pred.h"
#include "clone.h"

#include <z3.h>
 
/** `z3_find_discr_function` invokes Z3 solver to search for a function of arity
 * `fun_arity` discriminating two clones in the following sense:
 *   1) `fun` preserves all predicates from `clone1`,
 *   2) but `fun` does not preserve some predicate from `clone2`.
 *
 * The predicate from `clone2` that the function should not preserve is selected
 * in an unspecified manner.
 *
 * On success, it writes the result to `fun`.
 */

Z3_lbool z3_find_discr_function(const clone *clone1_basis, const clone *clone1, const clone *clone2, uint32_t fun_arity, fun *fun);
 
#endif
