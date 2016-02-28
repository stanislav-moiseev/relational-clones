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
 
/** `z3_find_discr_function` invokes Z3 solver to search for a function of
 * arity <= max_fun_arity discriminating two clones in the following sense:
 *   - `fun` preserves all predicates from `clone1_basis`,
 *   - but `fun` does not preserve some predicate from `clone2 \ clone1`.
 *
 * In current implementation, the procedure heuristically selects one predicate `p`
 * from `clone2 \ clone1`, and then searches for a function that preserves
 * `clone1_bases` and does not preserve the selected predicate `p`.
 *
 * Possible return values:
 *   - Z3_L_TRUE:       A discriminating function has been found successfully.
 *                      In this case, the discriminating function of the smallest
 *                      arity is written to `fun`.
 *   - Z3_L_FALSE:      I has been proven that the discriminating function
 *                      does not exist.
 *   - Z3_L_UNDEF:      The result is unknown (Z3 was unable to crack the problem).
 */
Z3_lbool z3_find_discr_function(const clone *clone1_basis,
                                const clone *clone1,
                                const clone *clone2,
                                int max_fun_arity,
                                fun *fun);

Z3_lbool z3_find_one_discr_function(const clone *clone1_basis,
                                    const clone *clone1,
                                    const clone *clone2,
                                    uint32_t fun_arity,
                                    fun *fun);

#endif
