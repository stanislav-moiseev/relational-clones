/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ESSENTIAL_PREDICATE_H
#define ESSENTIAL_PREDICATE_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"
#include "closure.h"


/******************************************************************************/
/** Essential predicates */

/** `pred_is_essential` returns non-zero if the predicate is an essential Zhuk
 *  predicate.
 */
int pred_is_essential(const pred *pred);

/** `all_essential_predicates` returns a clone containing the set of all
 * essential predicates of arity <= max_arity.
 */
void get_essential_predicates(uint32_t max_arity, pred **ess_preds, size_t *size);

/** `essential_predicates` writes all essential predicates of arity <= max_arity
 * to `cl`.
 */
void essential_predicates(uint32_t max_arity, clone *cl);

/******************************************************************************/
/** Closure-unique essential predicates */


/** `closure_one_pred` computes the closure of
 *      { false(0), true(0), eq(2), p }
 * and write the result to `closure`.
 */
void closure_one_pred(const closure_operator *clop, const pred *p, clone *closure);

/** `closure_uniq_ess_preds` returns a clone contain all 251 closure-unique
 * essential predicates of arity <= max_arity.
 *
 * Two essential predicates p1 and p2 are called /closure-equivalent/
 * if <{false(0), true(0), eq(2), p1}> == <{false(0), true(0), eq(2), p2}>.
 */
void closure_uniq_ess_preds(uint32_t max_arity, clone *cl);

void construct_closure_uniq_ess_preds(uint32_t max_arity, pred **uniq_preds, size_t *uniq_sz);

#endif
