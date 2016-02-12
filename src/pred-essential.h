/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ESSENTIAL_PREDICATE_H
#define ESSENTIAL_PREDICATE_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"

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

/******************************************************************************/
/** Closure-unique essential predicates */

/** `closure_uniq_ess_preds` returns a clone contain all 251 closure-unique
 * essential predicates of arity <= 2.
 *
 * Two essential predicates p1 and p2 are called /closure-equivalent/
 * if <false(0), true(1), eq(2), p1}> == <false(0), true(1), eq(2), p2}>.
 */
void closure_uniq_ess_preds(clone *cl);

void construct_closure_uniq_ess_preds(pred **uniq_preds, size_t *uniq_sz);

#endif
