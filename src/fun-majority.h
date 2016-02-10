/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef FUN_MAJORITY_H
#define FUN_MAJORITY_H

#include "pred.h"
#include "fun.h"
#include "clone.h"

/** `min_majorities` returns the list of all 7 minimal majority functions
 * in P3.
 * The pointer should be freed to release the memory.
 */
void min_majorities(fun **majs, size_t *size);

/** `clone_contains_majority` returns true if there is at least one minimal
 * majority operation `maj` such that `maj` preserves all the predicates from
 * `clone`.
 */
int clone_contains_majority(const clone *cl);

/* `pred_preserves_majority` return true if there is a minimal majority
 * operation preserving the predicate */
int pred_preserves_majority(const pred *p);

#endif
