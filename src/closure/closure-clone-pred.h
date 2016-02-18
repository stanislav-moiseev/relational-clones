/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Closure operator for predicates of arity <= 2.
 ******************************************************************************/

#ifndef CLOSURE_CLONE_PRED_H
#define CLOSURE_cLONE_PRED_H

#include <stdint.h>
#include <stdio.h>

#include "closure.h"
#include "algorithm/alg-closure-clone-pred.h"

/** Closure operator that uses a precomputed table of closure of a clone plus a
 * closure-unique essential predicate to efficiently compute the closure of the
 * given clone.
 */
closure_operator *clop_clone_pred_read(const char *fname);

/** `clop_clone_pred_alloc` initializes the clop with the given ccplt.
 * Note that the function does /not/ make a copy of ccplt, so ccplt will be
 * freed with calling to `clop_free`.
 */
closure_operator *clop_clone_pred_alloc(const ccplt *ccplt);

#endif
