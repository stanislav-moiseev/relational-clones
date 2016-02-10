/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Closure operator for predicates of arity <= 2.
 ******************************************************************************/

#ifndef CLOSURE_TWO_PREDS_H
#define CLOSURE_TWO_PREDS_H

#include <stdint.h>
#include <stdio.h>

#include "closure.h"
#include "pred-essential.h"

/** Closure operator that uses a precomputed table of closure of pairs of
 * predicates to efficiently compute the closure of the given clone.
 *
 * For a pair of predicates p1, p2 it returns the closure of the set
 *      { false(0), true(0), eq(2), p1, p2 }
 */
closure_operator *clop_two_preds_read(const char *fname);

#endif
