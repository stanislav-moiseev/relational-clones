/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ALGORITHMS_ALG_MAJ_H
#define ALGORITHMS_ALG_MAJ_H

#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "closure.h"

/** `clone_closure_two_preds` computes the closure of
 *      { false(0), true(0), eq(2), p1, p2 }
 * and inserts the predicates obtained to `closure`.
 */
void clone_closure_two_preds(const pred *p1, const pred *p2, clone *closure);

#endif
