/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ISAR_GEN_SPEC_H
#define ISAR_GEN_SPEC_H

#include "pred.h"
#include "clone.h"

/**
 * `isar_preds` writes specification of all 512 predicates of arity 2 in
 * 3-valued logic.
 *
 *
 * theory preds
 * imports Main
 * begin
 * 
 * datatype dom3 = V0 | V1 | V2
 * type_synonym pred2 = "dom3 \<Rightarrow> dom3 \<Rightarrow> bool"
 * 
 * (* p0 = {} *)
 * fun p0 :: "pred2" where
 *   "p0 V0 V0 = False"
 * | "p0 V0 V1 = False"
 * | "p0 V0 V2 = False"
 * | "p0 V1 V0 = False"
 * | "p0 V1 V1 = False"
 * | "p0 V1 V2 = False"
 * | "p0 V2 V0 = False"
 * | "p0 V2 V1 = False"
 * | "p0 V2 V2 = False"
 * 
 */
void isar_preds(FILE *fd);


/**
 * `isar_pred_operations` writes statements specifying about operations over
 * predicates, each statement being of the form
 *
 *      op_perm(p1)     == p2
 *      op_conj(p1, p2) == p3
 *      op_comp(p1, p2) == p3
 */
void isar_pred_operations(FILE *fd);

#endif
