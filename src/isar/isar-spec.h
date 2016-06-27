/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ISAR_SPEC_H
#define ISAR_SPEC_H

#include "pred.h"
#include "clone.h"

/**
 * `isar_clones` writes specification of all 2079040 relational clones of
 * degree <= 2 of in 3-valued logic.
 */
void isar_clones(const char *ccplt_fname, FILE *fd, const char *theory_name);


/**
 * `isar_preds` writes specification of all 512 predicates of arity 2 in
 * 3-valued logic.
 *
 * theory preds
 * imports common
 * begin
 * 
 * (* P311 = {22, 12, 11, 02, 01, 00}    -- linear order (0 < 1 < 2) *)
 * fun P311 :: "pred2" where
 *   "P311 V0 V0 = True"
 * | "P311 V0 V1 = True"
 * | "P311 V0 V2 = True"
 * | "P311 V1 V0 = False"
 * | "P311 V1 V1 = True"
 * | "P311 V1 V2 = True"
 * | "P311 V2 V0 = False"
 * | "P311 V2 V1 = False"
 * | "P311 V2 V2 = True"
 * 
 */
void isar_preds(FILE *fd, const char *theory_name);


/**
 * `isar_pred_ops_perm` writes statements about application of permutation
 * operation to all 512 predicates.
 *
 * theory ops_perm
 * imports common preds
 * begin
 *
 * lemma op_perm_P042: "op_perm P042 = P138"
 * proof (simp add: fun_eq_iff; intro allI)
 *   show "\<And>x1 x2. (op_perm P042) x1 x2 = P138 x1 x2"
 *   by (induct_tac x1 rule: dom3.induct;
 *       induct_tac x2 rule: dom3.induct;
 *       simp add: op_perm_def)
 * qed
 */
void isar_pred_ops_perm(FILE *fd, const char *theory_name);


/**
 * `isar_pred_ops_conj` writes statements about application of conjunction
 * operation to all 512*512 pairs of predicates.
 *
 * theory ops_conj
 * imports common preds
 * begin
 * 
 * lemma op_conj_P111_P222: "op_conj P111 P222 = P078"
 * proof (simp add: fun_eq_iff; intro allI)
 *   show "\<And>x1 x2. (op_conj P111 P222) x1 x2 = P078 x1 x2"
 *   by (induct_tac x1 rule: dom3.induct;
 *       induct_tac x2 rule: dom3.induct;
 *       simp add: op_conj_def)
 * qed
 */
void isar_pred_ops_conj(FILE *fd, const char *theory_name);


/**
 * `isar_pred_ops_conj2` is same to `isar_pred_ops_conj2` but it writes
 * one big formula specifying the conjunction operation.
 *
 * lemma "op_conj P000 P000 = P000 \<and>
 *        op_conj P000 P001 = P000 \<and>
 *        <...>
 *        op_conj P511 P509 = P509 \<and>
 *        op_conj P511 P510 = P510 \<and>
 *        op_conj P511 P511 = P511"
 */
void isar_pred_ops_conj2(FILE *fd, const char *theory_name);


/**
 * `isar_pred_ops_comp` writes statements about application of composition
 * operation to all 512*512 pairs of predicates.
 */
void isar_pred_ops_comp(FILE *fd, const char *theory_name);


#endif
