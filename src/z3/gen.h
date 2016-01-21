/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef Z3_GEN_H
#define Z3_GEN_H

#include "pred.h"
#include "class.h"

/** A predicate of a functional symbol,
 * given by its name and arity.
 */
struct token {
  char *name;
  int arity;
};
typedef struct token token;


/**
 * For k==3 prints:
 *      (declare-datatypes () ((E3 V0 V1 V2 )))
 */ 
void gen_header(FILE *fd, int k);

/**
 * For k==3 and predicate p1^(2) prints:
 *      (declare-fun p1 (E3 E3 ) Bool)
 *      (assert (= (p1 V0 V0) ))
 *      (assert (= (p1 V1 V0) ))
 *      (assert (= (p1 V2 V0) ))
 *      (assert (= (p1 V0 V1) ))
 *      (assert (= (p1 V1 V1) ))
 *      (assert (= (p1 V2 V1) ))
 *      (assert (= (p1 V0 V2) ))
 *      (assert (= (p1 V1 V2) ))
 *      (assert (= (p1 V2 V2) ))
 *
 * Note that the values of the predicate of the particular input are /not/
 * printed.
 */
void gen_pred(FILE *fd, int k, const token *tk, const pred *pred);

/**
 * For k==3 and function f^(2) prints:
 *      (declare-fun f (E3 E3 ) E3)
 */
void gen_fun(FILE *fd, int k, const token *f);

/**
 * For a predicate and a function, `gen_preserve` prints
 * an assertion that the function preserves the predicate, e.g.:
 *
 *      (assert (forall ((x0_0 E3) (x0_1 E3) (x1_0 E3) (x1_1 E3) )
 *      		(implies (and (p1 x0_0 x0_1)(p1 x1_0 x1_1)) (and (p1 (f x0_0 x1_0) (f x0_1 x1_1))))))
 *
 * If `if_not` is non-zero, then `gen_preserve` prints
 * an assertion that the function /does not/ preserve the predicate, e.g.:
 *
 *      (assert (not (forall ((x0_0 E3) (x0_1 E3) (x1_0 E3) (x1_1 E3) )
 *      		(implies (and (p x0_0 x0_1)(p x1_0 x1_1)) (and (p (f x0_0 x1_0) (f x0_1 x1_1)))))))
 */
void gen_preserve(FILE *fd, int if_not, int k, const token *pred, const token *fun);


/** `gen_assert_discr_fun` write an assertion for Z#Solver that 
 * there exists a function `f` of arity `fun_arity` such that
 *   1) f preserves all the basis predicates from `class`;
 *   2) f does not preserve the predicate `pred`.
 */
void gen_assert_discr_fun(FILE *fd, const class *class, const pred *pred, int fun_arity);

#endif
