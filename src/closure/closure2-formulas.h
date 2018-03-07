/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 *
 * This module implements an extended version of the closure operator
 * for predicates of arity = 2 that keeps track of the operations
 * applied to predicates and produces beautiful formulas for new
 * predicates in the closure.
 ******************************************************************************/

#ifndef CLOSURE2_FORMULAS_H
#define CLOSURE2_FORMULAS_H

#include <stdint.h>
#include <stdio.h>

#include "closure/closure2-straightforward.h"
#include "pred.h"
#include "clone.h"

typedef enum {
  FN_ATOM, FN_PERM, FN_CONJ, FN_COMP
} formula_node_type_t;


struct formula {
  /* A tag showing how to interpret the formula head. */
  formula_node_type_t head_type;

  /* Depending on the `head_type`, we will use different arguments. */
  union {
    struct {
      struct pred pred;
    } atom;
    
    struct {
      const struct formula *arg1;
    } perm;

    struct {
      const struct formula *arg1;
      const struct formula *arg2;
    } conj;
    
    struct {
      const struct formula *arg1;
      const struct formula *arg2;
    } comp;
  } head_data;
};

typedef struct formula formula_t;

/** A naming functions for predicates and variables used when printing
 * formulas.
 *
 * Note. The pointer return by these functions will /not/ be freed;
 *       it is assumed that functions return a pointer to a statically
 *       allocated memory region.
 */
typedef const char *(*pred_naming_fn_t) (struct pred);

/** The `int var` argument of the function is interpreted in the following way:
 *   - if var > 0, then `var` is an unbounded variable;
 *   - if var < 0, then `var` is a bounded variable.
 */
typedef const char *(*var_naming_fn_t) (int);


/** `formula_eval` returns the predicate defined by the formula `phi`.
 *
 * This functions can be used to test the correctness of formula
 * construction.
 */
pred formula_eval(const formula_t *phi);


/** `print_formula_func_form` returns a pointer to a string
 * representation of the formula in the functional form, e.g.
 *
 *      conj(comp(p1, p2), perm(p3))
 *
 * where `p1`, `p2`, `p3` are predicate names.
 * 
 * The function uses `pred_naming_fn` to print predicates' names.
 *
 * The pointer should be freed to release memory when it is no longer
 * needed.
 */
char *print_formula_func_form(const formula_t *phi, pred_naming_fn_t pred_naming_fn);

/** `print_formula_quantified_form` returns a pointer to a string
 * representation of the formula in the quantified form, e.g.
 *
 * ∃y1 ∃y2 (p283(x1,y1) ∧ p433(y1,x2) ∧ p433(x1,y2) ∧ p283(y2,x2));
 *
 * The function prints the formula in LaTeX format:
 *
 * \exists y_{1}\, \exists y_{2}\,
 *      \bigl( p_{439}(x_{1},y_{2}) \wedge p_{275}(y_{2},y_{1}) \wedge
 *             p_{439}(x_{1},y_{1}) \wedge p_{275}(y_{1},x_{2}) \bigr)
 *
 * The function uses predicate and variable naming functions to print
 * their names.
 *                                        
 * The pointer should be freed to release memory when it is no longer
 * needed.
 */
char *print_formula_quantified_form(const formula_t *phi, pred_naming_fn_t pred_naming_fn, var_naming_fn_t var_naming_fn);


/* Naming functions for predicates, variables, and clones that use
 * LaTeX output format.
 */
const char *pred_naming_fn(pred p);

const char *var_naming_fn(int var);

const char *clone_naming_fn(const struct clone *clone);

#endif
