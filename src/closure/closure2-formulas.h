/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 *
 * This module provides interfaces to deal with terms and primitive
 * positive formulas.
 ******************************************************************************/

#ifndef CLOSURE2_FORMULAS_H
#define CLOSURE2_FORMULAS_H

#include <stdint.h>
#include <stdio.h>

#include "pred.h"
#include "clone.h"

typedef enum {
  FN_ATOM, FN_PERM, FN_CONJ, FN_COMP
} term_node_type_t;


struct term {
  /* A tag showing how to interpret the term head. */
  term_node_type_t head_type;

  /* Depending on the `head_type`, we will use different arguments. */
  union {
    struct {
      struct pred pred;
    } atom;
    
    struct {
      const struct term *arg1;
    } perm;

    struct {
      const struct term *arg1;
      const struct term *arg2;
    } conj;
    
    struct {
      const struct term *arg1;
      const struct term *arg2;
    } comp;
  } head_data;
};
typedef struct term term_t;

typedef struct {
  pred pred;
  int arg1;
  int arg2;
} atom_t;

/** A data type representing primitive positive formulas, e.g.
 * ∃y1 ∃y2 (p283(x1,y1) ∧ p433(y1,x2) ∧ p433(x1,y2) ∧ p283(y2,x2));
 */
typedef struct {
  /* Number of bounded variables, i.e. number of variables under
   * existential quantifiers. */
  int num_bounded_vars;
  
  /* List of predicates and their arguments. 
   * Negative-valued arguments represent bounded variables. */
  atom_t *atoms;
  size_t num_atoms;
  size_t capacity;
} formula_t;


formula_t *formula_alloc();

void formula_free(formula_t *phi);

void formula_insert_atom(formula_t *phi, const atom_t *atom);

int formula_get_fresh_bounded_var(formula_t *phi);


/** `term_eval` returns the predicate defined by the term `tau`.
 *
 * This functions can be used to test the correctness of term
 * construction.
 */
pred term_eval(const term_t *tau);

/** `formula_eval` returns the predicate defined by the formula `phi`.
 *
 * This functions can be used to test the correctness of term
 * construction.
 */
pred formula_eval(const formula_t *phi);

/** `term_to_formula` returns a primitive-positive formula identical
 * to the term `tau`. */
formula_t *term_to_formula(const term_t *tau);



/** A naming functions for predicates and variables used when printing
 * terms and formulas.
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


/** `print_term` returns a pointer to a string representation of the
 * term in the functional form, e.g.
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
char *term_print(const term_t *tau, pred_naming_fn_t pred_naming_fn);


/** `print_formula` returns a pointer to a string representation of
 * a quantified formula, e.g.
 *
 * ∃y1 ∃y2 (p283(x1,y1) ∧ p433(y1,x2) ∧ p433(x1,y2) ∧ p283(y2,x2));
 *
 * The function uses predicate and variable naming functions to print
 * their names. The exists (∃) and conjunction (∧) symbols are printed
 * in LaTeX format.
 *                                        
 * The pointer should be freed to release memory when it is no longer
 * needed.
 */
char *formula_print_latex(const formula_t *phi, pred_naming_fn_t pred_naming_fn, var_naming_fn_t var_naming_fn);


/* Naming functions for predicates, variables, and clones that use
 * LaTeX output format.
 */
const char *pred_naming_fn_latex(pred p);

const char *var_naming_fn_latex(int var);

const char *clone_naming_fn_latex(const struct clone *clone);

#endif
