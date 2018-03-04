/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 *
 * This module implements an extended version of the closure operator
 * for predicates of arity = 2 that keeps track of the operations
 * applied to predicates and produces beautiful formulas for new
 * predicates in the closure.
 ******************************************************************************/

#ifndef CLOSURE2_TRACE_H
#define CLOSURE2_TRACE_H

#include <stdint.h>
#include <stdio.h>

#include "closure2-straightforward.h"

/* A predicates descriptor used for formula atoms. */
typedef struct {
  pred pred;
  char *name;
} pred_descr_t;


typedef enum {
  FN_ATOM, FN_PERM, FN_CONJ, FN_COMP
} formula_node_type_t;


struct formula {
  /* A tag showing how to interpret the formula head. */
  formula_node_type_t head_type;

  /* Depending on the `head_type`, we will use different arguments. */
  union {
    struct {
      pred_descr_t descr;
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

/** `formula_eval` returns the predicate defined by the formula `phi`.
 */
pred formula_eval(const formula_t *phi);


/** Traces of predicates and formulas that they define. */
typedef struct {
  pred pred;
  formula_t formula;
} trace_entry_t;

typedef struct {
  trace_entry_t *entries;
  size_t num_entries;
  size_t capacity;
} closure_trace_t;


closure_trace_t *closure_trace_alloc();

void closure_trace_free(closure_trace_t *trace);

void closure_trace_insert(closure_trace_t *trace, const trace_entry_t *entry);


/** `closure2_trace` computes the closure of the given predicates
 * ("base predicates") and returns the list of all predicates with the
 * information of how they have been constructed from (i.e. a trace).
 * The base predicates are also included to the trace.
 *
 * The function returns a pointer to a newly constructed object; the
 * memory should be freed by `closure_trace_free()` after the object
 * is no longer need.
 *
 * If `closure` is non-NULL, the function will copy the resulting set
 * of predicates to `closure`.
 */
closure_trace_t *closure2_trace(const pred_descr_t *preds, size_t sz, struct clone *closure);


/** `print_formula_func_form` returns a pointer to a string
 * representation of the formula in the functional form, e.g.
 *
 *      conj(comp(p1, p2), perm(p3)),
 *
 * where `p1`, `p2`, `p3` are predicate names.
 *
 * The pointer should be freed to release memory when it is no longer
 * needed.
 */
char *print_formula_func_form(const formula_t *phi);


#endif

