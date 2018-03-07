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
#include "closure2-formulas.h"


/** Traces of predicates and formulas that they define. */
typedef struct {
  /* The predicate represented by the `formula`. */
  pred pred;
  /* A formula representing the predicate `pred`. */
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
closure_trace_t *closure2_clone_traced(const struct clone *clone, struct clone *closure);


#endif

