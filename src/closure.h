/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Abstract closure operator for predicates of arity <= 2.
 ******************************************************************************/

#ifndef CLOSURE_H
#define CLOSURE_H

#include <stdint.h>
#include <stdio.h>

#include "utils.h"
#include "fun.h"
#include "pred.h"
#include "clone.h"

/******************************************************************************/
/** Abstract closure operator */

struct closure_operator_ops {
  /** `clone_closure_ex` computes the closure of the union <base ∪ suppl>
   * under an assumption that `base` is a closed set.
   */
  void (*closure_clone_ex)(void *internals, const clone *base, const clone *suppl, clone *closure);

  /** Virtual destructor for internal data. */
  void (*internals_free)(void *internals);
};

/** Abstract closure operator. */
struct closure_operator {
  struct closure_operator_ops ops;
  void *internals;
};
typedef struct closure_operator closure_operator;


static inline void clop_free(closure_operator *clop) {
  clop->ops.internals_free(clop->internals);
  free(clop);
}

static inline void closure_clone_ex(const closure_operator *clop, const clone *base, const clone *suppl, clone *closure) {
  clop->ops.closure_clone_ex(clop->internals, base, suppl, closure);
}



/******************************************************************************/
/** Common usages of closure operator */

/** `top_clone` returns a clone equal to {false(0), true(0), eq(2)}.
 */
const clone *top_clone();


void closure_clone(const closure_operator *clop, const clone *clone, struct clone *closure);


#endif

