/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef FUN_H
#define FUN_H

#include "utils.h"
#include "pred.h"
#include "clone.h"

#define FUN_DATA_SIZE 8

struct fun {
  int64_t arity;
  uint64_t data[FUN_DATA_SIZE];
};

typedef struct fun fun;

/** `fun_consistent` returns non-zero if the internal structure of `fun` is
 * consistent. In particular, it checks that `struct fun` contains enough bits
 * to store all `int_pow(K, func->arity)` values of the function.
 */
int fun_consistent(const fun *fun);

/** `fun_hash` is a 32-bit hashing function for functions.
 */
uint32_t fun_hash(const void *fun);


/******************************************************************************/
/** printing and scanning */

/** `fun_print` returns a string contain the values of the function on all input
 * tuples.
 */
char *fun_print(const fun *fun);

/** `fun_print_verbosely` prints all input tuples for non-zero function value.
 */
void fun_print_verbosely(FILE *, const fun *fun);

/** `fun_scan` is the reverse function to `fun_print`.
 */
void fun_scan(const char *str, fun *fun);

/******************************************************************************/
/** basic operations */

/** `fun_init` initializes the function to be equal to zero.
 */
void fun_init(fun *fun, uint32_t arity);

/** `fun_set_val` sets the value of the function on the given tuple.
 */
void fun_set_val(fun *fun, uint64_t tuple, uint64_t val);

/** `fun_compute` computes the value of the function on the given
 * list of arguments.
 * `args` should have size == `fun->arity`.
 */
uint32_t fun_compute(const fun *fun, uint64_t tuple);

int fun_eq(const fun *f1, const fun *f2);

/******************************************************************************/
/** Mathematical properties */

/** `fun_preserves_pred` returns non-zero if the function preserves the
 * predicate.
 */
int fun_preserves_pred(const fun *fun, const pred *pred);

/** `fun_preserves_clone` returns true if the functions preserves every
 * predicate from the given clone.
 */
int fun_preserves_clone(const fun *fun, const clone *clone);

/** `test_discr_function` returns non-zero if the function preserves all
 * predicates from `clone1` and does not preserve at least one predicate from
 * `clone2`.
 */
static int test_discr_function(const clone *clone1, const clone *clone2, const fun *fun) {
  return fun_preserves_clone(fun, clone1) && !fun_preserves_clone(fun, clone2);
}


#endif
