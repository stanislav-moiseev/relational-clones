/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef FUNC_H
#define FUNC_H

#include "utils.h"
#include "pred.h"

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

/** `fun_compute` computes the value of the function on the given
 * list of arguments.
 * `args` should have size == `fun->arity`.
 */
uint32_t fun_compute(const fun *fun, uint32_t args[]);

void fun_set_zero(fun *fun, uint32_t arity);

void fun_set_val(fun *fun, uint64_t xs, uint64_t y);

char *fun_print(const fun *fun);

#endif
