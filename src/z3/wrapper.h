/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef Z3_WRAPPER_H
#define Z3_WRAPPER_H

#include <z3.h>

struct z3_wrapper {
  Z3_context ctx;
  Z3_solver solver;
  
  Z3_sort Ek_sort;
  Z3_ast *Ek_consts;

  Z3_func_decl fun;
};
typedef struct z3_wrapper z3_wrapper;

/** Simpler error handler.
 */
static void z3_error_handler(Z3_context c, Z3_error_code e)
{
  fprintf(stderr, "Z3 error: %d\n", e);
}

void z3_wrapper_init(z3_wrapper *z3);

void z3_wrapper_free(z3_wrapper *z3);

/** `z3_wrapper_check` checks whether the current logical context is
 * satisfiable.
 */
void z3_wrapper_check(z3_wrapper *z3);

#endif
