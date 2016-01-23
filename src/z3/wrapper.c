/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "z3/wrapper.h"

#include <z3.h>

void z3_wrapper_init(z3_wrapper *z3) {
  /* init ctx */
  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");
  z3->ctx = Z3_mk_context(cfg);

  /* init error handling */
  Z3_set_error_handler(z3->ctx, z3_error_handler);

  /* init solver */
  z3->solver = Z3_mk_solver(z3->ctx);
  Z3_solver_inc_ref(z3->ctx, z3->solver);

  Z3_del_config(cfg);

  z3->Ek_consts = NULL;
}

void z3_wrapper_free(z3_wrapper *z3) {
  Z3_solver_dec_ref(z3->ctx, z3->solver);
  Z3_del_context(z3->ctx);
  free(z3->Ek_consts);
}


/**
   \brief Check whether the logical context is satisfiable. If the context is
   satisfiable, then display the model.
*/
void z3_wrapper_check(z3_wrapper *z3) {
  Z3_model m      = 0;
  Z3_lbool result = Z3_solver_check(z3->ctx, z3->solver);
  switch (result) {
  case Z3_L_FALSE:
    printf("unsat\n");
    break;
  case Z3_L_UNDEF:
    printf("unknown\n");
    m = Z3_solver_get_model(z3->ctx, z3->solver);
    if (m) Z3_model_inc_ref(z3->ctx, m);
    printf("potential model:\n%s\n", Z3_model_to_string(z3->ctx, m));
    break;
  case Z3_L_TRUE:
    //printf("sat\n");
    m = Z3_solver_get_model(z3->ctx, z3->solver);
    if (m) Z3_model_inc_ref(z3->ctx, m);
    printf("sat\n%s\n", Z3_model_to_string(z3->ctx, m));
    break;
  }
  if (m) Z3_model_dec_ref(z3->ctx, m);
}

