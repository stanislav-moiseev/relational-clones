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

