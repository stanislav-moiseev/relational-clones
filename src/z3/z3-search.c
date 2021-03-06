/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "fun.h"
#include "z3/z3-search.h"

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


void gen_header(z3_wrapper *z3) {
  char Ek_name[8];
  sprintf(Ek_name, "E%d", K);
  Z3_symbol Ek_sym = Z3_mk_string_symbol(z3->ctx, Ek_name);

  Z3_constructor Ek_constructors[K];
  Z3_symbol Ek_syms[K];
  for(size_t i = 0; i < K; ++i) {
    char Ek_sym_name[8];
    sprintf(Ek_sym_name, "V%ld", i);
    Ek_syms[i] = Z3_mk_string_symbol(z3->ctx, Ek_sym_name);

    char Vk_recognizer_name[16];
    sprintf(Vk_recognizer_name, "is_V%ld", i);
    Z3_symbol Ek_sym_recognizer = Z3_mk_string_symbol(z3->ctx, Vk_recognizer_name);

    Ek_constructors[i] = Z3_mk_constructor(z3->ctx, Ek_syms[i], Ek_sym_recognizer, 0, 0, 0, 0);
  }

  z3->Ek_consts = malloc(K * sizeof(Z3_ast));

  z3->Ek_sort = Z3_mk_datatype(z3->ctx, Ek_sym, K, Ek_constructors);
  
  for(size_t i = 0; i < K; ++i) {
    Z3_func_decl decl;
    Z3_query_constructor(z3->ctx, Ek_constructors[i], 0, &decl, NULL, 0);
    z3->Ek_consts[i] = Z3_mk_app(z3->ctx, decl, 0, 0);
  }

  /* TODO: experiment more with finite domain sort. */
  /* z3->Ek_sort = Z3_mk_finite_domain_sort(z3->ctx, Ek_sym, K); */

  /* for(size_t i = 0; i < K; ++i) { */
  /*   z3->Ek_consts[i] = Z3_mk_int(z3->ctx, i, z3->Ek_sort); */
  /* } */
}

/* (declare-fun p_name (E3 E3 ...) Bool) */
Z3_func_decl gen_pred(z3_wrapper *z3, const char *name, const pred *pred) {
  Z3_symbol symb = Z3_mk_string_symbol(z3->ctx, name);
  Z3_sort domain[pred->arity];
  for(size_t i = 0; i < pred->arity; ++i) {
      domain[i] = z3->Ek_sort;
  }
  Z3_sort range = Z3_mk_bool_sort(z3->ctx);
  Z3_func_decl p = Z3_mk_func_decl(z3->ctx, symb, pred->arity, domain, range);
  
  /* create assertions */
  for(size_t xs = 0; xs < int_pow(K, pred->arity); ++xs) {
    /* represent `xs` in the K-ary form,
     * with digits[0] being the highest digit. */
    uint32_t digits[pred->arity];
    get_K_digits(digits, pred->arity, xs);
    
    Z3_ast args[pred->arity];
    for(size_t i = 0; i < pred->arity; ++i) {
      args[i] = z3->Ek_consts[digits[i]];
    }
    Z3_ast phi = Z3_mk_app(z3->ctx, p, pred->arity, args);

    /* if the predicate equals to false on `xs` */
    if(!pred_compute(pred, xs)) {
      phi = Z3_mk_not(z3->ctx, phi);
    }

    /* printf("\n%s\n", Z3_ast_to_string(z3->ctx, phi)); */
    Z3_solver_assert(z3->ctx, z3->solver, phi);
  }

  return p;
}

/* (declare-fun f (E3 E3 E3 ...) E3) */
Z3_func_decl gen_fun(z3_wrapper *z3, const char *name, uint32_t arity) {
  Z3_symbol symb = Z3_mk_string_symbol(z3->ctx, name);
  Z3_sort domain[arity];
  for(size_t i = 0; i < arity; ++i) {
    domain[i] = z3->Ek_sort;
  }
  Z3_sort range = z3->Ek_sort;
  return Z3_mk_func_decl(z3->ctx, symb, arity, domain, range);
}

void gen_preserve(z3_wrapper *z3, int not_preserve, Z3_func_decl fun, uint32_t fun_arity, Z3_func_decl pred, uint32_t pred_arity) {
  /* create bound variables */
  Z3_ast bound_vars[fun_arity][pred_arity];
  size_t idx = fun_arity * pred_arity - 1;
  for(int i = 0; i < fun_arity; ++i) {
    for(int j = 0; j < pred_arity; ++j) {
      bound_vars[i][j] = Z3_mk_bound(z3->ctx, idx, z3->Ek_sort);
      --idx;
    }
  }

  /* create left-hand side of implication */
  Z3_ast t1;
  if(fun_arity == 0) {
    t1 = Z3_mk_true(z3->ctx);
  } else { /* fun_arity >= 1*/
    Z3_ast and_args[fun_arity];
    for(int i = 0; i < fun_arity; ++i) {
      Z3_ast pred_args[pred_arity];
      for(int j = 0; j < pred_arity; ++j) {
        pred_args[j] = bound_vars[i][j];
      }
      and_args[i] = Z3_mk_app(z3->ctx, pred, pred_arity, pred_args);
    }
    t1 = Z3_mk_and(z3->ctx, fun_arity, and_args);
  }
  
  /* create right-hand side of implication */
  Z3_ast pred_args[pred_arity];
  for(int j = 0; j < pred_arity; ++j) {
    Z3_ast fun_args[fun_arity];
    for(int i = 0; i < fun_arity; ++i) {
      fun_args[i] = bound_vars[i][j];
    }
    pred_args[j] = Z3_mk_app(z3->ctx, fun, fun_arity, fun_args);
  }
  Z3_ast t2 = Z3_mk_app(z3->ctx, pred, pred_arity, pred_args);

  /* create implication */
  Z3_ast body = Z3_mk_implies(z3->ctx, t1, t2);

  /* create quantified formula phi */
  size_t num_decls = fun_arity * pred_arity;
  Z3_sort sorts[num_decls];
  for(int i = 0; i < num_decls; ++i) {
    sorts[i] = z3->Ek_sort;
  }
  Z3_symbol decl_names[num_decls];
  idx = fun_arity * pred_arity - 1;
  for(int i = 0; i < fun_arity; ++i) {
    for(int j = 0; j < pred_arity; ++j) {
      char s[16];
      sprintf(s, "x%d_%d ", i, j);
      decl_names[idx] = Z3_mk_string_symbol(z3->ctx, s);
      --idx;
    }
  }
  Z3_ast phi = Z3_mk_forall(z3->ctx, 0, 0, NULL, num_decls, sorts, decl_names, body);

  if(not_preserve) {
    phi = Z3_mk_not(z3->ctx, phi);
  }

  /* printf("\n%s\n", Z3_ast_to_string(z3->ctx, phi)); */
  Z3_solver_assert(z3->ctx, z3->solver, phi);
}

void gen_assert_discr_fun(z3_wrapper *z3, const clone *clone, const pred *pred, int fun_arity) {
  gen_header(z3);

  /* the basis of the clone */
  struct pred *pred_list;
  uint64_t num_preds;
  clone_get_predicates(clone, &pred_list, &num_preds);

  /* write a definition for all predicates */
  Z3_func_decl preds[num_preds];
  for(int i = 0; i < num_preds; ++i) {
    char name[8];
    sprintf(name, "p%d", i);
    preds[i] = gen_pred(z3, name, &pred_list[i]);
  }

  Z3_func_decl p = gen_pred(z3, "p", pred);

  /* declare a discriminating function */
  Z3_func_decl f = gen_fun(z3, "f", fun_arity);
  z3->fun = f;

  /* write assertions about function preservation */
  for(int i = 0; i < num_preds; ++i) {
    gen_preserve(z3, 0, f, fun_arity, preds[i], pred_list[i].arity);
  }
  gen_preserve(z3, 1, f, fun_arity, p, pred->arity);

  free(pred_list);
}

void gen_assert_discr_fun_two_clones(z3_wrapper *z3, const clone *clone1_basis, const clone *clone1, const clone *clone2, int fun_arity) {
  /* select any predicate discriminating two clones */
  clone diff;
  clone_diff(clone2, clone1, &diff);
  assert(!clone_is_empty(&diff));

  /* heuristically, find a predicate from `diff` with the smallest extensional
   * size */
  uint64_t min_card = -1;
  pred min_pred;
  for(clone_iterator it = clone_iterator_begin(&diff); !clone_iterator_end(&diff, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    int64_t card = pred_cardinality(&pred);
    if(card < min_card) {
      min_card = card;
      min_pred = pred;
    }
  }
  gen_assert_discr_fun(z3, clone1_basis, &min_pred, fun_arity);
}

void get_function(z3_wrapper *z3, Z3_func_decl fun, uint32_t fun_arity, struct fun *kfun) {
  Z3_model m = Z3_solver_get_model(z3->ctx, z3->solver);
  assert(m);
  
  /* printf("------\n%s\n------\n", Z3_model_to_string(z3->ctx, m)); */
  
  Z3_model_inc_ref(z3->ctx, m);
  
  fun_init(kfun, fun_arity);
  for(size_t xs = 0; xs < int_pow(K, fun_arity); ++xs) {
    /* represent `xs` in the K-ary form,
     * with digits[0] being the highest digit. */
    uint32_t digits[fun_arity];
    get_K_digits(digits, fun_arity, xs);
    Z3_ast args[fun_arity];
    for(size_t i = 0; i < fun_arity; ++i) {
      args[i] = z3->Ek_consts[digits[i]];
    }
    
    /* eval func on given args */
    Z3_ast t = Z3_mk_app(z3->ctx, fun, fun_arity, args);
    Z3_ast res;
 
    assert(Z3_model_eval(z3->ctx, m, t, 1, &res) == Z3_TRUE);


    /* printf("%s == %s\n", Z3_ast_to_string(z3->ctx, t), Z3_ast_to_string(z3->ctx, res)); */
    
    /* interpret the result of function application */
    uint64_t y;
    sscanf(Z3_ast_to_string(z3->ctx, res), "V%lu", &y);
    fun_set_val(kfun, xs, y);
  }
  
  Z3_model_dec_ref(z3->ctx, m);
}


Z3_lbool z3_find_one_discr_function(const clone *clone1_basis, const clone *clone1, const clone *clone2, uint32_t fun_arity, fun *fun) {
  z3_wrapper z3;
  z3_wrapper_init(&z3);
  
  gen_assert_discr_fun_two_clones(&z3, clone1_basis, clone1, clone2, fun_arity);

  Z3_lbool rc = Z3_solver_check(z3.ctx, z3.solver);
  
  if(rc == Z3_L_TRUE) {
    get_function(&z3, z3.fun, fun_arity, fun);
  }
  
  z3_wrapper_free(&z3);
  
  return rc;
}

Z3_lbool z3_find_discr_function(const clone *clone1_basis, const clone *clone1, const clone *clone2, int max_fun_arity, fun *fun) {
  Z3_lbool final_rc = Z3_L_FALSE;     /* the flag shows if we have proved that
                                         the discriminating function of current
                                         arity does not exist */
  for(int fun_arity = 0; fun_arity <= max_fun_arity; ++fun_arity) {
    Z3_lbool rc = z3_find_one_discr_function(clone1_basis, clone1, clone2, fun_arity, fun);
    if(rc == Z3_L_UNDEF) {
      /* we no longer have a proof that the discriminating function does not
         exist */
      final_rc = Z3_L_UNDEF;
    }
    if(rc == Z3_L_TRUE) {
      final_rc = Z3_L_TRUE;
      break;    /* do not search for functions of higher arities */
    }
  }
  return final_rc;
}


