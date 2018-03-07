/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 *
 * This module implements an extended version of the closure operator
 * for predicates of arity = 2 that keeps track of the operations
 * applied to predicates and produces beautiful formulas for new
 * predicates in the closure.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure2-formulas.h"

pred formula_eval(const formula_t *phi) {
  switch(phi->head_type) {
  case FN_ATOM: {
    return phi->head_data.atom.pred;
  }
    
  case FN_PERM: {
    pred p1 = formula_eval(phi->head_data.perm.arg1);
    return op_perm2(&p1);
  }
    
  case FN_CONJ: {
    pred p1 = formula_eval(phi->head_data.conj.arg1);
    pred p2 = formula_eval(phi->head_data.conj.arg2);
    return op_conj2(&p1, &p2);
  }
    
  case FN_COMP: {
    pred p1 = formula_eval(phi->head_data.comp.arg1);
    pred p2 = formula_eval(phi->head_data.comp.arg2);
    return op_comp2(&p1, &p2);
  }}

  /* unreachable */
  pred p;
  return p;
}


char *print_formula_func_form(const formula_t *phi, pred_naming_fn_t pred_naming_fn) {
  char *str;
  
  switch(phi->head_type) {
  case FN_ATOM: {
    asprintf(&str, "%s", pred_naming_fn(phi->head_data.atom.pred));
    break;
  }
    
  case FN_PERM: {
    char *substr = print_formula_func_form(phi->head_data.perm.arg1, pred_naming_fn);
    asprintf(&str, "perm(%s)", substr);
    free(substr);
    break;
  }
    
  case FN_CONJ: {
    char *substr1 = print_formula_func_form(phi->head_data.conj.arg1, pred_naming_fn);
    char *substr2 = print_formula_func_form(phi->head_data.conj.arg2, pred_naming_fn);
    asprintf(&str, "conj(%s, %s)", substr1, substr2);
    free(substr1);
    free(substr2);
    break;
  }
    
  case FN_COMP: {
    char *substr1 = print_formula_func_form(phi->head_data.comp.arg1, pred_naming_fn);
    char *substr2 = print_formula_func_form(phi->head_data.comp.arg2, pred_naming_fn);
    asprintf(&str, "comp(%s, %s)", substr1, substr2);
    free(substr1);
    free(substr2);
    break;
  }}
  
  return str;
}


/**
 * `num_bounded_vars` works as a shared state for all executions of
 * this worker function. Some executions may allocate a fresh bounded
 * variable; other executions should now how many bounded variable
 * have been allocated so far.
 */
static char *print_formula_quantified_form_worker(int *num_bounded_vars,
                                                  const formula_t *phi, int var1, int var2,
                                                  pred_naming_fn_t pred_naming_fn,
                                                  var_naming_fn_t var_naming_fn) {
  char *str = NULL;
  
  switch(phi->head_type) {
  case FN_ATOM: {
    char *var1_name = strdup(var_naming_fn(var1));
    char *var2_name = strdup(var_naming_fn(var2));
    asprintf(&str, "%s(%s,%s)", pred_naming_fn(phi->head_data.atom.pred), var1_name, var2_name);
    free(var1_name);
    free(var2_name);
    break;
  }
    
  case FN_PERM: {
    str = print_formula_quantified_form_worker(num_bounded_vars, phi->head_data.perm.arg1, var2, var1, pred_naming_fn, var_naming_fn);
    break;
  }
    
  case FN_CONJ: {
    char *substr1 = print_formula_quantified_form_worker(num_bounded_vars, phi->head_data.conj.arg1, var1, var2, pred_naming_fn, var_naming_fn);
    char *substr2 = print_formula_quantified_form_worker(num_bounded_vars, phi->head_data.conj.arg2, var1, var2, pred_naming_fn, var_naming_fn);
    asprintf(&str, "%s \\wedge %s", substr1, substr2);
    free(substr1);
    free(substr2);
    break;
  }
    
  case FN_COMP: {
    ++(*num_bounded_vars);
    /* We should fix a bounded variable /before/ a recursive execution
     * of the worker function, because that execution can allocate new
     * bounded variables, thus changing the value of (*num_bounded_vars). */
    int bounded_var = -(*num_bounded_vars);
    /* Print the left side, possibly changing the value of (*num_bounded_vars). */
    char *substr1 = print_formula_quantified_form_worker(num_bounded_vars, phi->head_data.comp.arg1, var1, bounded_var, pred_naming_fn, var_naming_fn);
    /* Print the right side. */
    char *substr2 = print_formula_quantified_form_worker(num_bounded_vars, phi->head_data.comp.arg2, bounded_var, var2, pred_naming_fn, var_naming_fn);
    asprintf(&str, "%s \\wedge %s", substr1, substr2);
    free(substr1);
    free(substr2);
    break;
  }}

  return str;
}


char *print_formula_quantified_form(const formula_t *phi, pred_naming_fn_t pred_naming_fn, var_naming_fn_t var_naming_fn) {
  int num_bounded_vars = 0;
  char *body = print_formula_quantified_form_worker(&num_bounded_vars, phi, 1/*var1*/, 2/*var2*/, pred_naming_fn, var_naming_fn);
  assert(num_bounded_vars >= 0);
  
  if(num_bounded_vars == 0) {
    return body;
  }

  char *head = malloc(1);
  head[0] = 0;
  for(int k = 1; k <= num_bounded_vars; ++k) {
    char *str;
    asprintf(&str, "%s\\exists %s\\, ", head, var_naming_fn(-k));
    free(head);
    head = str;
  }

  char *str;
  asprintf(&str, "%s \\bigl( %s \\bigr)", head, body);
  free(body);
  return str;
}


static inline void strappend(char **str1, const char *str2) {
  char *str;
  asprintf(&str, "%s%s", *str1, str2);
  free(*str1);
  *str1 = str;
}


const char *pred_naming_fn(pred p) {
  assert(p.arity == 2);
  
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  if(p.data == 0) {
    asprintf(&str, "false^{(2)}");
  } else if(p.data == 0x1FF) {
    asprintf(&str, "true^{(2)}");
  } else if(p.data == 0x111) {
    asprintf(&str, "eq^{(2)}");
  } else {
    asprintf(&str, "p_{%lu}", p.data);
  }
  return str;
}


const char *var_naming_fn(int var) {
  static char buf[64];
  assert(var != 0 && "var_name: var number should be > 0 for unbound variables, and < 0 for bound variables.");
  if(var > 0) {
    snprintf(buf, 64, "x_{%d}", var);
  }
  if(var < 0) {
    snprintf(buf, 64, "y_{%d}", -var);
  }
  return buf;
}


const char *clone_naming_fn(const struct clone *clone) {
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  if(clone_is_empty(clone)) {
    asprintf(&str, "\\varnothing");
    return str;
  }
  
  asprintf(&str, "\\{");

  unsigned nprinted = 0;

  static const pred p_false = { .arity = 2, .data  = 0x000 };
  static const pred p_true  = { .arity = 2, .data  = 0x1FF };
  static const pred p_eq    = { .arity = 2, .data  = 0x111 };

  if(clone_test_pred(clone, &p_false)) {
    strappend(&str, pred_naming_fn(p_false));
    ++nprinted;
  }
  if(clone_test_pred(clone, &p_true)) {
    if(nprinted > 0) {
      strappend(&str, ", ");
    }
    strappend(&str, pred_naming_fn(p_true));
    ++nprinted;
  }
  if(clone_test_pred(clone, &p_eq)) {
    if(nprinted > 0) {
      strappend(&str, ", ");
    }
    strappend(&str, pred_naming_fn(p_eq));
    ++nprinted;
  }

  unsigned card = clone_cardinality(clone);
  
  for(clone_iterator it = clone_iterator_begin(clone); !clone_iterator_end(clone, &it); clone_iterator_next(&it)) {
    pred p = clone_iterator_deref(&it);

    if(pred_eq(&p, &p_false) || pred_eq(&p, &p_true) || pred_eq(&p, &p_eq)) {
      continue;
    }

    if(nprinted > 0) {
      strappend(&str, ", \\, ");
    }

    if(nprinted >= 2 && nprinted <= card - 2) {
      strappend(&str, "\\allowbreak ");
    }

    strappend(&str, pred_naming_fn(p));
        
    ++nprinted;
  }

  strappend(&str, "\\}");

  return str;
}

