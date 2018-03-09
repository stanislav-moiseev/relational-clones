/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 *
 * This module implements an extended version of the closure operator
 * for predicates of arity = 2 that keeps track of the operations
 * applied to predicates and produces beautiful terms for new
 * predicates in the closure.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure2-formulas.h"
#include "closure/closure2-straightforward.h" /* op_perm, op_conj, op_comp */

pred term_eval(const term_t *tau) {
  switch(tau->head_type) {
  case FN_ATOM: {
    return tau->head_data.atom.pred;
  }
    
  case FN_PERM: {
    pred p1 = term_eval(tau->head_data.perm.arg1);
    return op_perm2(&p1);
  }
    
  case FN_CONJ: {
    pred p1 = term_eval(tau->head_data.conj.arg1);
    pred p2 = term_eval(tau->head_data.conj.arg2);
    return op_conj2(&p1, &p2);
  }
    
  case FN_COMP: {
    pred p1 = term_eval(tau->head_data.comp.arg1);
    pred p2 = term_eval(tau->head_data.comp.arg2);
    return op_comp2(&p1, &p2);
  }}

  /* unreachable */
  pred p;
  return p;
}


#define ARG_VAL2(arg)                                                   \
  ((arg == -1) ? y1 :                                                   \
   ((arg == -2) ? y2 :                                                  \
    ((arg == 1) ? x1 :                                                  \
     ((arg == 2) ? x2 :                                                 \
      (assert(0 && "formula_eval: invalid atom's argument number (expected: -1, -2, 1, 2)"), 0))))) \
  
pred formula_eval(const formula_t *phi) {
  assert(phi->num_bounded_vars <= 2 && "formula_eval is implemented for formulas with <= 2 bounded variables only.");
  
  for(const atom_t *atom = phi->atoms; atom < phi->atoms + phi->num_atoms; ++atom) {
    assert(atom->pred.arity == 2 && "formula_eval is implemented for predicates of arity == 2 only.");
  }
    
  pred resp;
  pred_init(&resp, 2 /*arity*/);
    
  for(uint32_t x1 = 0; x1 < K; ++x1) {
    for(uint32_t x2 = 0; x2 < K; ++x2) {
      uint64_t resp_tuple = x1*K + x2;

      int exists;
      
      /* If phi->num_bounded_vars < 2, these loops will exit optimally quickly. */
      for(uint32_t y2 = 0; y2 < K; ++y2) {
        for(uint32_t y1 = 0; y1 < K; ++y1) {
          exists = 1;
          
          for(const atom_t *atom = phi->atoms; atom < phi->atoms + phi->num_atoms; ++atom) {
            uint64_t p_tuple = ARG_VAL2(atom->arg1) * K + ARG_VAL2(atom->arg2);
            if(!pred_compute(&atom->pred, p_tuple)) {
              exists = 0;
              break;
            }
          }
          
          if(exists) {
            pred_set(&resp, resp_tuple);
            break;
          }

          if(!exists && phi->num_bounded_vars == 0) break;
        }
        
        if(exists) break;
        if(!exists && phi->num_bounded_vars <= 1) break;
      }
    }
  }

  return resp;
}


/**
 * `phi` works as a shared state for all recursive executions of this
 * worker function.
 *
 * Some executions may allocate a fresh bounded variable; other
 * executions should now how many bounded variable have been allocated
 * so far.
 */
static void term_to_formula_worker(formula_t *phi, const term_t *tau, int var1, int var2) {
  switch(tau->head_type) {
  case FN_ATOM: {
    atom_t atom = {
      .pred = tau->head_data.atom.pred,
      .arg1 = var1,
      .arg2 = var2,
    };
    formula_insert_atom(phi, &atom);
    break;
  }

  case FN_PERM: {
    term_to_formula_worker(phi, tau->head_data.perm.arg1, var2, var1);
    break;
  }

  case FN_CONJ: {
    term_to_formula_worker(phi, tau->head_data.conj.arg1, var1, var2);
    term_to_formula_worker(phi, tau->head_data.conj.arg2, var1, var2);
    break;
  }

  case FN_COMP: {
    /* We should fix a bounded variable /before/ a recursive execution
     * of this worker function, because that execution can allocate
     * new bounded variables, thus changing the value of `phi->num_bounded_vars`. */
    int bounded_var = formula_get_fresh_bounded_var(phi);
    term_to_formula_worker(phi, tau->head_data.comp.arg1, var1, bounded_var);
    term_to_formula_worker(phi, tau->head_data.comp.arg2, bounded_var, var2);
    break;
  }}
}


formula_t *term_to_formula(const term_t *tau) {
  formula_t *phi = formula_alloc();
  term_to_formula_worker(phi, tau, 1/*var1*/, 2/*var2*/);
  return phi;
}

formula_t *formula_alloc() {
  formula_t *phi = malloc(sizeof(formula_t));
  assert(phi);
  phi->num_bounded_vars = 0;
  phi->num_atoms   = 0;
  phi->capacity    = 16;
  phi->atoms       = malloc(phi->capacity * sizeof(atom_t));
  assert(phi->atoms);
  return phi;
}

void formula_free(formula_t *phi) {
  free(phi->atoms);
  free(phi);
}

void formula_insert_atom(formula_t *phi, const atom_t *atom) {
  if(phi->num_atoms == phi->capacity) {
    phi->capacity *= 2;
    phi->atoms = realloc(phi->atoms, phi->capacity);
  }
  assert(phi->num_atoms < phi->capacity);
  
  phi->atoms[phi->num_atoms] = *atom;
  
  ++phi->num_atoms;
}

int formula_get_fresh_bounded_var(formula_t *phi) {
  ++phi->num_bounded_vars;
  return -(phi->num_bounded_vars);
}


char *term_print(const term_t *tau, pred_naming_fn_t pred_naming_fn) {
  char *str;
  
  switch(tau->head_type) {
  case FN_ATOM: {
    asprintf(&str, "%s", pred_naming_fn(tau->head_data.atom.pred));
    break;
  }
    
  case FN_PERM: {
    char *substr = term_print(tau->head_data.perm.arg1, pred_naming_fn);
    asprintf(&str, "perm(%s)", substr);
    free(substr);
    break;
  }
    
  case FN_CONJ: {
    char *substr1 = term_print(tau->head_data.conj.arg1, pred_naming_fn);
    char *substr2 = term_print(tau->head_data.conj.arg2, pred_naming_fn);
    asprintf(&str, "conj(%s, %s)", substr1, substr2);
    free(substr1);
    free(substr2);
    break;
  }
    
  case FN_COMP: {
    char *substr1 = term_print(tau->head_data.comp.arg1, pred_naming_fn);
    char *substr2 = term_print(tau->head_data.comp.arg2, pred_naming_fn);
    asprintf(&str, "comp(%s, %s)", substr1, substr2);
    free(substr1);
    free(substr2);
    break;
  }}
  
  return str;
}


char *formula_print_latex(const formula_t *phi, pred_naming_fn_t pred_naming_fn, var_naming_fn_t var_naming_fn) {
  for(const atom_t *atom = phi->atoms; atom < phi->atoms + phi->num_atoms; ++atom) {
    assert(atom->pred.arity == 2 && "formula_print_latex is implemented for predicates of arity == 2 only.");
  }

  char *str;
  size_t sizeloc;
  FILE *fd = open_memstream(&str, &sizeloc);
  assert(fd);

  if(phi->num_atoms == 0) {
    assert(phi->num_bounded_vars == 0 && "formula_print_latex: a formula with no atoms should have no bounded variables.");
    assert(K == 3);
    static const pred p_true  = { .arity = 2, .data  = 0x1FF };
    fprintf(fd, "%s", pred_naming_fn(p_true));
    fclose(fd);
    return str;
  }

  int use_multline = 1;

  for(int k = 1; k <= phi->num_bounded_vars; ++k) {
    fprintf(fd, "\\exists %s\\, ", var_naming_fn(-k));
  }

  if(phi->num_bounded_vars > 0) {
    fprintf(fd, "\\bigl(");
  }

  assert(phi->num_atoms <= 6);
  for(int k = 0; k < phi->num_atoms; ++k) {
    if(k > 0) {
      fprintf(fd, " \\wedge ");
    }

    if(use_multline) {
      if((phi->num_atoms == 4 && k == 2) ||
         (phi->num_atoms >= 5 && k == 3)) {
        fprintf(fd, "{} \\\\ && \\hspace{-0.7\\textwidth} {}\\wedge ");
      }
    }
    
    char *arg1 = strdup(var_naming_fn(phi->atoms[k].arg1));
    char *arg2 = strdup(var_naming_fn(phi->atoms[k].arg2));
    fprintf(fd, "%s(%s, %s)", pred_naming_fn(phi->atoms[k].pred), arg1, arg2);
    free(arg1);
    free(arg2);
  }
  
  if(phi->num_bounded_vars > 0) {
    fprintf(fd, "\\bigr)");
  }

  fclose(fd);
  return str;
}


/********************************************************************/
/** Naming functions. **/

static const pred p_false = { .arity = 2, .data  = 0x000 };
static const pred p_true  = { .arity = 2, .data  = 0x1FF };
static const pred p_eq    = { .arity = 2, .data  = 0x111 };


const char *pred_naming_fn_latex(pred p) {
  assert(K == 3);
  assert(p.arity == 2);
  
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  if(pred_eq(&p, &p_false)) {
    asprintf(&str, "false^{(2)}");
    
  } else if(pred_eq(&p, &p_true)) {
    asprintf(&str, "true^{(2)}");
    
  } else if(pred_eq(&p, &p_eq)) {
    asprintf(&str, "eq^{(2)}");
    
  } else {
    asprintf(&str, "p_{%lu}", p.data);
  }
  return str;
}


const char *var_naming_fn_latex(int var) {
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  assert(var != 0 && "var_name: var number should be > 0 for unbound variables, and < 0 for bound variables.");
  if(var > 0) {
    asprintf(&str, "x_{%d}", var);
  }
  if(var < 0) {
    asprintf(&str, "y_{%d}", -var);
  }
  
  return str;
}


const char *clone_naming_fn_latex(const struct clone *clone) {
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }
  
  size_t sizeloc;
  FILE *fd = open_memstream(&str, &sizeloc);
  assert(fd);

  if(clone_is_empty(clone)) {
    fprintf(fd, "\\varnothing");
    fclose(fd);
    return str;
  }
  
  fprintf(fd, "\\{");

  unsigned nprinted = 0;

  if(clone_test_pred(clone, &p_false)) {
    fprintf(fd, pred_naming_fn_latex(p_false));
    ++nprinted;
  }
  if(clone_test_pred(clone, &p_true)) {
    if(nprinted > 0) {
      fprintf(fd, ", ");
    }
    fprintf(fd, pred_naming_fn_latex(p_true));
    ++nprinted;
  }
  if(clone_test_pred(clone, &p_eq)) {
    if(nprinted > 0) {
      fprintf(fd, ", ");
    }
    fprintf(fd, pred_naming_fn_latex(p_eq));
    ++nprinted;
  }

  unsigned card = clone_cardinality(clone);
  
  for(clone_iterator it = clone_iterator_begin(clone); !clone_iterator_end(clone, &it); clone_iterator_next(&it)) {
    pred p = clone_iterator_deref(&it);

    if(pred_eq(&p, &p_false) || pred_eq(&p, &p_true) || pred_eq(&p, &p_eq)) {
      continue;
    }

    if(nprinted > 0) {
      fprintf(fd, ", \\> ");
    }

    if(nprinted >= 2 && nprinted <= card - 2) {
      fprintf(fd, "\\allowbreak ");
    }

    fprintf(fd, pred_naming_fn_latex(p));
        
    ++nprinted;
  }

  fprintf(fd, "\\}");

  fclose(fd);
  return str;
}

