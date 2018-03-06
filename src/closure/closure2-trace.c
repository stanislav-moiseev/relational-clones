/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure2-trace.h"

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


closure_trace_t *closure_trace_alloc() {
  closure_trace_t *trace = malloc(sizeof(closure_trace_t));
  assert(trace);
  
  trace->num_entries = 0;
  trace->capacity    = 128;
  trace->entries     = malloc(trace->capacity * sizeof(trace_entry_t));
  assert(trace->entries);

  return trace;
}

void closure_trace_free(closure_trace_t *trace) {
  free(trace->entries);
  free(trace);
}

void closure_trace_insert(closure_trace_t *trace, const trace_entry_t *entry) {
  if(trace->num_entries == trace->capacity) {
    trace->capacity *= 2;
    trace->entries = realloc(trace->entries, trace->capacity * sizeof(trace_entry_t));
    assert(trace->entries);
  }
  
  trace->entries[trace->num_entries] = *entry;
  ++trace->num_entries;
}


closure_trace_t *closure2_clone_traced(const struct clone *clone, struct clone *closure) {
  /* To speed-up set-membership queries when constructing new
   * predicates, we keep track of all predicates constructed so far in
   * `working_set`.
   */
  struct clone working_set;
  clone_init(&working_set);

  closure_trace_t *trace = closure_trace_alloc();

  
  /* First, insert the base predicates to the working set and to the
   * trace. */
  for(clone_iterator it = clone_iterator_begin(clone); !clone_iterator_end(clone, &it); clone_iterator_next(&it)) {
    pred p = clone_iterator_deref(&it);
    
    clone_insert_pred(&working_set, &p);

    trace_entry_t new_entry = {
      .pred    = p,
      .formula = {
        .head_type           = FN_ATOM,
        .head_data.atom.pred = p
      }
    };
    
    closure_trace_insert(trace, &new_entry);
  }

  
  /* Second, compute permutations of the base predicates and, if we
   * get new predicates, insert them to the trace.
   *
   * We will /not/ compute the permutations of the predicates in the
   * future when computing the closure.
   */
  for(trace_entry_t *entry = trace->entries; entry < trace->entries + trace->num_entries; ++entry) {
    pred q = op_perm2(&entry->pred);
    if(clone_test_pred(&working_set, &q)) continue;

    clone_insert_pred(&working_set, &q);

    trace_entry_t new_entry = {
      .pred    = q,
      .formula = {
        .head_type           = FN_PERM,
        .head_data.perm.arg1 = &entry->formula
      }
    };
    
    closure_trace_insert(trace, &new_entry);
  }  


  /* Third, apply operations of arity 2. The first predicate is taken
   * from the base set and from the supplement set, while the second
   * is taken from the supplement set only.
   *
   * (!) Note that we change the limits of the exterior loop inside
   *     the loop by calling to `closure_trace_insert()`. Therefore,
   *     this procedure will be working while new elements are being
   *     found.
   *
   *     Because we want to find simple formulas, we implement a
   *     width-first algorithm.
   */
  size_t suppl_start = 0;
  size_t suppl_end   = trace->num_entries;
  
  while(suppl_start < suppl_end) {
    for(trace_entry_t *entry1 = trace->entries; entry1 < trace->entries + trace->num_entries; ++entry1) {
      for(trace_entry_t *entry2 = trace->entries + suppl_start; entry2 < trace->entries + suppl_end; ++entry2) {
        pred p1 = entry1->pred;
        pred p2 = entry2->pred;

        {
          pred q = op_conj2(&p1, &p2);
          if(!clone_test_pred(&working_set, &q)) {
            trace_entry_t new_entry = {
              .pred    = q,
              .formula = {
                .head_type           = FN_CONJ,
                .head_data.conj.arg1 = &entry1->formula,
                .head_data.conj.arg2 = &entry2->formula
              }
            };
            closure_trace_insert(trace, &new_entry);
            clone_insert_pred(&working_set, &q);
          }
        }

        {
          pred q = op_comp2(&p1, &p2);
          if(!clone_test_pred(&working_set, &q)) {
            trace_entry_t new_entry = {
              .pred    = q,
              .formula = {
                .head_type           = FN_COMP,
                .head_data.comp.arg1 = &entry1->formula,
                .head_data.comp.arg2 = &entry2->formula
              }
            };
            closure_trace_insert(trace, &new_entry);
            clone_insert_pred(&working_set, &q);
          }
        }

        {
          pred q = op_comp2(&p2, &p1);
          if(!clone_test_pred(&working_set, &q)) {
            trace_entry_t new_entry = {
              .pred    = q,
              .formula = {
                .head_type           = FN_COMP,
                .head_data.comp.arg1 = &entry2->formula,
                .head_data.comp.arg2 = &entry1->formula
              }
            };
            closure_trace_insert(trace, &new_entry);
            clone_insert_pred(&working_set, &q);
          }
        }
      }
    }
  
    suppl_start = suppl_end;
    suppl_end   = trace->num_entries;
  }

  if(closure != NULL) {
    clone_copy(&working_set, closure);
  }
  
  return trace;
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
