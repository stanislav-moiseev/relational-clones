/*******************************************************************************
 * (C) 2018 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure2-trace.h"

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


closure_trace_t *closure2_trace(const pred_descr_t *preds, size_t sz, struct clone *closure) {
  /* To speed-up set-membership queries when constructing new
   * predicates, we keep track of all predicates constructed so far in
   * `working_set`.
   */
  struct clone working_set;
  clone_init(&working_set);

  closure_trace_t *trace = closure_trace_alloc();

  
  /* First, insert the base predicates to the working set and to the
   * trace. */
  for(const pred_descr_t *descr = preds; descr < preds + sz; ++descr) {
    clone_insert_pred(&working_set, &descr->pred);

    trace_entry_t new_entry = {
      .pred    = descr->pred,
      .formula = {
        .head_type            = FN_ATOM,
        .head_data.atom.descr = *descr
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

