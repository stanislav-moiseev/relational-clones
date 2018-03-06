/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "closure.h"
#include "closure/closure2-straightforward.h"
#include "closure/closure2-trace.h"


/* This test randomly creates a set of predicates and compares the
 * result of the closure operation computed by the straightforward
 * implementation and by the implementation that keeps track of
 * formulas (`closure2_get_trace`). */
#define SET_SIZE_LIMIT 512
void test_formula_constructor() {
  closure_operator *clop2 = clop2_alloc_straightforward();

  for(unsigned k = 0; k < 1024; ++k) {
    struct clone clone;
    clone_init(&clone);
    
    unsigned num_preds = rand() % SET_SIZE_LIMIT;
    
    for(unsigned j = 0; j < num_preds; ++j) {
      pred p = {
        .arity = 2,
        .data = rand() % 512
      };

      clone_insert_pred(&clone, &p);
    }
  
    struct clone closure_sf;
    closure_clone(clop2, &clone, &closure_sf);

    struct clone closure_gt;
    closure_trace_t *trace = closure2_clone_traced(&clone, &closure_gt);
    
    closure_trace_free(trace);

    if(!clone_eq(&closure_sf, &closure_gt)) {
      printf("Error\n");
      printf("================================================================\n");
      printf("Initial set of predicates:\n");
      clone_print_verbosely(stdout, &clone);
      
      printf("================================================================\n");
      printf("Difference closure_sf \\ closure_gt:\n");
      struct clone diff1;
      clone_diff(&closure_sf, &closure_gt, &diff1);
      clone_print_verbosely(stdout, &diff1);
      
      printf("================================================================\n");
      printf("Difference closure_gt \\ closure_sf:\n");
      struct clone diff2;
      clone_diff(&closure_gt, &closure_sf, &diff2);
      clone_print_verbosely(stdout, &diff2);
      
      printf("================================================================\n");
      printf("Intersection closure_gt ∩ closure_sf:\n");
      struct clone inter;
      clone_intersection(&closure_sf, &closure_gt, &inter);
      clone_print_verbosely(stdout, &inter);
      
      printf("================================================================\n");
      exit(1);
    }
  }
  
  clop_free(clop2);
}


int main() {
  srand(time(NULL));
  
  printf("test-closure2-trace:\t"); fflush(stdout);
  test_formula_constructor();
  printf("Ok.\n");
}
