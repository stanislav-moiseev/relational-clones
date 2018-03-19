/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes some properties of the sublattices of R3(2),
 * containing 0, 1, 2, min, max.
 *
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "utils.h"
#include "colors.h"
#include "closure/closure-straightforward.h"
#include "closure/closure2-trace.h"
#include "pred-essential.h"
#include "lattice.h"
#include "binary/bin-lattice.h"

#include "../script/sublattice-0-1-2-min-max/sublattice33.h"

lattice *get_sublattice33(const char *lt_name) {
  fprintf(stderr, "reading \"%s\"...", lt_name); fflush(stdout);
  time_t t0 = time(NULL);
  lattice *lt = lattice_read(lt_name);
  fprintf(stderr, "\t%.1f sec. Ok.\n", difftime(time(NULL), t0));

  fun f_0, f_1, f_2;
  fun_scan("fun3_0_0", &f_0);
  fun_scan("fun3_0_1", &f_1);
  fun_scan("fun3_0_2", &f_2);
  fun f_min, f_max;
  fun_scan("fun3_2_210110000", &f_min);
  fun_scan("fun3_2_222211210", &f_max);
  
  /* Select clones containing 0, 1, 2, min, max */
  lattice *sublt = lattice_alloc();
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);
              
      if(fun_preserves_clone(&f_0, &c->clone) &&
         fun_preserves_clone(&f_1, &c->clone) &&
         fun_preserves_clone(&f_2, &c->clone) &&
         fun_preserves_clone(&f_min, &c->clone) &&
         fun_preserves_clone(&f_max, &c->clone)) {

        class *sublt_c = class_alloc(&c->clone, &c->generator);
        lattice_add_class(sublt, sublt_c);
        /* NB. Copy class indices from the main lattice. */
        sublt_c->cidx = c->cidx;
        sublt_c->lidx = c->lidx;
        sublt_c->cpos = c->cpos;
      }
    }
  }
  
  lattice_free(lt);
  return sublt;
}


ccplt *get_ccplt33() {
  fprintf(stderr, "Constructing the sublattices of R3(2), containing 0, 1, 2, min, max...");
  fflush(stderr);
  
  closure_operator *clop2 = clop2_alloc_straightforward();
  ccplt *ccplt = ccplt_alloc();
  
  ccplt->pred_num = predicate_numerator_alloc(basic_preds, num_basic_preds);

  /* start from a ccplt containing just one clone */
  ccpnode *top = ccpnode_alloc(ccplt);
  top->clone = *top_clone2();
  ccplt_insert_node(ccplt, top, 0 /*pidx_begin*/);
  
  /* iteratively construct new ccpnodes */
  for(pred_idx_t pidx = 0; pidx < ccplt->pred_num->uniq_sz; ++pidx) {
    ccplt_construct_step(clop2, ccplt, pidx);
  }

  fprintf(stderr, " Ok.\n");
  fprintf(stderr, "Total nodes: %lu\n", ccplt->num_nodes);

  clop_free(clop2);
  return ccplt;
}

const char *sublattice33_pred_naming_fn_latex(pred p) {
  assert(K == 3);
  assert(p.arity == 2);

  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  size_t idx = 0;
  for(; idx < num_basic_preds; ++idx) {
    if(pred_eq(&p, &basic_preds[idx])) {
      asprintf(&str, "q_{%lu}", idx+1);
      break;
    }
  }
  if(idx == num_basic_preds) {
    fprintf(stderr, COLOR_YELLOW "WARNING: "
                    COLOR_BLUE "the predicate %s is not a member of 10 basic predicates; it was printed as p_{%lu}."
                    COLOR_RESET "\n",
            pred_print_extensional_ex(&p), p.data);
    asprintf(&str, "p_{%lu}", p.data);
  }
  
  return str;
}

