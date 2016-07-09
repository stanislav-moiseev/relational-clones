/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This script constructs the lattice R3(2) of relational clones of arity
 * exactly 2.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "closure/closure-straightforward.h"
#include "closure/closure-clone-pred.h"
#include "binary/bin-closure-clone-pred.h"
#include "closure/closure2-straightforward.h"

void verify(const char *ccp2_name, const char *ccp_name) {
  printf("reading \"%s\"...", ccp2_name); fflush(stdout);
  ccplt *lt2 = ccplt_read(ccp2_name);
  printf("\tOk.\n");

  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *lt = ccplt_read(ccp_name);
  printf("\tOk.\n");


  printf("verification"); fflush(stdout);
  closure_operator *clop = clop_alloc_straightforward();

  clone uniq_preds;
  closure_uniq_ess_preds(2, &uniq_preds);

  size_t idx = 0;
  for(ccpnode **cp2 = lt2->nodes; cp2 < lt2->nodes + lt2->num_nodes; ++cp2) {
    ccpnode *c2 = *cp2;

    clone closure;
    closure_clone(clop, &c2->clone, &closure);
    clone_union(&closure, top_clone(), &closure);
    clone_intersection(&closure, &uniq_preds, &closure);

    if(ccplt_lookup(lt, &closure) == NULL) {
      printf("\nError: the following clone has not been found in CCPLT'2016(ar<=2) lattice:\n");
      clone_print_verbosely(stdout, &c2->clone);
      return;
    }
    
    ++idx;
    if(lt->num_nodes >= 40) {
      if(idx % (lt->num_nodes/40) == 0) {
        printf("."); fflush(stdout);
      }
    }
  }

  clop_free(clop);
  ccplt_free(lt);
  ccplt_free(lt2);
}


void construct(const char *ccp_name) {
  closure_operator *clop2 = clop2_alloc_straightforward();

  ccplt *lt = ccplt_alloc();
  
  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  lt->pred_num = predicate_numerator_construct2();

  /* start from a ccplt containing just one clone */
  ccpnode *top = ccpnode_alloc(lt);
  top->clone = *top_clone2();
  ccplt_insert_node(lt, top, 0);
  
  /* iteratively construct new ccpnodes */
  for(pred_idx_t pidx = 0; pidx < lt->pred_num->uniq_sz; ++pidx) {
    ccplt_construct_step(clop2, lt, pidx);
    printf("%u\t %lu\n", pidx, lt->num_nodes);
  }

  assert(lt->num_nodes == 2079040);

  printf("writing \"%s\"...", ccp_name); fflush(stdout);
  ccplt_write(ccp_name, lt);
  printf("\tOk.\n");
  
  ccplt_free(lt);
  clop_free(clop2);
}

int main() {
  printf("script-closure2-clone-pred-construct:\n"); fflush(stdout);
  time_t t0 = time(NULL);
  construct("output/closure2-clone-pred.2016");
  printf("%.2f min. Ok.\n", difftime(time(NULL), t0) / 60.);

  time_t t1 = time(NULL);
  verify("output/closure2-clone-pred.2016",
         "data/closure-clone-pred.2016");
  printf("%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.);
}
