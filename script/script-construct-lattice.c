/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This script constructs the lattice R3(2) of relational clones of arity <= 2
 * under derivation rules considering predicates of arity <= 2 only.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "fun-majority.h"
#include "closure/closure-two-preds.h"
#include "algorithm/alg-closure-clone-pred.h"
#include "binary/bin-maj-lattice.h"
#include "binary/bin-closure-two-preds.h"
#include "binary/bin-closure-clone-pred.h"

void verify_lattice(const char *ccp_name, const char *table2p_name, const char *maj2013) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *lt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  printf("reading \"%s\"...", table2p_name);
  closure_operator *clop = clop_two_preds_read(table2p_name);
  printf("\tOk.\n");

  printf("reading \"%s\"...", maj2013); fflush(stdout);
  FILE *fd = fopen(maj2013, "rb");
  assert(fd != NULL);
  maj_lattice maj_lattice;
  maj_lattice_read(fd, &maj_lattice);
  printf("\t\t\tOk.\n");

  printf("verification"); fflush(stdout);
  size_t num_maj_nodes = 0;
  size_t idx = 0;
  for(ccpnode **cp = lt->nodes; cp < lt->nodes + lt->num_nodes; ++cp) {
    ccpnode *c = *cp;
    
    /* If the clone contains a majority operation,
     * verify that it is a member of the lattice `maj2013` */
    if(clone_contains_majority(&c->clone)) {
      ++num_maj_nodes;

      /* In current implementation we store only closure-unique predicates,
       * so we have to expand the clone to all essential predicates */
      clone full_closure;
      closure_clone(clop, &c->clone, &full_closure);
    
      /* In the previous lattice (maj'2013) we did not store predicates false(0)
       * and true(0), that's why we remove them first. */
      clone copy;
      clone_copy(&full_closure, &copy);
      pred p_false, p_true;
      pred_construct(0, "0", &p_false);
      pred_construct(0, "1", &p_true);
      clone_remove_pred(&copy, &p_false);
      clone_remove_pred(&copy, &p_true);

      if(!maj_lattice_member(&maj_lattice, &copy)) {
        printf("\nError: the following clone has not been found in maj'2013 lattice:\n");
        clone_print_verbosely(stdout, &c->clone);
        return;
      }
    }
    
    ++idx;
    if(lt->num_nodes >= 40)
      if(idx % (lt->num_nodes/40) == 0) {
      printf(".");
      fflush(stdout);
    }
  }

  printf("\n%lu clones with majority have been found.\n", num_maj_nodes);
  assert(num_maj_nodes == 1918040);

  maj_lattice_free(&maj_lattice);
  ccplt_free(lt);
  clop_free(clop);
  fclose(fd);
}

void construct_lattice(const char *table2p_uniq_name, const char *ccp_name) {
  closure_operator *clop = clop_two_preds_read(table2p_uniq_name);

  ccplt *lt = ccplt_alloc();
  latice_construct(clop, lt);
  assert(lt->num_nodes == 2079040);

  printf("writing \"%s\"...", ccp_name); fflush(stdout);
  ccplt_write(ccp_name, lt);
  printf("\tOk.\n");
  
  ccplt_free(lt);
  clop_free(clop);
}

int main() {
  printf("script-construct-lattice:\n"); fflush(stdout);
  time_t t0 = time(NULL);
  construct_lattice("data/closure-two-uniq-preds.2016",
                    "output/closure-clone-pred.2016");
  printf("%.2f min\n", difftime(time(NULL), t0) / 60.);

  time_t t1 = time(NULL);
  printf("\nscript-verify-lattice:\n");
  verify_lattice("output/closure-clone-pred.2016",
                 "data/closure-two-preds.2016",
                 "data/all-maj.2016");
  printf("%.2f min\n", difftime(time(NULL), t1) / 60.);
  printf("Ok.\n");
}
