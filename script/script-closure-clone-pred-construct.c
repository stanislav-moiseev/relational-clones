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
#include "closure/closure-straightforward.h"
#include "closure/closure-two-preds.h"
#include "algorithm/alg-closure-clone-pred.h"
#include "binary/bin-maj-lattice.h"
#include "binary/bin-closure-two-preds.h"
#include "binary/bin-closure-clone-pred.h"

#include "script-verify-maj.h"

/** Verify the computation over the previously computed lattice of all clones
 *  containing a majority operation. If the clone from new lattice contains a
 *  majority operation, we verify that it is a member of the lattice `maj2013`.
 */
void verify_lattice(const char *ccp_name, const char *maj2013) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *lt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  printf("reading \"%s\"...", maj2013); fflush(stdout);
  maj_lattice *maj_lattice = maj_lattice_read(maj2013);
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

      clone copy;
      clone_prepare_for_maj2013(&c->clone, &copy);

      if(!maj_lattice_member(maj_lattice, &copy)) {
        printf("\nError: the following clone has not been found in maj'2013 lattice:\n");
        clone_print_verbosely(stdout, &c->clone);
        return;
      }
    }
    
    ++idx;
    if(lt->num_nodes >= 40) {
      if(idx % (lt->num_nodes/40) == 0) {
        printf("."); fflush(stdout);
      }
    }
  }

  printf("\n%lu clones with majority have been found.\n", num_maj_nodes);
  assert(num_maj_nodes == 1918040);

  maj_lattice_free(maj_lattice);
  ccplt_free(lt);
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
  printf("%.2f min. Ok.\n", difftime(time(NULL), t0) / 60.);

  time_t t1 = time(NULL);
  printf("\nscript-verify-lattice:\n");
  verify_lattice("output/closure-clone-pred.2016",
                 "data/all-maj.2016");
  printf("%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.);
}
