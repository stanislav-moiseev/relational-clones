/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "lattice.h"
#include "binary/bin-closure-clone-pred.h"

void script_lattice_construct_layers(const char *ccp_name) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  lattice *lt = lattice_alloc();
  lattice_load_classes_from_ccplt(lt, ccplt);
  lattice_construct_layers(lt, ccplt);
  
  lattice_free(lt);
  ccplt_free(ccplt);
}

void verify_maximal_subclones(const lattice *lt, const ccplt *ccplt) {
  /* Verify that if no subclones have been found for a given clone `c`,
   * then for all closure-unique predicate `p` we have
   *< p ∪ c> == c*/
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    const ccpnode *nd = ccplt_get_node(ccplt, c->cidx);
     if(c->num_subclasses == 0) {
      for(class_idx *child2_cidx = nd->children; child2_cidx < nd->children + nd->num_children; ++child2_cidx) {
        assert(c->cidx == *child2_cidx);
      }
    }
  }
}

void script_lattice_construct_maximal_subclones(const char *ccp_name) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  time_t t1 = time(NULL);
  printf("construction..."); fflush(stdout);
  lattice *lt = lattice_alloc();
  lattice_load_classes_from_ccplt(lt, ccplt);
  lattice_construct_maximal_subclones(lt, ccplt);
  printf("\t%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.);

  time_t t2 = time(NULL);
  printf("verification..."); fflush(stdout);
  verify_maximal_subclones(lt, ccplt);
  printf("\t%.2f min. Ok.\n", difftime(time(NULL), t2) / 60.);
  
  lattice_free(lt);
  ccplt_free(ccplt);
}

int main() {
  /* time_t t0 = time(NULL); */
  /* printf("script-lattice-construct-layers:\n"); */
  /* script_lattice_construct_layers("data/closure-clone-pred.2016"); */
  /* printf("Ok.\n"); */
  /* printf("%.2f min\n", difftime(time(NULL), t0) / 60.); */

  printf("script-lattice-construct-maximal-subclones:\n");
  script_lattice_construct_maximal_subclones("data/closure-clone-pred.2016");
}
