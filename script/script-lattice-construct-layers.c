/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "lattice.h"
#include "binary/bin-closure-clone-pred.h"
#include "binary/bin-lattice.h"

void verify_maximal_subclones(const lattice *lt, const ccplt *ccplt) {
  /* Verify that there is exactly one clone `c` (the bottom) such that for all
   * closure-unique predicate `p` we have <{p} ∪ c> == c. */
  int num = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(c->num_subclasses == 0) {
      ++num;
    }
  }
  assert(num == 1);
}

void script_lattice_construct_layers(const char *ccp_name, const char *fout_name) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccp_name);
  printf("\tOk.\n\n");

  lattice *lt = lattice_alloc();
  lattice_load_classes_from_ccplt(lt, ccplt);
  lattice_construct_layers(lt, ccplt);
  lattice_construct_maximal_subclones(lt, ccplt);
  lattice_sort_maximal_subclones(lt);
  verify_maximal_subclones(lt, ccplt);
  
  lattice_write(fout_name, lt);
  
  lattice_free(lt);
  ccplt_free(ccplt);
}

/* void script_lattice_construct_maximal_subclones(const char *ccp_name) { */
/*   printf("reading \"%s\"...", ccp_name); fflush(stdout); */
/*   ccplt *ccplt = ccplt_read(ccp_name); */
/*   printf("\tOk.\n"); */

/*   lattice *lt = lattice_alloc(); */
/*   lattice_load_classes_from_ccplt(lt, ccplt); */
/*   lattice_construct_maximal_subclones(lt, ccplt); */

/*   time_t t2 = time(NULL); */
/*   printf("verification..."); fflush(stdout); */
/*   verify_maximal_subclones(lt, ccplt); */
/*   printf("\t%.2f min. Ok.\n", difftime(time(NULL), t2) / 60.); */
    
/*   lattice_free(lt); */
/*   ccplt_free(ccplt); */
/* } */

int main() {
  time_t t0 = time(NULL);
  printf("script-lattice-construct-layers:\n");
  script_lattice_construct_layers("data/closure-clone-pred.2016",
                                  "output/lattice.2016");
  printf("Ok.\n");
  printf("%.2f min\n", difftime(time(NULL), t0) / 60.);

  /* time_t t1 = time(NULL); */
  /* printf("script-lattice-construct-maximal-subclones:\n"); */
  /* script_lattice_construct_maximal_subclones("data/closure-clone-pred.2016"); */
  /* printf("%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.); */
}
