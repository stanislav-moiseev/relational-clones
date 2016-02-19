/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "fun-majority.h"
#include "lattice.h"
#include "binary/bin-closure-clone-pred.h"
#include "binary/bin-lattice.h"
#include "binary/bin-maj-lattice.h"

#include "script-verify-maj.h"

void script_lattice_construct_layers(const char *ccp_name, const char *fout_name) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  lattice *lt = lattice_alloc();
  lattice_load_classes_from_ccplt(lt, ccplt);
  printf("\n");
  lattice_construct_layers(lt, ccplt);
  lattice_write(fout_name, lt);
  
  lattice_free(lt);
  ccplt_free(ccplt);
}

void script_lattice_construct_maximal_subclones(const char *ccp_name, const char *fin_name, const char *fout_name) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  printf("reading \"%s\"...", fin_name); fflush(stdout);
  lattice *lt = lattice_read(fin_name);
  printf("\tOk.\n");

  lattice_construct_maximal_subclones(lt, ccplt);
  lattice_sort_maximal_subclones(lt);

  lattice_write(fout_name, lt);
  
  lattice_free(lt);
  ccplt_free(ccplt);
}

/** Verify the computation over the previously computed lattice of all clones
 *  containing a majority operation. If the clone from new lattice contains a
 *  majority operation, we verify that the set of its maximal proper subclones
 *  containing a majority operation coincide with that from the lattice
 *  `maj2013`.
 */
void verify_maximal_subclones(const char *fin_name, const char *maj2013) {
  printf("reading \"%s\"...", maj2013); fflush(stdout);
  maj_lattice *maj_lattice = maj_lattice_read(maj2013);
  printf("\t\tOk.\n");

  printf("reading \"%s\"...", fin_name); fflush(stdout);
  lattice *lt = lattice_read(fin_name);
  printf("\tOk.\n");

  printf("verification"); fflush(stdout);
  size_t idx = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(!clone_contains_majority(&c->clone)) continue;

    clone copy;
    clone_prepare_for_maj2013(&c->clone, &copy);
    maj_class *maj_c = maj_lattice_lookup(maj_lattice, &copy);
    assert(maj_c != NULL);

    size_t num_maj_subs = 0;
    for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
      class *sub = lattice_get_class(lt, *sub_idx);
      if(!clone_contains_majority(&sub->clone)) continue;
      ++num_maj_subs;

      /* Test that the given maximal subclone is present in maj'2013. */
      clone sub_copy;
      clone_prepare_for_maj2013(&sub->clone, &sub_copy);
      if(!maj_lattice_member(maj_lattice, &sub_copy)) {
        printf("\nError: the following clone contains a majority operation, but its maximal proper subclone has not been found in maj'2013 lattice:\n");
        clone_print_verbosely(stdout, &c->clone);
        printf("================================\n");
        printf("maximal proper subclone:\n");
        clone_print_verbosely(stdout, &sub->clone);
        return;
      }
    }

    /* Verify that the number of maximal proper subclones coincide. */
    assert(num_maj_subs == maj_c->num_subclasses);

    ++idx;
    if(lt->num_classes >= 40) {
      if(idx % (lt->num_classes/40) == 0) {
        printf("."); fflush(stdout);
      }
    }
  }
}

int main() {
  time_t t0 = time(NULL);
  printf("script-lattice-construct-layers:\n");
  script_lattice_construct_layers("data/closure-clone-pred.2016",
                                  "output/lattice.2016");
  printf("Ok.\n");
  printf("%.2f min\n", difftime(time(NULL), t0) / 60.);

  time_t t1 = time(NULL);
  printf("script-lattice-construct-maximal-subclones:\n");
  script_lattice_construct_maximal_subclones("data/closure-clone-pred.2016",
                                             "output/lattice.2016",
                                             "output/lattice.2016");
  printf("%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.);

  time_t t2 = time(NULL);
  printf("verify-maximal-subclones:\n");
  verify_maximal_subclones("output/lattice.2016",
                           "data/all-maj.2016");
  printf("\t%.2f min. Ok.\n", difftime(time(NULL), t2) / 60.);
}
