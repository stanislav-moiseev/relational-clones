/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/bin-maj-lattice.h"
#include "binary/bin-closure-two-preds.h"
#include "algorithms.h"

void verify(const closure_operator *clop, const char *maj2013, const lattice *lt) {
  FILE *fd = fopen(maj2013, "rb");
  assert(fd != NULL);

  maj_lattice maj_lattice;
  maj_lattice_read(fd, &maj_lattice);
  
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    
    /* if the clone contains a majority operation,
     * verify that it is a member of the lattice `maj2013` */
    if(!clone_contains_majority(&c->clone)) continue;

    /* In current implementation we store only closure-unique predicates,
     * so we have to expand the clone to all essential predicates */
    clone full_closure;
    clone_closure(clop, &c->clone, &full_closure);
    
    /* In the previous lattice we do not store predicates false(0) and true(0),
     * that's why we remove them first.
     */
    clone copy;
    clone_copy(&full_closure, &copy);
    pred p_false, p_true;
    pred_construct(0, "0", &p_false);
    pred_construct(0, "1", &p_true);
    clone_remove_pred(&copy, &p_false);
    clone_remove_pred(&copy, &p_true);

    /* assert(maj_lattice_member(&maj_lattice, &copy)); */
    if(!maj_lattice_member(&maj_lattice, &copy)) {
      printf("Error: the following clone has not been found in maj'2013 lattice:\n");
      clone_print_verbosely(stdout, &c->clone);
      return;
    }
  }
  
  maj_lattice_free(&maj_lattice);
  fclose(fd);
}

void construct_lattice(const char *table2p_name, const char *table2p_uniq_name, const char *maj2013) {
  FILE *fd = fopen(table2p_uniq_name, "rb");
  assert(fd);
  
  closure_table_two_preds *table2p = closure_table_two_preds_alloc();
  closure_two_preds_read(fd, table2p);

  closure_operator *clop = clop_alloc_table_two_preds(table2p);

  lattice *lt = lattice_alloc();
  latice_construct(clop, lt);

  {
    FILE *fd = fopen(table2p_name, "rb");
    assert(fd);
    
    closure_table_two_preds *table2p = closure_table_two_preds_alloc();
    closure_two_preds_read(fd, table2p);

    closure_operator *clop = clop_alloc_table_two_preds(table2p);

    printf("verification: "); fflush(stdout);
    verify(clop, maj2013, lt);
  }

  lattice_free(lt);
  closure_table_two_preds_free(table2p);
  clop_free(clop);
}

int main() {
  printf("script-construct-lattice:\n"); fflush(stdout);
  construct_lattice("data/closure-two-preds.2016",
                    "data/closure-two-uniq-preds.2016",
                    "data/all-maj.2016");
  printf("Ok.\n");
}
