/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/bin-maj-lattice.h"
#include "z3/z3-search.h"

void test_find_classes_with_one_subclass(const char *fname) {
  majlattice *lattice = majlattice_read(fname);
  
  majclass **classes;
  uint64_t num_classes;
  majlattice_classes_with_one_subclass(lattice, &classes, &num_classes);
  
  FILE *flog = stdout;

  size_t idx = 0;
  for(majclass **pclass = classes; pclass < classes + num_classes; ++pclass) {
    majclass *class = *pclass;
    assert(class->num_subclasses == 1);
    struct majclass *subclass = majlattice_get_class(lattice, class->subclasses[0]);

    fprintf(flog, "%lu:\t class %2d:%-6d\t subclass %2d:%-6d\n",
            idx,
            class->id.layer_id, class->id.class_id,
            subclass->id.layer_id, subclass->id.class_id);
    fflush(flog);

    ++idx;
  }

  free(classes);
  majlattice_free(lattice);
}


int main() {
  printf("script-maj-classes-with-one-subclass:\n"); fflush(stdout);
  test_find_classes_with_one_subclass("data/all-maj.2016");
  printf("Ok.\n");
}

