/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/bin-maj-lattice.h"
#include "algorithms.h"

void test_find_classes_with_one_subclass(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);
  
  maj_lattice lattice;
  maj_lattice_read(fd, &lattice);
  fclose(fd);
  
  maj_class **classes;
  uint64_t num_classes;
  find_classes_with_one_subclass(&lattice, &classes, &num_classes);
  
  FILE *flog = stdout;

  size_t idx = 0;
  for(maj_class **pclass = classes; pclass < classes + num_classes; ++pclass) {
    maj_class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct maj_class *subclass = maj_lattice_get_class(&lattice, class->subclasses[0]);

    fprintf(flog, "%lu:\t class %2d:%-6d\t subclass %2d:%-6d\n",
            idx,
            class->id.layer_id, class->id.class_id,
            subclass->id.layer_id, subclass->id.class_id);
    fflush(flog);

    ++idx;
  }

  free(classes);
  maj_lattice_free(&lattice);
}


int main() {
  printf("script-maj-classes-with-one-subclass:\n"); fflush(stdout);
  test_find_classes_with_one_subclass("data/all-maj.2016");
  printf("Ok.\n");
}
