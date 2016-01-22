/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "utils.h"
#include "pred.h"
#include "clone.h"
#include "class.h"
#include "lattice.h"
#include "binary.h"

void test_find_classes_with_one_subclass() {
  lattice lattice;
  lattice_read(51, "data/all_maj_cpp", "data/lattice2", &lattice);
  
  class **classes;
  uint64_t num_classes;
  lattice_find_classes_with_one_subclass(&lattice, &classes, &num_classes);

  printf("\n");
  int idx = 1;
  for(class **pclass = classes; pclass < classes + num_classes; ++pclass) {
    class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct class *subclass = lattice_get_class(&lattice, class->subclasses[0]);
    printf("%d:\t class %.2d:%-6d ~~>  subclass %.2d:%-6d\n",
           idx,
           class->id.layer_id, class->id.class_id,
           subclass->id.layer_id, subclass->id.class_id);
    ++idx;
  }

  free(classes);
  lattice_free(&lattice);
}

int main() {
  printf("test-find-classes-with-one-subclass: ");
  fflush(stdout);
  test_find_classes_with_one_subclass();
  printf("Ok.\n");
}
