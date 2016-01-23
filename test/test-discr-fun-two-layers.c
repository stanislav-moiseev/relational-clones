/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "z3/wrapper.h"
#include "z3/gen-spec.h"
#include "binary-2016.h"

void get_assert_two_layers(const layer *layer1, const layer *layer2) {
  printf("\n");
  for(int i = 0; i < layer1->num_classes; ++i) {
    for(int j = 0; j < layer2->num_classes; ++j) {
      const class *class1 = layer1->classes + i;
      const class *class2 = layer2->classes + j;

      /* if one set is a subset of the other set */
      if(clone_subset(&class1->clone, &class2->clone)) {
        printf("%d-%d: ", i, j); fflush(stdout);
        z3_wrapper z3;
        z3_wrapper_init(&z3);
        gen_assert_discr_fun_two_classes(&z3, class1, class2, 2);
        z3_wrapper_check(&z3);
        z3_wrapper_free(&z3);
      }
    }
  }
}

void test_gen_assert_disrc_fun_two_layers(const char *fname, layer_id id1, layer_id id2) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);

  lattice lattice;
  lattice_read(fd, &lattice);

  const layer *layer1 = lattice_get_layer(&lattice, id1);
  assert(layer1 != NULL);
  const layer *layer2 = lattice_get_layer(&lattice, id2);
  assert(layer2 != NULL);
  
  get_assert_two_layers(layer1, layer2);
  
  lattice_free(&lattice);
  fclose(fd);
}

int main() {
  printf("test-disrc-fun-two-layers: "); fflush(stdout);
  test_gen_assert_disrc_fun_two_layers("data/all-maj.2016", 49, 50);
  printf("Ok.\n");
}

