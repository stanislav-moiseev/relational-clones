/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "algorithm/alg-maj-classes.h"
#include "binary/bin-maj-lattice.h"

void worker(const maj_layer *layer1, const maj_layer *layer2) {
  for(int i = 0; i < layer1->num_classes; ++i) {
    for(int j = 0; j < layer2->num_classes; ++j) {
      const maj_class *class1 = layer1->classes + i;
      const maj_class *class2 = layer2->classes + j;

      /* if one set is a subset of the other set */
      if(clone_subset(&class1->clone, &class2->clone)) {
        printf("class %2d:%-6d\t subclass %2d:%-6d\t ",
            class1->id.layer_id, class1->id.class_id,
            class2->id.layer_id, class2->id.class_id);
        fflush(stdout);

        fun fun;
        Z3_lbool rc = find_discr_function(class1, class2, 5, &fun);
        switch(rc) {
        case Z3_L_FALSE:
          printf("unsat\n");
          break;
        case Z3_L_UNDEF:
          printf("unknown\n");
          break;
        case Z3_L_TRUE: {
          /* verify the result */
          assert(test_discr_function(&class1->clone, &class2->basis, &fun));
          char *str = fun_print(&fun);
          printf("%s\n", str);
          free(str);
          break;
        }
        }
      }
    }
  }
}

void script_maj_disrc_fun_two_layers(const char *fname, maj_layer_id id1, maj_layer_id id2) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);

  maj_lattice lattice;
  maj_lattice_read(fd, &lattice);

  const maj_layer *layer1 = maj_lattice_get_layer(&lattice, id1);
  assert(layer1 != NULL);
  const maj_layer *layer2 = maj_lattice_get_layer(&lattice, id2);
  assert(layer2 != NULL);
  
  worker(layer1, layer2);
  
  maj_lattice_free(&lattice);
  fclose(fd);
}

int main() {
  printf("script-maj-disrc-fun-two-layers:\n"); fflush(stdout);
  script_maj_disrc_fun_two_layers("data/all-maj.2016", 49, 50);
  printf("Ok.\n");
}

