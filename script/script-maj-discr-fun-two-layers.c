/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "z3/z3-search.h"
#include "binary/bin-maj-lattice.h"

void worker(const majlayer *layer1, const majlayer *layer2) {
  for(int i = 0; i < layer1->num_classes; ++i) {
    for(int j = 0; j < layer2->num_classes; ++j) {
      const majclass *class1 = layer1->classes + i;
      const majclass *class2 = layer2->classes + j;

      /* if one set is a subset of the other set */
      if(clone_subset(&class1->clone, &class2->clone)) {
        printf("class %2d:%-6d\t subclass %2d:%-6d\t ",
            class1->id.layer_id, class1->id.class_id,
            class2->id.layer_id, class2->id.class_id);
        fflush(stdout);

        fun fun;
        Z3_lbool rc = z3_find_discr_function(&class1->basis, &class1->clone, &class2->clone, 5, &fun);
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

void script_majdisrc_fun_two_layers(const char *fname, majlayer_id id1, majlayer_id id2) {
  majlattice *lattice =  majlattice_read(fname);

  const majlayer *layer1 = majlattice_get_layer(lattice, id1);
  assert(layer1 != NULL);
  const majlayer *layer2 = majlattice_get_layer(lattice, id2);
  assert(layer2 != NULL);
  
  worker(layer1, layer2);
  
  majlattice_free(lattice);
}

int main() {
  printf("script-maj-disrc-fun-two-layers:\n"); fflush(stdout);
  script_majdisrc_fun_two_layers("data/all-maj.2016", 49, 50);
  printf("Ok.\n");
}

