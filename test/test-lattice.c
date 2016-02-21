/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes a sublattice R3(2) containing the function 2x+2y.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "lattice.h"
#include "binary/bin-lattice.h"

void test_lattice(const char *lt_name) {
  lattice *lt = lattice_read(lt_name);
  assert(lt->num_layers == 55);
  assert(lt->num_classes == 2079040);
  
  size_t num_classes = 0;
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);

    /* test class positions */
    class_pos cpos = 0;
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);
      assert(c->lidx == lidx);
      assert(c->cpos == cpos);
      ++cpos;
    }

    num_classes += lr->num_classes;
  }
  
  assert(num_classes == lt->num_classes);

  lattice_free(lt);
}

int main() {
  printf("test-lattice:\t\t\t"); fflush(stdout);
  test_lattice("data/lattice.2016");
  printf("Ok.\n");
}
