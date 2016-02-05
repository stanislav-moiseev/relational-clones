/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/bin-maj-lattice.h"
#include "algorithms.h"

void test_size(const maj_lattice *lt) {
  assert(lt->num_layers == 51);

  size_t sz = 0;
  for(maj_layer *layer = lt->layers; layer < lt->layers + lt->num_layers; ++layer) {
    sz += layer->num_classes;
  }
  assert(sz == 1918040);
}

void test(const char *maj2013name) {
  FILE *fd = fopen(maj2013name, "rb");
  assert(fd != NULL);

  maj_lattice maj_lattice;
  maj_lattice_read(fd, &maj_lattice);
  
  /* run individual tests */
  test_size(&maj_lattice);
  
  maj_lattice_free(&maj_lattice);
  fclose(fd);
}

int main() {
  printf("test-maj-lattice:\n"); fflush(stdout);
  test("data/all-maj.2016");
  printf("Ok.\n");
}
