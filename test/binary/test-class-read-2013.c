/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/binary-2013.h"

void test_layer_read_classes() {
  char *filename;
  asprintf(&filename, "data/all_maj_cpp/%d.bin", 50);
  FILE *fd = fopen(filename, "rb");
  assert(fd != NULL);
  
  maj_layer layer;
  maj_layer_aread_classes_2013(fd, &layer);

  free(filename);
  maj_layer_free(&layer);
  fclose(fd);
}

void test_lattice_read() {
  maj_lattice lattice;
  maj_lattice_read_2013(51, "data/all_maj_cpp", "data/lattice2", &lattice);
  maj_lattice_free(&lattice);
}

int main() {
  printf("test-layer-read-classes: "); fflush(stdout);
  test_layer_read_classes();
  printf("Ok.\n");

  /* printf("test-lattice-read: "); fflush(stdout);*/
  /* test_lattice_read(); */
  /* printf("Ok.\n"); */
}

