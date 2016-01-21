/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "pred.h"
#include "utils.h"
#include "clone.h"
#include "binary.h"
#include "lattice.h"

void test_layer_read_classes() {
  char *filename;
  asprintf(&filename, "data/all_maj_cpp/%d.bin", 50);
  FILE *fd = fopen(filename, "rb");
  assert(fd != NULL);
  
  size_t size;
  class *classes;
  layer_aread_classes(fd, 50, &classes, &size);

  free(filename);
  free(classes);
  fclose(fd);
}

void test_lattice_read() {
  lattice lattice;
  lattice_read("data/all_maj_cpp", 51, "data/lattice2", &lattice);
  lattice_free(&lattice);
}

int main() {
  printf("test_layer_read_classes: ");
  test_layer_read_classes();
  printf("Ok.\n");

  printf("test_lattice_read: ");
  test_lattice_read();
  printf("Ok.\n");
}

