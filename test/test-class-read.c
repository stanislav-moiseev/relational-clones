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

void test_class_read_layer() {
  char *filename;
  asprintf(&filename, "data/all_maj_cpp/%d.bin", 50);
  FILE *fd = fopen(filename, "rb");
  assert(fd != NULL);
  
  size_t size;
  class *classes;
  assert(class_aread_layer(fd, &classes, &size));

  free(filename);
  free(classes);
  fclose(fd);
}

int main() {
  printf("test_class_read_layer: ");
  test_class_read_layer();
  printf("Ok.\n");
}

