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

void test_clone_read_layer() {
  char *filename;
  sprintf(&filename, "data/all_maj_cpp/%d.bin", 50);
  FILE *fd = fopen(filename, "rb");
  assert(fd != NULL);
  
  size_t size;
  clone *clones;
  assert(clone_aread_layer(fd, &size, &clones));

  free(filename);
  free(clones);
  fclose(fd);
}

int main() {
  printf("test_clone_read_layer: ");
  test_clone_read_layer();
  printf("Ok.\n");
}

