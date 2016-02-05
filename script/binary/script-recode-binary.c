/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * @file        test-recode-binary.c
 * @brief       Recode 2013 binary files to new serialization format (2016).
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/bin-maj-lattice-2013.h"
#include "binary/bin-maj-lattice.h"

void test_maj_layer_read_classes_2013() {
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

void test_maj_lattice_read_2013() {
  maj_lattice lattice;
  maj_lattice_read_2013(51, "data/all_maj_cpp", "data/lattice2", &lattice);
  maj_lattice_free(&lattice);
}

/** `test_recode_binary` reads lattice in 2013 file format
 * and writes to 2016 format.
 */
void script_recode_binary()  {
  maj_lattice lattice;
  maj_lattice_read_2013(51, "data/all_maj_cpp", "data/lattice2", &lattice);
  FILE *fout = fopen("data/all-maj.2016", "wb");
  assert(fout != NULL);
  
  maj_lattice_write(fout, &lattice);
  
  maj_lattice_free(&lattice);
  fclose(fout);
}

void test_read_maj_lattice_2016(const char *fname) {
  FILE *fin = fopen(fname, "rb");
  assert(fin != NULL);
  
  maj_lattice lattice;
  maj_lattice_read(fin, &lattice);
  
  maj_lattice_free(&lattice);
  fclose(fin);
}

int main() {
  printf("test that I can read layer in 2013 binary format: "); fflush(stdout);
  test_maj_layer_read_classes_2013();
  printf("Ok.\n");

  printf("test that I can read lattice in 2013 binary format: "); fflush(stdout);
  test_maj_lattice_read_2013();
  printf("Ok.\n");

  printf("recode binaries to new format: "); fflush(stdout);
  script_recode_binary();
  printf("Ok.\n");

  printf("test new binaries: "); fflush(stdout);
  test_read_maj_lattice_2016("data/all-maj.2016");
  printf("Ok.\n");
}
