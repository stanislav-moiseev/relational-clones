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

#include "binary-2013.h"
#include "binary-2016.h"

/** `test_recode_binary` reads lattice in 2013 file format
 * and writes to 2016 format.
 */
void test_recode_binary()  {
  lattice lattice;
  lattice_read_2013(51, "data/all_maj_cpp", "data/lattice2", &lattice);
  FILE *fout = fopen("data/all-maj.2016", "wb");
  assert(fout != NULL);
  
  lattice_write(fout, &lattice);
  
  lattice_free(&lattice);
  fclose(fout);
}

void test_read_binary_2016() {
  FILE *fin = fopen("data/all-maj.2016", "rb");
  assert(fin != NULL);
  
  lattice lattice;
  lattice_read(fin, &lattice);
  
  lattice_free(&lattice);
  fclose(fin);
}

int main() {
  printf("test-recode-binary: "); fflush(stdout);
  test_recode_binary();
  printf("Ok.\n");

  printf("test-read-new-inary: "); fflush(stdout);
  test_read_binary_2016();
  printf("Ok.\n");
}
