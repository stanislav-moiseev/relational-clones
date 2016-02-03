/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "binary/common.h"
#include "algorithms/alg-closure.h"
#include "binary/closure-two-preds.h"

void construct_closure_two_preds(const char *fout_name) {
  closure_two_preds_table table;
  clone_closure_two_preds_construct_table(&table);

  FILE *fout = fopen(fout_name, "wb");
  assert(fout);
  closure_two_preds_write(fout, &table);
  
  closure_two_preds_table_free(&table);
  fclose(fout);
}

void read_closure_two_preds(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  closure_two_preds_table table;
  closure_two_preds_read(fd, &table);
  
  closure_two_preds_table_free(&table);
  fclose(fd);
}

int main() {
  printf("construct-closure-two-preds: "); fflush(stdout);
  construct_closure_two_preds("output/closure-two-preds.2016");
  printf("Ok.\n");

  printf("read-closure-two-preds: "); fflush(stdout);
  read_closure_two_preds("output/closure-two-preds.2016");
  printf("Ok.\n");
}
