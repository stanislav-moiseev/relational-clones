/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure.h"
#include "binary/bin-common.h"
#include "binary/bin-closure-two-preds.h"

void construct_closure_two_preds(const char *fout_name) {
  closure_table_two_preds *table = closure_table_two_preds_alloc();
  closure_table_two_preds_construct(table);

  FILE *fout = fopen(fout_name, "wb");
  assert(fout);
  closure_two_preds_write(fout, table);

  closure_table_two_preds_free(table);
  fclose(fout);
}

void read_closure_two_preds(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  closure_table_two_preds *table = closure_table_two_preds_alloc();
  closure_two_preds_read(fd, table);

  closure_table_two_preds_free(table);
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
