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

void construct_closure_two_uniq_preds(const char *fout_name) {
  time_t t0 = time(NULL);
  printf("construct-closure-two-uniq-preds: "); fflush(stdout);
  closure_table_two_preds *table = closure_table_two_preds_alloc();
  closure_table_two_preds_construct(table);
  printf("%.2f min. Ok.\n", difftime(time(NULL), t0) / 60.);

  printf("writing \"%s\"...", fout_name); fflush(stdout);
  FILE *fout = fopen(fout_name, "wb");
  assert(fout);
  closure_two_preds_write(fout, table);
  printf("\t\tOk.\n");

  closure_table_two_preds_free(table);
  fclose(fout);
}

void read_closure_two_uniq_preds(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  closure_table_two_preds *table = closure_table_two_preds_alloc();
  closure_two_preds_read(fd, table);

  closure_table_two_preds_free(table);
  fclose(fd);
}

int main() {
  construct_closure_two_uniq_preds("output/closure-two-uniq-preds.2016");

  time_t t1 = time(NULL);
  printf("read-closure-two-uniq-preds: "); fflush(stdout);
  read_closure_two_uniq_preds("output/closure-two-uniq-preds.2016");
  printf("%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.);
}
