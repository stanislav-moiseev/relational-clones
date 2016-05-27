/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "isar/isar-spec.h"

static void isabelle_write_root(FILE *fd) {
  fprintf(fd, "session \"R3-2\" = \"HOL\" +\n");
  fprintf(fd, "  options [document = false]\n");
  fprintf(fd, "  theories\n");
  fprintf(fd, "    preds\n");
}

static void test_isar(FILE *isabelle_root_fd, FILE *preds_fd, FILE *ops_fd) {
  isabelle_write_root(isabelle_root_fd);
  isar_preds(preds_fd);
  isar_pred_operations(ops_fd);
}


int main() {
  FILE *isabelle_root_fd = fopen("output/R3_2/ROOT", "w");
  FILE *preds_fd  = fopen("output/R3_2/preds.thy", "w");
  FILE *ops_fd    = fopen("output/R3_2/ops.thy", "w");
  assert(isabelle_root_fd);
  assert(preds_fd);
  assert(ops_fd);
  
  test_isar(isabelle_root_fd, preds_fd, ops_fd);
}

