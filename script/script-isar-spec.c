/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "globals.h"
#include "isar/isar-spec.h"


static void isabelle_write_root(FILE *fd) {
  fprintf(fd, "session \"R3_2\" = \"HOL\" +\n");
  fprintf(fd, "  options [document = false]\n");
  fprintf(fd, "  theories\n");
  fprintf(fd, "    common\n");
  fprintf(fd, "    preds\n");
  fprintf(fd, "    ops_perm\n");
  fprintf(fd, "    ops_conj\n");
  fprintf(fd, "    ops_comp\n");
}

static void test_isar(FILE *isabelle_root_fd,
                      FILE *preds_fd,
                      FILE *ops1_fd,
                      FILE *ops2_fd,
                      FILE *ops3_fd) {
  isabelle_write_root(isabelle_root_fd);
  isar_preds(preds_fd, "preds");
  isar_pred_ops_perm(ops1_fd, "ops_perm");
  isar_pred_ops_conj2(ops2_fd, "ops_conj");
  isar_pred_ops_comp(ops3_fd, "ops_comp");
}

int main() {
  FILE *isabelle_root_fd = fopen("output/R3_2/ROOT", "w");
  FILE *preds_fd         = fopen("output/R3_2/preds.thy", "w");
  FILE *ops1_fd          = fopen("output/R3_2/ops_perm.thy", "w");
  FILE *ops2_fd          = fopen("output/R3_2/ops_conj.thy", "w");
  FILE *ops3_fd          = fopen("output/R3_2/ops_comp.thy", "w");
  assert(isabelle_root_fd);
  assert(preds_fd);
  assert(ops1_fd);
  assert(ops2_fd);
  assert(ops3_fd);
  
  test_isar(isabelle_root_fd,
            preds_fd, ops1_fd, ops2_fd, ops3_fd);
}

