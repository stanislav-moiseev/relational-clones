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
  fprintf(fd, "    clones\n");
}

static void test_isar(const char *ccplt_fname,
                      FILE *isabelle_root_fd,
                      FILE *preds_fd,
                      FILE *clones_fd) {
  isabelle_write_root(isabelle_root_fd);
  isar_preds(preds_fd, "preds");
  isar_clones(ccplt_fname, clones_fd, "clones");
}

int main() {
  FILE *isabelle_root_fd = fopen("output/R3_2/ROOT", "w");
  FILE *preds_fd         = fopen("output/R3_2/preds.thy", "w");
  FILE *clones_fd        = fopen("output/R3_2/clones.thy", "w");
  assert(isabelle_root_fd);
  assert(preds_fd);
  assert(clones_fd);
  
  test_isar("data/closure-clone-pred.2016", isabelle_root_fd, preds_fd, clones_fd);

  fclose(isabelle_root_fd);
  fclose(preds_fd);
  fclose(clones_fd);
}

