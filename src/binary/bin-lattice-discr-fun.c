/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "bin-common.h"
#include "bin-lattice-discr-fun.h"

void lattice_discr_fun_write(const char *fout, const discrfun *dfs, size_t size) {
  FILE *fd = fopen(fout, "wb");
  assert(fd && "cannot open file");

  uint64_write(fd, size);
  for(const discrfun *df = dfs; df < dfs + size; ++df) {
    uint32_write(fd, df->parent);
    uint32_write(fd, df->child);
    fun_write(fd, &df->fun);
  }
  
  fclose(fd);
}

void lattice_discr_fun_read(const char *fin, discrfun **dfs, size_t *size) {
  FILE *fd = fopen(fin, "rb");
  assert(fd && "cannot open file");

  *size = uint64_read(fd);
  *dfs  = malloc((*size) * sizeof(discrfun));
  for(discrfun *df = *dfs; df < *dfs + *size; ++df) {
    df->parent = uint32_read(fd);
    df->child  = uint32_read(fd);
    fun_read(fd, &df->fun);
  }

  fclose(fd);
}
