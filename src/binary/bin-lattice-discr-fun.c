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

void lattice_discr_fun_txt_read(const char *fin, discrfun **dfs, size_t *size) {
  FILE *fd = fopen(fin, "r");
  assert(fd && "cannot open file");

  size_t capacity = 4096;
  *dfs = malloc(capacity * sizeof(discrfun));
  assert(*dfs);
  *size = 0;

  for(;;) {
    class_idx parent, child;
    char fun_str[1024];
    int rc = fscanf(fd, "class %u (%*u:%*u) subclass %u (%*u:%*u) %s\n",
                    &parent, &child, fun_str);
    if(rc == EOF) break;
    assert(rc == 3);

    if(*size == capacity) {
      capacity *= 2;
      *dfs = realloc(*dfs, capacity * sizeof(discrfun));
    }
    discrfun *df = (*dfs) + *size;
    df->parent = parent;
    df->child  = child;
    fun_scan(fun_str, &df->fun);
    ++(*size);
  }

  fclose(fd);
}

