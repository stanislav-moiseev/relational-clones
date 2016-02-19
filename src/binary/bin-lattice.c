/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "binary/bin-common.h"
#include "binary/bin-lattice.h"

void class_write(FILE *fd, const class *c) {
  uint32_write(fd, c->cidx);
  uint32_write(fd, c->lidx);
  uint32_write(fd, c->cpos);
  clone_write(fd, &c->clone);
  uint64_write(fd, c->num_maxsubs);
  for(class_idx *sub = c->maxsubs; sub < c->maxsubs + c->num_maxsubs; ++sub) {
    uint32_write(fd, *sub);
  }
}

void lattice_write(const char *fname, const lattice *lt) {
  FILE *fd = fopen(fname, "wb");
  assert(fd);
  uint64_write(fd, lt->num_layers);
  uint64_write(fd, lt->num_classes);
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class_write(fd, *cp);
  }
  fclose(fd);
}


void class_read(FILE *fd, class *c) {
  c->cidx = uint32_read(fd);
  c->lidx = uint32_read(fd);
  c->cpos = uint32_read(fd);
  clone_read(fd, &c->clone);
  c->num_maxsubs = uint64_read(fd);
  c->cap_maxsubs = c->num_maxsubs;
  c->maxsubs = malloc(c->cap_maxsubs * sizeof(class_idx));
  for(class_idx *sub = c->maxsubs; sub < c->maxsubs + c->num_maxsubs; ++sub) {
    *sub = uint32_read(fd);
  }
}

lattice *lattice_read(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  lattice *lt = malloc(sizeof(lattice));
  lt->num_layers  = uint64_read(fd);
  lt->layers      = NULL; /* TODO: construct layers */
  lt->cap_layers  = 0;
  lt->num_classes = uint64_read(fd);
  lt->classes     = aligned_alloc(32, lt->num_classes * sizeof(class *));
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    *cp = aligned_alloc(32, sizeof(class));
    class_read(fd, *cp);
  }
  fclose(fd);
  return lt;
}
