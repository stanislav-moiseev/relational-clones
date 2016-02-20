/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

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
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    uint64_write(fd, lattice_get_layer(lt, lidx)->num_classes);
  }
  uint64_write(fd, lt->num_classes);
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class_write(fd, *cp);
  }
  fclose(fd);
}


void class_read(FILE *fd, class *c) {
  c->cidx        = uint32_read(fd);
  c->lidx        = uint32_read(fd);
  c->cpos        = uint32_read(fd);
  clone_read(fd, &c->clone);
  c->num_maxsubs = uint64_read(fd);
  c->cap_maxsubs = c->num_maxsubs;
  c->maxsubs     = malloc(c->cap_maxsubs * sizeof(class_idx));
  for(class_idx *sub = c->maxsubs; sub < c->maxsubs + c->num_maxsubs; ++sub) {
    *sub = uint32_read(fd);
  }
}

lattice *lattice_read(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  lattice *lt = malloc(sizeof(lattice));

  /* Alloc memory for layers */
  lt->num_layers  = uint64_read(fd);
  lt->cap_layers  = lt->num_layers;
  lt->layers      = malloc(lt->cap_layers * sizeof(layer *));
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = malloc(sizeof(layer));
    lr->lidx        = lidx;
    /* Alloc memory for classes, but do not write class pointers. */
    lr->num_classes = uint64_read(fd);
    lr->cap_classes = lr->num_classes;
    lr->classes     = malloc(lr->cap_classes * sizeof(class_idx));
    /* Fill the list of classes with invalid class index (-1). */
    memset(lr->classes, 0xFF, lr->cap_classes * sizeof(class_idx));
    /* Put the layer to the lattice */
    lt->layers[lidx] = lr;
  }

  /* Read classes */
  lt->num_classes = uint64_read(fd);
  lt->classes     = aligned_alloc(32, lt->num_classes * sizeof(class *));
  layer_idx max_lidx = 0;       /* max layer index */
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    *cp = aligned_alloc(32, sizeof(class));
    class_read(fd, *cp);
    if((*cp)->lidx > max_lidx) max_lidx = (*cp)->lidx;
  }
  assert(lt->num_layers == max_lidx+1 && "layer with index >= the number of layers in the lattice.");

  /* Put classes to layers. */
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    layer *lr = lattice_get_layer(lt, c->lidx);
    assert(c->cpos < lr->num_classes && "class position >= the number of classes on the layer");
    /* Be sure that the class position is free. */
    assert(lr->classes[c->cpos] == -1 && "class position has been populated by another class already");
    /* Place the class withing the layer */
    lr->classes[c->cpos] = c->cidx;
  }

  /* Verify that all layers have been populated completely. */
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
     layer *lr = lattice_get_layer(lt, lidx);
     for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
       assert(*cidx != -1 && "class position has not been populated with a class");
     }
  }
  
  fclose(fd);
  return lt;
}
