/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "binary-2016.h"

void uint32_write(FILE *fd, uint32_t x) {
  assert(fwrite(&x, 4, 1, fd) == 1);
}

void uint64_write(FILE *fd, uint64_t x) {
  assert(fwrite(&x, 8, 1, fd) == 1);
}

uint32_t uint32_read(FILE *fd) {
  uint32_t x;
  assert(fread(&x, 4, 1, fd) == 1);
  return x;
}

uint64_t uint64_read(FILE *fd) {
  uint64_t x;
  assert(fread(&x, 8, 1, fd) == 1);
  return x;
}


/******************************************************************************/
/** WRITE part */

void fun_write(FILE *fd, const fun *fun) {
  uint32_write(fd, fun->arity);
  for(size_t offset = 0; offset < FUN_DATA_SIZE; ++offset) {
    uint64_write(fd, fun->data[offset]);
  }
}

void pred_write(FILE *fd, const pred *pred) {
  uint32_write(fd, K);
  uint32_write(fd, pred->arity);
  uint64_write(fd, pred->data);
}

void clone_write(FILE *fd, const clone *clone) {
  uint32_write(fd, clone->data0);
  uint32_write(fd, clone->data1);
  for(size_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    uint64_write(fd, clone->data2[offset]);
  }
}

void class_id_write(FILE *fd, const class_id *id) {
  uint32_write(fd, id->layer_id);
  uint32_write(fd, id->class_id);
}

void class_write(FILE *fd, const class *class) {
  class_id_write(fd, &class->id);
  clone_write(fd, &class->basis);
  clone_write(fd, &class->clone);
  uint64_write(fd, class->num_subclasses);
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    class_id_write(fd, class->subclasses + i);
  }
}

void layer_write(FILE *fd, const layer *layer) {
  uint64_write(fd, layer->id);
  uint64_write(fd, layer->num_classes);
  for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    class_write(fd, class);
  }
}

void lattice_write(FILE *fd, const lattice *lattice) {
  uint64_write(fd, lattice->num_layers);
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    layer_write(fd, layer);
  }
}


/******************************************************************************/
/** READ part */

void fun_read(FILE *fd, fun *fun) {
  fun->arity = uint32_read(fd);
  for(size_t offset = 0; offset < FUN_DATA_SIZE; ++offset) {
    fun->data[offset] = uint64_read(fd);
  }
}

void pred_read(FILE *fd, pred *pred) {
  assert(uint32_read(fd) == K);
  pred->arity = uint32_read(fd);
  pred->data = uint64_read(fd);
}

void clone_read(FILE *fd, clone *clone) {
  clone->data0 = uint32_read(fd);
  clone->data1 = uint32_read(fd);
  for(size_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    clone->data2[offset] = uint64_read(fd);
  }
}

void class_id_read(FILE *fd, class_id *id) {
  id->layer_id = uint32_read(fd);
  id->class_id = uint32_read(fd);
}

void class_read(FILE *fd, class *class) {
  class_id_read(fd, &class->id);
  clone_read(fd, &class->basis);
  clone_read(fd, &class->clone);
  class->num_subclasses = uint64_read(fd);
  class->subclasses     = malloc(class->num_subclasses * sizeof(struct class_id));
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    class_id_read(fd, class->subclasses + i);
  }
}

void layer_read(FILE *fd, layer *layer) {
  layer->id          = uint64_read(fd);
  layer->num_classes = uint64_read(fd);
  layer->classes     = malloc(layer->num_classes * sizeof(struct class));
  for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    class_read(fd, class);
  }
}

void lattice_read(FILE *fd, lattice *lattice) {
  lattice->num_layers = uint64_read(fd);
  lattice->layers     = malloc(lattice->num_layers * sizeof(struct layer));
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    layer_read(fd, layer);
  }
}
