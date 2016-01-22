/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "binary-2016.h"

static void write_uint32(FILE *fd, uint32_t x) {
  assert(fwrite(&x, 4, 1, fd) == 1);
}
static void write_uint64(FILE *fd, uint64_t x) {
  assert(fwrite(&x, 8, 1, fd) == 1);
}

static uint32_t read_uint32(FILE *fd) {
  uint32_t x;
  assert(fread(&x, 4, 1, fd) == 1);
  return x;
}
static uint64_t read_uint64(FILE *fd) {
  uint64_t x;
  assert(fread(&x, 8, 1, fd) == 1);
  return x;
}


/******************************************************************************/
/** WRITE part*/

/* void pred_write(FILE *fd, const pred *pred) { */
/*   write_uint32(fd, K); */
/*   write_uint32(fd, pred->arity); */
/*   write_uint64(fd, pred->data); */
/* } */

void class_id_write(FILE *fd, const class_id *id) {
  write_uint32(fd, id->layer_id);
  write_uint32(fd, id->class_id);
}

void clone_write(FILE *fd, const clone *clone) {
  write_uint32(fd, clone->data0);
  write_uint32(fd, clone->data1);
  for(size_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    write_uint64(fd, clone->data2[offset]);
  }
}

void class_write(FILE *fd, const class *class) {
  class_id_write(fd, &class->id);
  clone_write(fd, &class->basis);
  clone_write(fd, &class->clone);
  write_uint64(fd, class->num_subclasses);
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    class_id_write(fd, class->subclasses + i);
  }
}

void layer_write(FILE *fd, const layer *layer) {
  write_uint64(fd, layer->id);
  write_uint64(fd, layer->num_classes);
  for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    class_write(fd, class);
  }
}

void lattice_write(FILE *fd, const lattice *lattice) {
  write_uint64(fd, lattice->num_layers);
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    layer_write(fd, layer);
  }
}


/******************************************************************************/
/** READ part*/

/* void pred_read(FILE *fd, pred *pred) { */
/*   assert(read_uint32(fd) == K); */
/*   pred->arity = read_uint32(fd); */
/*   pred->data = read_uint64(fd); */
/* } */

void class_id_read(FILE *fd, class_id *id) {
  id->layer_id = read_uint32(fd);
  id->class_id = read_uint32(fd);
}

void clone_read(FILE *fd, clone *clone) {
  clone->data0 = read_uint32(fd);
  clone->data1 = read_uint32(fd);
  for(size_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    clone->data2[offset] = read_uint64(fd);
  }
}

void class_read(FILE *fd, class *class) {
  class_id_read(fd, &class->id);
  clone_read(fd, &class->basis);
  clone_read(fd, &class->clone);
  class->num_subclasses = read_uint64(fd);
  class->subclasses     = malloc(class->num_subclasses * sizeof(struct class_id));
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    class_id_read(fd, class->subclasses + i);
  }
}

void layer_read(FILE *fd, layer *layer) {
  layer->id          = read_uint64(fd);
  layer->num_classes = read_uint64(fd);
  layer->classes     = malloc(layer->num_classes * sizeof(struct class));
  for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    class_read(fd, class);
  }
}

void lattice_read(FILE *fd, lattice *lattice) {
  lattice->num_layers = read_uint64(fd);
  lattice->layers     = malloc(lattice->num_layers * sizeof(struct layer));
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    layer_read(fd, layer);
  }
}
