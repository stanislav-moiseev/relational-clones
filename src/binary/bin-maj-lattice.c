/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "binary/bin-common.h"
#include "binary/bin-maj-lattice.h"

/******************************************************************************/
/** WRITE part */

void maj_class_id_write(FILE *fd, const maj_class_id *id) {
  uint32_write(fd, id->layer_id);
  uint32_write(fd, id->class_id);
}

void maj_class_write(FILE *fd, const maj_class *class) {
  maj_class_id_write(fd, &class->id);
  clone_write(fd, &class->basis);
  clone_write(fd, &class->clone);
  uint64_write(fd, class->num_subclasses);
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    maj_class_id_write(fd, class->subclasses + i);
  }
}

void maj_layer_write(FILE *fd, const maj_layer *layer) {
  uint64_write(fd, layer->id);
  uint64_write(fd, layer->num_classes);
  for(maj_class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    maj_class_write(fd, class);
  }
}

void maj_lattice_write(FILE *fd, const maj_lattice *lattice) {
  uint64_write(fd, lattice->num_layers);
  for(maj_layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    maj_layer_write(fd, layer);
  }
}


/******************************************************************************/
/** READ part */

void maj_class_id_read(FILE *fd, maj_class_id *id) {
  id->layer_id = uint32_read(fd);
  id->class_id = uint32_read(fd);
}

void maj_class_read(FILE *fd, maj_class *class) {
  maj_class_id_read(fd, &class->id);
  clone_read(fd, &class->basis);
  clone_read(fd, &class->clone);
  class->num_subclasses = uint64_read(fd);
  class->subclasses     = malloc(class->num_subclasses * sizeof(struct maj_class_id));
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    maj_class_id_read(fd, class->subclasses + i);
  }
}

void maj_layer_read(FILE *fd, maj_layer *layer, hashtable *ht) {
  layer->id          = uint64_read(fd);
  layer->num_classes = uint64_read(fd);
  layer->classes     = malloc(layer->num_classes * sizeof(struct maj_class));
  for(maj_class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    maj_class_read(fd, class);
    hashtable_insert(ht, &class->clone, class);
  }
}

maj_lattice *maj_lattice_read(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  maj_lattice *lattice = malloc(sizeof(maj_lattice));

  lattice->num_layers = uint64_read(fd);
  lattice->layers     = malloc(lattice->num_layers * sizeof(struct maj_layer));
  lattice->ht         = hashtable_alloc(2<<20, clone_hash, (int (*)(const void *, const void *))clone_eq);
  for(maj_layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    maj_layer_read(fd, layer, lattice->ht);
  }
  
  fclose(fd);
  return lattice;
}
