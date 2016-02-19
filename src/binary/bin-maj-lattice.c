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

void majclass_id_write(FILE *fd, const majclass_id *id) {
  uint32_write(fd, id->layer_id);
  uint32_write(fd, id->class_id);
}

void majclass_write(FILE *fd, const majclass *class) {
  majclass_id_write(fd, &class->id);
  clone_write(fd, &class->basis);
  clone_write(fd, &class->clone);
  uint64_write(fd, class->num_subclasses);
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    majclass_id_write(fd, class->subclasses + i);
  }
}

void majlayer_write(FILE *fd, const majlayer *layer) {
  uint64_write(fd, layer->id);
  uint64_write(fd, layer->num_classes);
  for(majclass *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    majclass_write(fd, class);
  }
}

void majlattice_write(FILE *fd, const majlattice *lattice) {
  uint64_write(fd, lattice->num_layers);
  for(majlayer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    majlayer_write(fd, layer);
  }
}


/******************************************************************************/
/** READ part */

void majclass_id_read(FILE *fd, majclass_id *id) {
  id->layer_id = uint32_read(fd);
  id->class_id = uint32_read(fd);
}

void majclass_read(FILE *fd, majclass *class) {
  majclass_id_read(fd, &class->id);
  clone_read(fd, &class->basis);
  clone_read(fd, &class->clone);
  class->num_subclasses = uint64_read(fd);
  class->subclasses     = malloc(class->num_subclasses * sizeof(struct majclass_id));
  for(size_t i = 0; i < class->num_subclasses; ++i) {
    majclass_id_read(fd, class->subclasses + i);
  }
}

void majlayer_read(FILE *fd, majlayer *layer, hashtable *ht) {
  layer->id          = uint64_read(fd);
  layer->num_classes = uint64_read(fd);
  layer->classes     = malloc(layer->num_classes * sizeof(struct majclass));
  for(majclass *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    majclass_read(fd, class);
    hashtable_insert(ht, &class->clone, class);
  }
}

majlattice *majlattice_read(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  majlattice *lattice = malloc(sizeof(majlattice));

  lattice->num_layers = uint64_read(fd);
  lattice->layers     = malloc(lattice->num_layers * sizeof(struct majlayer));
  lattice->ht         = hashtable_alloc(2<<20, clone_hash, (int (*)(const void *, const void *))clone_eq);
  for(majlayer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    majlayer_read(fd, layer, lattice->ht);
  }
  
  fclose(fd);
  return lattice;
}
