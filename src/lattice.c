/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "lattice.h"

void layer_free(layer *layer) {
  for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    class_free(class);
  }
  free(layer->classes);
}

void lattice_free(lattice *lattice) {
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    layer_free(layer);
  }
  free(lattice->layers);
  lattice->layers = NULL;
}

class *lattice_get_class(const lattice *lattice, class_id id) {
  assert(id.layer_id <= lattice->num_layers);
  assert(id.class_id < lattice->layers[id.layer_id-1].num_classes);
  /* NB. id.layer_id - 1, because layer numbering starts from 1 */
  return &lattice->layers[id.layer_id-1].classes[id.class_id];
}

void lattice_find_classes_with_one_subclass(const lattice *lattice, class ***classes, uint64_t *num_classes) {
  size_t capacity = 128;
  size_t size = 0;
  *classes = malloc(capacity * sizeof(class *));
  assert(*classes);
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
      if(class->num_subclasses == 1) {
        if(size == capacity) {
          capacity *= 2;
          *classes = realloc(*classes, capacity * sizeof(struct class *));
          assert(*classes);
        }
        (*classes)[size] = class;
        ++size;
      }
    }
  }
  *num_classes = size;
}
