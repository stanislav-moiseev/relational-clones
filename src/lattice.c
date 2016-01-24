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
  if(id.layer_id < lattice->num_layers) {
    if(id.class_id < lattice->layers[id.layer_id].num_classes) {
      class *class = &lattice->layers[id.layer_id].classes[id.class_id];
      assert(class->id.layer_id == id.layer_id && class->id.class_id == id.class_id);
      return class;
    }
  }
  return NULL;
}

layer *lattice_get_layer(const lattice *lattice, layer_id id) {
  if(id < lattice->num_layers) {
    layer *layer = lattice->layers + id;
    assert(layer->id = id);
    return layer;
  }
  return NULL;
}
