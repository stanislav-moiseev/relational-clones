/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "lattice.h"

void lattice_free(lattice *lattice) {
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {   
    for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
      class_free(class);
    }
    free(layer->classes);
  }
  free(lattice->layers);
  lattice->layers = NULL;
}

class *lattice_get_class(const lattice *lattice, class_id id) {
  assert(id.layer_id < lattice->num_layers);
  assert(id.class_id < lattice->layers[id.layer_id-1].num_classes);
  /* NB. id.layer_id - 1, because layer numbering starts from 1 */
  return &lattice->layers[id.layer_id-1].classes[id.class_id];
}
