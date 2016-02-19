/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "maj-lattice.h"

void maj_class_free(maj_class *class) {
  if(class->subclasses) {
    free(class->subclasses);
    class->subclasses = NULL;
  }
}

void maj_class_print_verbosely(FILE *fd, const maj_class *class) {
  fprintf(fd, "class %2d:%-6d\n", class->id.layer_id, class->id.class_id);
  fprintf(fd, "class basis:\n");
  clone_print_verbosely(fd, &class->basis);
  fprintf(fd, "class clone:\n");
  clone_print_verbosely(fd, &class->clone);
}

void maj_layer_free(maj_layer *layer) {
  for(maj_class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    maj_class_free(class);
  }
  free(layer->classes);
}

void maj_lattice_free(maj_lattice *lattice) {
  for(maj_layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    maj_layer_free(layer);
  }
  free(lattice->layers);
  lattice->layers = NULL;
  hashtable_free(lattice->ht);
  lattice->ht = NULL;
}

maj_class *maj_lattice_get_class(const maj_lattice *lattice, maj_class_id id) {
  if(id.layer_id < lattice->num_layers) {
    if(id.class_id < lattice->layers[id.layer_id].num_classes) {
      maj_class *class = &lattice->layers[id.layer_id].classes[id.class_id];
      assert(class->id.layer_id == id.layer_id && class->id.class_id == id.class_id);
      return class;
    }
  }
  return NULL;
}

maj_layer *maj_lattice_get_layer(const maj_lattice *lattice, maj_layer_id id) {
  if(id < lattice->num_layers) {
    maj_layer *layer = lattice->layers + id;
    assert(layer->id = id);
    return layer;
  }
  return NULL;
}

int maj_lattice_member(const maj_lattice *lattice, const clone *cl) {
  return maj_lattice_lookup(lattice, cl) != NULL;
}

maj_class *maj_lattice_lookup(const maj_lattice *lt, const clone *cl) {
  return hashtable_lookup(lt->ht, cl);
}
