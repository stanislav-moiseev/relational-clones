/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "maj-lattice.h"

void majclass_free(majclass *class) {
  if(class->subclasses) {
    free(class->subclasses);
    class->subclasses = NULL;
  }
}

void majclass_print_verbosely(FILE *fd, const majclass *class) {
  fprintf(fd, "class %2d:%-6d\n", class->id.layer_id, class->id.class_id);
  fprintf(fd, "class basis:\n");
  clone_print_verbosely(fd, &class->basis);
  fprintf(fd, "class clone:\n");
  clone_print_verbosely(fd, &class->clone);
}

void majlayer_free(majlayer *layer) {
  for(majclass *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    majclass_free(class);
  }
  free(layer->classes);
}

void majlattice_free(majlattice *lattice) {
  for(majlayer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    majlayer_free(layer);
  }
  free(lattice->layers);
  hashtable_free(lattice->ht);
  free(lattice);
}

majclass *majlattice_get_class(const majlattice *lattice, majclass_id id) {
  if(id.layer_id < lattice->num_layers) {
    if(id.class_id < lattice->layers[id.layer_id].num_classes) {
      majclass *class = &lattice->layers[id.layer_id].classes[id.class_id];
      assert(class->id.layer_id == id.layer_id && class->id.class_id == id.class_id);
      return class;
    }
  }
  return NULL;
}

majlayer *majlattice_get_layer(const majlattice *lattice, majlayer_id id) {
  if(id < lattice->num_layers) {
    majlayer *layer = lattice->layers + id;
    assert(layer->id = id);
    return layer;
  }
  return NULL;
}

int majlattice_member(const majlattice *lattice, const clone *cl) {
  return majlattice_lookup(lattice, cl) != NULL;
}

majclass *majlattice_lookup(const majlattice *lt, const clone *cl) {
  return hashtable_lookup(lt->ht, cl);
}



void majlattice_classes_with_one_subclass(const majlattice *lattice, majclass ***classes, uint64_t *num_classes) {
  size_t capacity = 128;
  size_t size = 0;
  *classes = malloc(capacity * sizeof(majclass *));
  assert(*classes);
  for(majlayer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    for(majclass *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
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

