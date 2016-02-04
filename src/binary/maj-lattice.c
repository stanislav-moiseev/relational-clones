/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "binary/common.h"
#include "binary/maj-lattice.h"

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
  for(maj_layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    for(maj_class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
      if(clone_eq(cl, &class->clone)) return 1;
    }
  }
  return 0;
}

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

void maj_layer_read(FILE *fd, maj_layer *layer) {
  layer->id          = uint64_read(fd);
  layer->num_classes = uint64_read(fd);
  layer->classes     = malloc(layer->num_classes * sizeof(struct maj_class));
  for(maj_class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
    maj_class_read(fd, class);
  }
}

void maj_lattice_read(FILE *fd, maj_lattice *lattice) {
  lattice->num_layers = uint64_read(fd);
  lattice->layers     = malloc(lattice->num_layers * sizeof(struct maj_layer));
  for(maj_layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    maj_layer_read(fd, layer);
  }
}
