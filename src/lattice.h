/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "class.h"


struct layer {
  uint64_t num_classes;
  class *classes;
};

typedef struct layer layer;

struct lattice {
  uint64_t num_layers;
  layer *layers;
};

typedef struct lattice lattice;

void layer_free(layer *layer);

/** `lattice_free` releases the memory allocated to store the layers.
 * The function also calls `class_free` on all classes.
 */
void lattice_free(lattice *lattice);

/** `lattice_get_class` returns a pointer to a class identified by
 * the given class id.
 */
class *lattice_get_class(const lattice *lattice, class_id id);

void lattice_find_classes_with_one_subclass(const lattice *lattice, class ***classes, uint64_t *num_classes);

#endif
