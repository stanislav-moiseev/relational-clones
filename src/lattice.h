/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "algorithm/alg-closure-clone-pred.h"

typedef uint32_t layer_idx;
/** class_pos is the index of class withing the layer. */
typedef uint32_t class_pos;

struct class {
  /** Unique class identifier. */
  class_idx cidx;
  
  /** The layer which the clone belongs to and its position withing the layer. */
  layer_idx lidx;
  class_pos cpos;

  /** A closed set of predicates. */
  clone clone;

  /** Number of maximal proper subclasses for this class. */
  size_t num_maxsubs;

  /** A resizable array of maximal proper subclasses for this class. */
  class_idx *maxsubs;
  
  /** The current array capacity. */
  size_t cap_maxsubs;
}  __attribute__ ((aligned (32)));
typedef struct class class;

/** Allocate a new class and copy the class index and clone from `nd`. */
class *class_alloc(const ccpnode *nd);

void class_free(class *c);

void class_add_subclass(class *c, class_idx subclass_idx);

struct layer {
  layer_idx lidx;
  
  /** The layer size. */
  size_t num_classes;

  /** A resizable list of classes constituting the layer. */
  class_idx *classes;

  /** The current capacity of the `classes` list. */
  size_t cap_classes;
};
typedef struct layer layer;

layer *layer_alloc();

void layer_free(layer *lr);

void layer_add_class(layer *lr, class *c);

struct lattice {
  /** The number of layers in the lattice. */
  size_t num_layers;
  
  /** List of all layers, with layers[0] being the top layer (the layer
   * containing the top clone), layer[1] being the set of all precomplete
   * clones, layer[2] being the set of all maximal clones after removing
   * layer[0] and layer[1], and so on.
   *
   * We construct the layers iteratively, so we use a resizable vector of
   * pointer to classes. */
  layer **layers;

  /** The current capacity of the `layers` vector. */
  size_t cap_layers;

  /* List of all classes. */
  size_t num_classes;
  class **classes;
};
typedef struct lattice lattice;

static inline class *lattice_get_class(const lattice *lt, class_idx cidx) {
  assert(cidx < lt->num_classes);
  return lt->classes[cidx];
}

lattice *lattice_alloc();

void lattice_free(lattice *lt);

void lattice_add_layer(lattice *lt, layer *lr);

void lattice_load_classes_from_ccplt(lattice *lt, const ccplt *ccplt);

/** `lattice_construct_layers` constructs all layers.
 */
void lattice_construct_layers(lattice *lt, const ccplt *ccplt);

/** `lattice_construct_maximal_clones` for each clone computes all maximal
 * proper subclones.
 */
void lattice_construct_maximal_subclones(lattice *lt, const ccplt *ccplt);

/** `lattice_sort_maximal_subclones` arranged the maximal subclones of all
    clones in an order from higher layers to lower layers. */
void lattice_sort_maximal_subclones(lattice *lt);

#endif
