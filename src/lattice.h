/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "closure/closure-clone-pred.h"

typedef uint32_t layer_idx;
/** class_pos is the index of class withing the layer. */
typedef uint32_t class_pos;

struct class {
  /** Unique class identifier. */
  class_idx cidx;
  
  /** The layer which the clone belongs to and its position withing the layer.
   *
   * Layer indices and class positions are either loaded from file or
   * constructed by `lattice_construct_layers`
   */
  layer_idx lidx;
  class_pos cpos;

  /** A closed set of predicates. */
  clone clone;

  /** Some generator for `clone`. */
  clone generator;

  /** Number of maximal proper subclasses for this class. */
  size_t num_maxsubs;

  /** A resizable list of maximal proper subclasses for this class.
   *
   * The list of maximal proper subclones is constructed by
   * `lattice_construct_maximal_subclones`.
   *
   * Normally, the list is sorted by `lattice_sort_maximal_subclones`.
   * Even though the sorting is not obligatory, but it is convenient for pretty
   * printing and when searching for a function discriminating a pair clone —
   * maximal subclone.
   */
  class_idx *maxsubs;
  
  /** The current array capacity. */
  size_t cap_maxsubs;
}  __attribute__ ((aligned (32)));
typedef struct class class;

/** Allocate a new class and copy clone `cl` to class. */
class *class_alloc(const clone *cl);

void class_free(class *c);

void class_add_subclass(class *c, class_idx subclass_idx);

struct layer {
  /** unique identifier. */
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

/** `layer_add_class` insert a given class to a given layer and assigns class
 * `lidx` and `cpos`.
 */
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

  /* A resizable array of all classes. */
  size_t num_classes;
  class **classes;
  size_t cap_classes;
};
typedef struct lattice lattice;

static inline class *lattice_get_class(const lattice *lt, class_idx cidx) {
  assert(cidx < lt->num_classes);
  class *c = lt->classes[cidx];
  assert(c->cidx == cidx);
  return c;
}

static inline layer *lattice_get_layer(const lattice *lt, layer_idx lidx) {
  assert(lidx < lt->num_layers);
  layer *lr = lt->layers[lidx];
  assert(lr->lidx == lidx);
  return lr;
}

lattice *lattice_alloc();

void lattice_free(lattice *lt);

/** `lattice_add_class` insert a given class layer and assigns a layer index to
 * it. */
void lattice_add_class(lattice *lt, class *c);

/** `lattice_add_layers` insert a given layers layer and assigns a layer index
 * to it. */
void lattice_add_layer(lattice *lt, layer *lr);


/** `lattice_construct_maximal_clones` for each clone computes all maximal
 * proper subclones.
 *
 * This algorithms is not efficient: for all clone it first searches all
 * proper subclones (all, not only direct), and then searches for maximal
 * clones among proper subclones.
 * If the lattice was constructed from `ccplt`, one can use a more efficient
 * implementation: `lattice_construct_maximal_subclones_ccplt`.
 */
void lattice_construct_maximal_subclones(lattice *lt);

/******************************************************************************/
/** Functions to deal with lattices initialized from a closure table
 * "clone + predicate"*/

/** `lattice_load_classes_from_ccplt` initializes the lattice as the set of
 * clones from `ccplt`. */
void lattice_load_classes_from_ccplt(lattice *lt, const ccplt *ccplt);

/** `lattice_construct_layers` constructs all layers.
 * See comments for `layers` member of `struct lattice`.
 *
 * NB. This function is applicable only to lattices having been initialized
 * previously from `ccplt`!
 */
void lattice_construct_layers_ccplt(lattice *lt, const ccplt *ccplt);

/** `lattice_construct_maximal_clones` for each clone computes all maximal
 * proper subclones.
 *
 * NB. This function is applicable only to lattices having been initialized
 * previously from `ccplt`!
 */
void lattice_construct_maximal_subclones_ccplt(lattice *lt, const ccplt *ccplt);

/** `lattice_sort_maximal_subclones` arranged the maximal subclones of all
 * clones in an order from higher layers (with smaller lidx) to lower layers
 * (with larger lidx).
 */
void lattice_sort_maximal_subclones(lattice *lt);

#endif
