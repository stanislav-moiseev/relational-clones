/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_MAJ_H
#define LATTICE_MAJ_H

#include "clone.h"

/** `maj_class_id` is a unique class identifier.
 */
struct maj_class_id {
  uint32_t layer_id;
  /* class number withing a layer */
  uint32_t class_id;
};
typedef struct maj_class_id maj_class_id;

struct maj_class {
  maj_class_id id;
  clone basis;
  clone clone;
  uint64_t num_subclasses;
  maj_class_id *subclasses;
};

typedef struct maj_class maj_class;

/** `maj_class_free` releases the memory allocated to store the list of 
 * subclasses.
 */
void maj_class_free(maj_class *class);

/** `maj_class_print_verbosely` writes
 *   1) a list of all basis predicates of the class `class`.
 *   2) a list of all predicates from the `class->clone`.
 */
void maj_class_print_verbosely(FILE *fd, const maj_class *class);

typedef uint32_t maj_layer_id;

struct maj_layer {
  maj_layer_id id;
  uint64_t num_classes;
  maj_class *classes;
};

typedef struct maj_layer maj_layer;

struct maj_lattice {
  uint64_t num_layers;
  maj_layer *layers;
};

typedef struct maj_lattice maj_lattice;

void maj_layer_free(maj_layer *layer);

/** `maj_lattice_free` releases the memory allocated to store the layers.
 * The function also calls `maj_class_free` on all classes.
 */
void maj_lattice_free(maj_lattice *lattice);

/** `maj_lattice_get_class` returns a pointer to a class identified by
 * the given class id.
 */
maj_class *maj_lattice_get_class(const maj_lattice *lattice, maj_class_id id);

maj_layer *maj_lattice_get_layer(const maj_lattice *lattice, maj_layer_id id);


/******************************************************************************/
/** binary file related functionality */

void maj_class_id_write(FILE *fd, const maj_class_id *id);

/** `maj_lattice_write` writes the lattice to binary file.
 */
void maj_lattice_write(FILE *fd, const maj_lattice *lattice);

void maj_class_id_read(FILE *fd, maj_class_id *id);

/** `maj_lattice_read` reads the lattice from binary file.
 */
void maj_lattice_read(FILE *fd, maj_lattice *lattice);

#endif
