/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef MAJLATTICE_H
#define MAJLATTICE_H

#include "clone.h"
#include "hashtable.h"

/** `majclass_id` is a unique class identifier.
 */
struct majclass_id {
  uint32_t layer_id;
  /* class number withing a layer */
  uint32_t class_id;
};
typedef struct majclass_id majclass_id;

struct majclass {
  majclass_id id;
  clone basis;
  clone clone;
  uint64_t num_subclasses;
  majclass_id *subclasses;
};

typedef struct majclass majclass;

/** `majclass_free` releases the memory allocated to store the list of 
 * subclasses.
 */
void majclass_free(majclass *class);

/** `majclass_print_verbosely` writes
 *   1) a list of all basis predicates of the class `class`.
 *   2) a list of all predicates from the `class->clone`.
 */
void majclass_print_verbosely(FILE *fd, const majclass *class);

typedef uint32_t majlayer_id;

struct majlayer {
  majlayer_id id;
  uint64_t num_classes;
  majclass *classes;
};

typedef struct majlayer majlayer;

struct majlattice {
  uint64_t num_layers;
  majlayer *layers;

  /** A hash table to support efficient clone search and membership test. */
  hashtable *ht;
};

typedef struct majlattice majlattice;

void majlayer_free(majlayer *layer);

/** `majlattice_free` releases the memory allocated to store the layers.
 * The function also calls `majclass_free` on all classes.
 */
void majlattice_free(majlattice *lattice);

/** `majlattice_get_class` returns a pointer to a class identified by
 * the given class id.
 */
majclass *majlattice_get_class(const majlattice *lattice, majclass_id id);

majlayer *majlattice_get_layer(const majlattice *lattice, majlayer_id id);

/** `majlattice_member` returns true if the lattice contains the clone.
 */
int majlattice_member(const majlattice *lt, const clone *cl);

/** `majlattice_lookup` efficiently searches the lattice for a clone `cl`.
 * If found, the function returns the corresponding majclass; otherwise
 * the function returns NULL.
 */
majclass *majlattice_lookup(const majlattice *lt, const clone *cl);

#endif
