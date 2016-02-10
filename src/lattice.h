/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "clone.h"
#include "hashtable.h"
#include "globals.h"

/** Each class requires approx. 4KiB memory to store the predicate-clone closure
    table. */
struct class {
  const struct lattice *lattice;
  
  /* Some parent of the class.
   * A parent of `clone` is a clone `parent` such that there exists a
   * predicate `p` such that
   *    clone == <{p} ∪ parent>.
   *
   * We heuristically select the parent such that the different between the
   * current clone and the parent is the smallest. */
  struct class *parent;
  
  /* `diff_parent` is a difference between current clone and its parent;
   * it is used to optimize the computation of the closure of the union <p ∪ clone>. */
  clone diff_parent;

  /* A "basis" set of the clone in a sense that <basis> == clone
   * Note that the elements of the basis set are not necessary independent. */
  clone basis;
  clone clone;

  /* A predicate-clone closure table.
   * table[ar] maps a predicate `p` of arity `ar` to a result of closure
   *    <{p} ∪ clone> */
  struct class **children;
} __attribute__ ((aligned (32)));

typedef struct class class;

/** `class_alloc` allocates memory for a class and its closure table.
 * One should call `class_free` to release the memory.
 */
class *class_alloc(const struct lattice *lt);

void class_free(class *c);

/** `class_parent` returns some parent of the class.
 */
class *class_parent(const class *c);

/** `class_get_child` searches the predicate-clone closure table
 * for a clone the clone <{p} ∪ c> */
class *class_get_child(const class *c, const pred *p);

/** `class_set_child` sets the result of the closure <{p} ∪ parent> to be equal
 *  to `child`.  */
void class_set_child(class *parent, const pred *p, class *child);


/******************************************************************************/
struct lattice {
  /** Number of classes in the lattice. */
  size_t num_classes;
  
  /* A list of all lattice members (pointers to classes). */
  class **classes;
  /* The current capacity of `classes` array. We realloc the memory when the
   * space becomes exhausted. The reallocation can occur only when a new class
   * is inserted to the lattice. */
  size_t capacity;

  /* A hash table to support efficient clone membership test */
  hash_table *ht;

  predicate_numerator *pred_num;
};
typedef struct lattice lattice;


lattice *lattice_alloc();

void lattice_free(lattice *lt);

/** `lattice_insert_class` inserts a new class to the lattice.
 */
void lattice_insert_class(lattice *lt, class *c);

/** `lattice_lookup` efficiently searches the lattice for a class corresponding
 * to a given clone. If it's been found, the function returns the corresponding
 * class.
 * The function returns NULL if the clone is not present in the lattice.
 */
class *lattice_lookup(const lattice *lt, const clone *cl);

#endif

