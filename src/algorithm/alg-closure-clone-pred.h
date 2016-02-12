/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "clone.h"
#include "hashtable.h"
#include "globals.h"
#include "closure.h"

/** Each class requires approx. 2KiB memory to store the predicate-clone closure
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
  
  /* `diff_parent` is a difference between current clone and its parent.
   * It is used to optimize the computation of the closure of the union
   * <p ∪ clone>. */
  clone diff_parent;

  /* A generator of the clone is a set of predicates such that
   *    <generator> == clone.
   *
   * The generator reflects the way how the clone was constructed. Given that
   * for each predicate clone there can be many generator; the exact contents of
   * the generator is determined by the lattice construction procedure and
   * depends on the implementation. The elements of the generator are not
   * necessary independent. */
  clone generator;

  /* A closed set of predicates, a closure of the generator. */
  clone clone;

  /* A clone-predicate closure table. table[ar] maps a predicate `p` of arity
   * `ar` to a result of closure <{p} ∪ this_clone>
   *
   * To minimize the memory consumption, but store only a part of the table for
   * a minimal set of 250 closure-unique predicates here (except one "dummy"
   * predicate zero(0)). The exact predicates and their numbering scheme is
   * determined by the lattice predicate numerator. */
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

  /* A hash table to support efficient clone membership test.
   * See `lattice_lookup` */
  hash_table *ht;

  /* A structure that enumerates all closure-unique predicates with natural
   * numbers (pred_idx_t). The numbering is used in clone-predicate closure
   * table. */
  struct predicate_numerator *pred_num;
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


/******************************************************************************/
typedef size_t pred_idx_t;

struct predicate_numerator {
  /* Number of predicates. */
  size_t uniq_sz;
  
  /* uniq_preds maps a predicate index to the predicate. */
  pred *uniq_preds;
  
  /* reverse index: uniq_pred_idx[ar] maps a predicate of arity `ar` to its index. */
  pred_idx_t *uniq_pred_idx[3];
};
typedef struct predicate_numerator predicate_numerator;

predicate_numerator *predicate_numerator_alloc();

void predicate_numerator_free(predicate_numerator *pred_num);

static inline pred_idx_t pred_idx(predicate_numerator *pred_num, const pred *p) {
  assert(p->arity <= 2);
  return pred_num->uniq_pred_idx[p->arity][p->data];
}

static inline pred idx_pred(predicate_numerator *pred_num, size_t idx) {
  assert(idx < pred_num->uniq_sz);
  return pred_num->uniq_preds[idx];
}


/******************************************************************************/
/** Lattice of all clones in R3(2) */

/** The main algorithm.
 * Construct the lattice R3(2) of predicates of arity <= 2.
 */
void latice_construct(const closure_operator *clop, lattice *lt);

#endif

