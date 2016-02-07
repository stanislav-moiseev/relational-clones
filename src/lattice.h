/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "clone.h"
#include "hashtable.h"

/** Each class requires approx. 4KiB memory */
struct class {
  const struct lattice *lattice;
  
  /* Some parent of the class.
   * We heuristically select the parent such that the different between the
   * current clone and the parent is the smallest. */
  struct class *parent;
  
  /* diff_parent is a difference between current clone and its parent;
   * it is used when computing the closure of the union <p ∪ clone> */
  clone diff_parent;

  clone basis;
  clone clone;

  /* table[ar] maps a predicate `p` of arity `ar` to a result of closure
   * <clone ∪ {p}> */
  struct class **children;
};

typedef struct class class;


class *class_alloc(const struct lattice *lt);

void class_free(class *c);

class *class_parent(const class *c);

class *class_get_child(const class *c, const pred *p);

void class_set_child(class *parent, const pred *p, class *child);

struct lattice {
  size_t num_classes;
  size_t capacity;
  
  /* a list of pointers to classes */
  class **classes;

  /* a hash table to support efficient clone membership test */
  hash_table *ht;

  /* uniq_preds maps a predicate index to the predicate */
  size_t uniq_sz;
  pred *uniq_preds;
  /* reverse index: uniq_pred_idx maps a predicate to its index */
  size_t *uniq_pred_idx[3];
};

typedef struct lattice lattice;

/** `uniq` is the set of all closure-unique essential predicates.
 */
lattice *lattice_alloc();

void lattice_free(lattice *lt);

void lattice_insert_class(lattice *lt, class *c);

class *lattice_lookup(const lattice *lt, const clone *cl);

#endif

