/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef LATTICE_H
#define LATTICE_H

#include "clone.h"
#include "hashtable.h"

/** Each class requires approx. 4KiB memory */
struct class {
  /* the first parent of the class */
  struct class *parent;
  
  /* diff_parent is a difference between current clone and its parent;
   * it is used when computing the closure of the union <p ∪ clone> */
  clone diff_parent;

  clone basis;
  clone clone;

  /* table[ar] maps a predicate `p` of arity `ar` to a result of closure
   * <clone ∪ {p}> */
  struct class **children[3];
};

typedef struct class class;


class *class_alloc();

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
};

typedef struct lattice lattice;

lattice *lattice_alloc();

void lattice_free(lattice *lt);

void lattice_insert_class(lattice *lt, class *c);

class *lattice_lookup(const lattice *lt, const clone *cl);

#endif
