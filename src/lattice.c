/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "lattice.h"

class *class_alloc() {
  class *c = malloc(sizeof(class));
  assert(c);
  
  c->parent = NULL;
  clone_init(&c->diff_parent);
  clone_init(&c->basis);
  clone_init(&c->clone);
  
  for(uint32_t ar = 0; ar <= 2; ++ar) {
    uint64_t num = int_pow2(int_pow(K, ar));
    c->children[ar] = malloc(num * sizeof(class *));
    assert(c->children[ar] != NULL);
    memset(c->children[ar], 0, num * sizeof(class *));
  }

  return c;
}

void class_free(class *c) {
  for(uint32_t ar = 0; ar <= 2; ++ar) {
    free(c->children[ar]);
  }
  free(c);
}

class *class_parent(const class *c) {
  return c->parent;
}

class *class_get_child(const class *c, const pred *p) {
  assert(p->arity <= 2 && "classes support predicates of arity <= 2 only");
  return c->children[p->arity][p->data];
}

void class_set_child(class *parent, const pred *p, class *child) {
  assert(p->arity <= 2 && "classes support predicates of arity <= 2 only");
  parent->children[p->arity][p->data] = child;
}

void lattice_init(lattice *lt) {
  lt->num_classes = 0;
  lt->capacity    = 4e6;
  lt->classes     = malloc(lt->capacity * sizeof(class *));
}

void lattice_free(lattice *lt) {
  for(class **c = lt->classes; c < lt->classes + lt->num_classes; ++c) {
    class_free(*c);
    free(*c);
  }
  free(lt->classes);
}

void lattice_insert_class(lattice *lt, class *c) {
  if(lt->num_classes == lt->capacity) {
    lt->capacity *= 2;
    lt->classes = realloc(lt->classes, lt->capacity);
    assert(lt->classes);
  }

  lt->classes[lt->num_classes] = c;
  ++lt->num_classes;
}

class *lattice_lookup(const lattice *lt, const clone *cl) {
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(clone_eq(&c->clone, cl)) return c;
  }
  return NULL;
}
