/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "lattice.h"
#include "fast-hash/fasthash.h"

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

static uint32_t clone_hash(const void *cl) {
  return fasthash32(cl, sizeof(clone), 0);
}

static int class_eq_clone(const void *c1, const void *c2) {
  return clone_eq((const clone *)c1, (const clone *)c2);
}

lattice *lattice_alloc() {
  lattice *lt = malloc(sizeof(lattice));
  assert(lt);
  
  lt->num_classes    = 0;
  lt->capacity       = 4e6;
  lt->classes        = malloc(lt->capacity * sizeof(class *));
  lt->ht             = hash_table_alloc(lt->capacity, clone_hash, class_eq_clone);
  
  return lt;
}

void lattice_free(lattice *lt) {
  for(class **c = lt->classes; c < lt->classes + lt->num_classes; ++c) {
    class_free(*c);
  }
  free(lt->classes);
  hash_table_free(lt->ht);
}

void lattice_insert_class(lattice *lt, class *c) {
  if(lt->num_classes == lt->capacity) {
    lt->capacity *= 2;
    lt->classes = realloc(lt->classes, lt->capacity);
    assert(lt->classes);
  }

  lt->classes[lt->num_classes] = c;
  ++lt->num_classes;

  hash_table_insert(lt->ht, &c->clone, c);
}

class *lattice_lookup(const lattice *lt, const clone *cl) {
  return hash_table_lookup(lt->ht, cl);
}
