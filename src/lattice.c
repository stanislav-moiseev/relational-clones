/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "lattice.h"
#include "fast-hash/fasthash.h"

class *class_alloc(const lattice *lt) {
  class *c = malloc(sizeof(class));
  assert(c);

  c->lattice = lt;
  c->parent = NULL;
  clone_init(&c->diff_parent);
  clone_init(&c->basis);
  clone_init(&c->clone);
  
  c->children = malloc(lt->uniq_sz * sizeof(class *)); 
  assert(c->children != NULL);
  memset(c->children, 0, lt->uniq_sz * sizeof(class *));

  return c;
}

void class_free(class *c) {
  free(c->children);
  free(c);
}

class *class_parent(const class *c) {
  return c->parent;
}

class *class_get_child(const class *c, const pred *p) {
  assert(p->arity <= 2 && "classes support predicates of arity <= 2 only");
  size_t idx = c->lattice->uniq_pred_idx[p->arity][p->data];
  return c->children[idx];
}

void class_set_child(class *parent, const pred *p, class *child) {
  assert(p->arity <= 2 && "classes support predicates of arity <= 2 only");
  size_t idx = parent->lattice->uniq_pred_idx[p->arity][p->data];
  parent->children[idx] = child;
}

static uint32_t clone_hash(const void *cl) {
  return fasthash32(cl, sizeof(clone), 0);
}

static int class_eq_clone(const void *c1, const void *c2) {
  return clone_eq((const clone *)c1, (const clone *)c2);
}

void construct_uniq_ess_preds(pred **uniq_preds, size_t *uniq_sz);

lattice *lattice_alloc() {
  lattice *lt = malloc(sizeof(lattice));
  assert(lt);
  
  lt->num_classes    = 0;
  lt->capacity       = 2<<20;
  lt->classes        = malloc(lt->capacity * sizeof(class *));
  lt->ht             = hash_table_alloc(lt->capacity, clone_hash, class_eq_clone);

  /* construct index for closure-unique predicates */
  construct_uniq_ess_preds(&lt->uniq_preds, &lt->uniq_sz);
  
  /* construct reverse index */
  for(uint32_t ar = 0; ar <= 2; ++ar) {
    uint64_t num = int_pow2(int_pow(K, ar));
    lt->uniq_pred_idx[ar] = malloc(num * sizeof(class *)); 
    assert(lt->uniq_pred_idx[ar] != NULL);
    memset(lt->uniq_pred_idx[ar], 0xFF, num * sizeof(class *));
  }
  for(pred *p = lt->uniq_preds; p < lt->uniq_preds + lt->uniq_sz; ++p) {
    size_t idx = 0;
    for(; idx < lt->uniq_sz; ++idx) {
      if(pred_eq(&lt->uniq_preds[idx], p)) break;
    }
    assert(idx < lt->uniq_sz);
    lt->uniq_pred_idx[p->arity][p->data] = idx;
  }
  
  return lt;
}

void lattice_free(lattice *lt) {
  for(class **c = lt->classes; c < lt->classes + lt->num_classes; ++c) {
    class_free(*c);
  }
  free(lt->classes);
  hash_table_free(lt->ht);
  free(lt->uniq_preds);
  for(int ar = 0; ar <=2; ++ar) {
    free(lt->uniq_pred_idx[ar]);
  }
  free(lt);
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
