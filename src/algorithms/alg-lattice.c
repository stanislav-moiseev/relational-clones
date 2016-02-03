/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "alg-closure.h"
#include "alg-lattice.h"

class *class_alloc() {
  class *c = malloc(sizeof(class));
  assert(c);
  
  c->parent = NULL;
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

static void construct_uniq_ess_preds(pred **_uniq_preds, size_t *_uniq_sz) {
  /* compute the closure of all essential predicates */
  clone ess_preds;
  uint32_t max_arity = 2;
  all_essential_predicates(&ess_preds, max_arity);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  size_t uniq_sz = 0;
  pred uniq_preds[clone_cardinality(&ess_preds)];
  clone uniq_closures[clone_cardinality(&ess_preds)];

  for(clone_iterator it = clone_iterator_begin(&ess_preds); !clone_iterator_end(&ess_preds, &it); clone_iterator_next(&it)) {
    pred p = clone_iterator_deref(&it);
    clone p_closure;
    closure_one_pred(&p, &p_closure);

    int j;
    for(j = 0; j < uniq_sz; ++j) {
      if(clone_eq(&p_closure, &uniq_closures[j])) break;
    }
    
    /* if not found, add to the list of unique clones */
    if(j == uniq_sz) {
      uniq_preds[uniq_sz] = p;
      clone_copy(&p_closure, &uniq_closures[uniq_sz]);
      ++uniq_sz;
    }
  }

  /* copy the result */
  *_uniq_preds = malloc(uniq_sz * sizeof(pred));
  assert(_uniq_preds);
  memcpy(*_uniq_preds, uniq_preds, uniq_sz * sizeof(pred));
  *_uniq_sz = uniq_sz;
}

void lattice_construct_step(lattice *lt, const pred *p) {
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *parent = *cp;

    /* add the predicate to the parent class and compute a closure */
    clone closure;
    closure_pred_clone(p, &parent->clone, &closure);

    /* test if we've constructed a new clone */
    class *child = lattice_lookup(lt, &closure);

    /* If we've constructed a new clone, add it to the lattice */
    if(child == NULL) {
      child = class_alloc();
      child->parent = parent;
      clone_copy(&parent->basis, &child->basis);
      clone_insert_pred(&child->basis, p);
      clone_copy(&closure, &child->clone);
      lattice_insert_class(lt, child);
    }
    
    /* link the parent and the child */
    class_set_child(parent, p, child);
  }
}

void latice_construct(lattice *lt) {
  lattice_init(lt);
  
  /* start from a lattice containing just one clone */
  class *top = class_alloc();
  closure_zero_preds(&top->clone);

  lattice_insert_class(lt, top);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  pred *uniq_preds;
  size_t uniq_sz;
  construct_uniq_ess_preds(&uniq_preds, &uniq_sz);

  int idx = 0;
  /* iteratively construct new classes */
  for(pred *p = uniq_preds; p < uniq_preds + uniq_sz; ++p) {
    printf("%d:\t %ld\n", idx, lt->num_classes);
    lattice_construct_step(lt, p);
    ++idx;
  }

  free(uniq_preds);
}
