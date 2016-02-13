/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "algorithm/alg-closure-clone-pred.h"
#include "pred-essential.h"

class *class_alloc() {
  class *c = aligned_alloc(32, sizeof(class));
  assert(c);

  c->idx        = -1;
  c->parent     = NULL;
  c->children   = NULL;
  c->pidx_begin = -1;
  c->lt         = NULL;
  clone_init(&c->diff_parent);
  clone_init(&c->generator);
  clone_init(&c->clone);
  
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
  pred_idx_t pidx = pred_idx(c->lt->pred_num, p);
  assert(pidx >= c->pidx_begin);
  return lattice_get_class(c->lt, c->children[pidx - c->pidx_begin]);
}

void class_set_child(class *parent, const pred *p, class *child) {
  pred_idx_t pidx = pred_idx(parent->lt->pred_num, p);
  assert(pidx >= parent->pidx_begin);
  parent->children[pidx - parent->pidx_begin] = child->idx;
}

lattice *lattice_alloc() {
  lattice *lt = malloc(sizeof(lattice));
  assert(lt);
  lt->num_classes = 0;
  lt->capacity    = 2<<20;
  lt->classes     = malloc(lt->capacity * sizeof(class *));
  assert(lt->classes);
  lt->ht          = hashtable_alloc(2*lt->capacity, clone_hash, (int (*)(const void *, const void *))clone_eq);
  lt->pred_num    = NULL;
  return lt;
}

void lattice_free(lattice *lt) {
  for(class **c = lt->classes; c < lt->classes + lt->num_classes; ++c) {
    class_free(*c);
  }
  free(lt->classes);
  if(lt->ht) hashtable_free(lt->ht);
  if(lt->pred_num) predicate_numerator_free(lt->pred_num);
  free(lt);
}

void lattice_insert_class(lattice *lt, class *c, pred_idx_t pidx_begin) {
  /* resize class storage if needed */
  if(lt->num_classes == lt->capacity) {
    lt->capacity *= 2;
    lt->classes   = realloc(lt->classes, lt->capacity);
    assert(lt->classes);
  }

  /* initialize uninitialized class fields*/
  c->idx             = lt->num_classes;
  c->lt              = lt;
  c->pidx_begin      = pidx_begin;
  assert(pidx_begin <= lt->pred_num->uniq_sz);
  c->children        = malloc((lt->pred_num->uniq_sz - pidx_begin) * sizeof(class_idx)); 
  assert(c->children != NULL);
  memset(c->children, 0xFF, (lt->pred_num->uniq_sz - pidx_begin) * sizeof(class_idx));

  /* insert class to lattice */
  lt->classes[lt->num_classes] = c;
  hashtable_insert(lt->ht, &c->clone, c);

  ++lt->num_classes;
}

class *lattice_lookup(const lattice *lt, const clone *cl) {
  return hashtable_lookup(lt->ht, cl);
}

class *lattice_get_class(const lattice *lt, class_idx idx) {
  assert(idx < lt->num_classes && "class_idx too large");
  return lt->classes[idx];
}

predicate_numerator *predicate_numerator_construct() {
  predicate_numerator *pred_num = malloc(sizeof(predicate_numerator));
  assert(pred_num);
  
  /* construct index for closure-unique predicates */
  construct_closure_uniq_ess_preds(&pred_num->uniq_preds, &pred_num->uniq_sz);
  
  /* construct reverse index */
  for(uint32_t ar = 0; ar <= 2; ++ar) {
    uint64_t num = int_pow2(int_pow(K, ar));
    pred_num->uniq_pred_idx[ar] = malloc(num * sizeof(class *)); 
    assert(pred_num->uniq_pred_idx[ar] != NULL);
    memset(pred_num->uniq_pred_idx[ar], 0xFF, num * sizeof(class *));
  }
  for(pred *p = pred_num->uniq_preds; p < pred_num->uniq_preds + pred_num->uniq_sz; ++p) {
    size_t idx = 0;
    for(; idx < pred_num->uniq_sz; ++idx) {
      if(pred_eq(&pred_num->uniq_preds[idx], p)) break;
    }
    assert(idx < pred_num->uniq_sz);
    pred_num->uniq_pred_idx[p->arity][p->data] = idx;
  }
  
  return pred_num;
}

void predicate_numerator_free(predicate_numerator *pred_num) {
  free(pred_num->uniq_preds);
  for(int ar = 0; ar <=2; ++ar) {
    free(pred_num->uniq_pred_idx[ar]);
  }
  free(pred_num);
}

static void lattice_construct_step(const closure_operator *clop, lattice *lt, pred_idx_t pidx) {
  const pred *p = idx_pred(lt->pred_num, pidx);
  size_t cur_step_num_classes = lt->num_classes;
  for(class **cp = lt->classes; cp < lt->classes + cur_step_num_classes; ++cp) {
    class *current = *cp;
    
    /* if the current class contains the predicate to be added, skip it */
    if(clone_test_pred(&current->clone, p)) {
      class_set_child(current, p, current);
      continue;
    }

    /* compute the closure of the union {p} ∪ current */
    clone closure;
    if(current->parent == NULL) {
      /* if the current clone is the top clone, use a direct approach */
      clone clone_p;
      clone_init(&clone_p);
      clone_insert_pred(&clone_p, p);
      closure_clone_ex(clop, &current->clone, &clone_p, &closure);
    } else {
      /* if the current clone has a parent, compute the closure <{p} ∪ current>
       * using the result of the closure of `p` and its parent:
       * <{p}∪current> == <<{p}∪parent> ∪ (current\parent)> ==
       *               == <<{p}∪parent> ∪ (current\parent\<{p}∪parent>)> */
      
      /* parent_p == <{p}∪parent> */
      class *parent_p = class_get_child(current->parent, p);
      /* the closure <{p} ∪ parent> should have already been computed */
      assert(parent_p != NULL);
      /* tmp == (current\parent) \ <{p}∪parent> */
      clone tmp;
      clone_diff(&current->diff_parent, &parent_p->clone, &tmp);
      
      closure_clone_ex(clop, &parent_p->clone, &tmp, &closure);
    }

    /* test if we've constructed a new class */
    class *child = lattice_lookup(lt, &closure);
    assert(child != current);
    if(child == NULL) {
      /* if we've constructed a new class, add it to the lattice */
      child = class_alloc(lt);
      child->parent = current;
      clone_diff(&closure, &current->clone, &child->diff_parent);
      clone_copy(&current->generator, &child->generator);
      clone_insert_pred(&child->generator, p);
      clone_copy(&closure, &child->clone);
      lattice_insert_class(lt, child, pidx+1);
    } else {
      /* If we've found a new parent for current clone, check if the difference
       * between it and the clone is smaller than the current child->diff_parent.
       * We want to select the parent such that the different is the smallest.
       * This heuristics gives significant overall computation speed-up.
       *
       * We apply this heuristics for `current < child` only because on each step
       * the parents must be proceeded strictly before their children,
       * otherwise the closure of a child will depend on a not-yet-computed
       * closure of its parent */
      if(current < child) {
        size_t diff_card1 = clone_cardinality(&child->diff_parent);
        clone diff2;
        clone_diff(&closure, &current->clone, &diff2);
        size_t diff_card2 = clone_cardinality(&diff2);
        if(diff_card2 < diff_card1) {
          child->parent = current;
          clone_copy(&diff2, &child->diff_parent);
        }
      }
    }

    /* link the current class and the child class */
    class_set_child(current, p, child);
  }
}

void latice_construct(const closure_operator *clop, lattice *lt) {
  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  lt->pred_num = predicate_numerator_construct();

  /* start from a lattice containing just one clone */
  class *top = class_alloc(lt);
  closure_dummy_clone(clop, &top->clone);
  lattice_insert_class(lt, top, 0);
  
  /* iteratively construct new classes */
  for(pred_idx_t pidx = 0; pidx < lt->pred_num->uniq_sz; ++pidx) {
    lattice_construct_step(clop, lt, pidx);
    printf("%u\t %lu\n", pidx, lt->num_classes);
  }
}

