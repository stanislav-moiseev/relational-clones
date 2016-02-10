/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure.h"
#include "closure/closure-straightforward.h"
#include "closure/closure-two-preds.h"
#include "algorithms.h"

/******************************************************************************/
/** Lattice of all clones containing a majority operation */

void find_classes_with_one_subclass(const maj_lattice *lattice, maj_class ***classes, uint64_t *num_classes) {
  size_t capacity = 128;
  size_t size = 0;
  *classes = malloc(capacity * sizeof(maj_class *));
  assert(*classes);
  for(maj_layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    for(maj_class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
      if(class->num_subclasses == 1) {
        if(size == capacity) {
          capacity *= 2;
          *classes = realloc(*classes, capacity * sizeof(struct class *));
          assert(*classes);
        }
        (*classes)[size] = class;
        ++size;
      }
    }
  }
  *num_classes = size;
}

Z3_lbool find_discr_function(const maj_class *class, const struct maj_class *subclass, int max_fun_arity, fun *fun) {
  int fun_arity;
  Z3_lbool final_rc = Z3_L_FALSE;     /* the flag shows if we have proved that
                                         the discriminating function of current
                                         arity does not exist */
  for(fun_arity = 0; fun_arity <= max_fun_arity; ++fun_arity) {
    Z3_lbool rc = z3_find_discr_function(&class->basis, &class->clone, &subclass->clone, fun_arity, fun);
    if(rc == Z3_L_UNDEF) {
      /* we no longer have a proof that the discriminating function does not
         exist */
      final_rc = Z3_L_UNDEF;
    }
    if(rc == Z3_L_TRUE) {
      final_rc = Z3_L_TRUE;
      break;    /* do not search for functions of higher arities */
    }
  }
  return final_rc;
}

int clone_contains_majority(const clone *cl) {
  fun *majs;
  size_t num;
  min_majorities(&majs, &num);

  for(fun *f = majs; f < majs + num; ++f) {
    int flag = 1;
    for(clone_iterator it = clone_iterator_begin(cl); !clone_iterator_end(cl, &it); clone_iterator_next(&it)) {
      pred p = clone_iterator_deref(&it);
      if(!fun_preserves_pred(f, &p)) { flag = 0; break; }
    }
    if(flag) { free(majs); return 1; }
  }

  free(majs);
  return 0;
}

int pred_preserves_majority(const pred *p) {
  fun *majs;
  size_t num_majs;
  min_majorities(&majs, &num_majs);

  int flag = 0;
  for(fun *f = majs; f < majs + num_majs; ++f) {
    if(fun_preserves_pred(f, p)) { flag = 1; break; }
  }
  free(majs);
  return flag;
}

/******************************************************************************/
/** Lattice of all clones in P3(2) */

predicate_numerator *predicate_numerator_alloc() {
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

void lattice_construct_step(const closure_operator *clop, lattice *lt, const pred *p) {
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
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
      clone_copy(&current->basis, &child->basis);
      clone_insert_pred(&child->basis, p);
      clone_copy(&closure, &child->clone);
      lattice_insert_class(lt, child);
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
  /* start from a lattice containing just one clone */
  class *top = class_alloc(lt);
  closure_dummy_clone(clop, &top->clone);
  lattice_insert_class(lt, top);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  pred *uniq_preds;
  size_t uniq_sz;
  construct_closure_uniq_ess_preds(&uniq_preds, &uniq_sz);

  int idx = 0;
  /* iteratively construct new classes */
  for(pred *p = uniq_preds; p < uniq_preds + uniq_sz; ++p) {
    printf("%d\t %lu\n", idx, lt->num_classes);
    lattice_construct_step(clop, lt, p);
    ++idx;
    if(idx == 75) return;
  }

  free(uniq_preds);
}

