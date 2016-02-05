/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure.h"
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

/******************************************************************************/
/** Lattice of all clones in P3(2) */

static void construct_uniq_ess_preds(const closure_operator *clop, pred **_uniq_preds, size_t *_uniq_sz) {
  /* compute the closure of all essential predicates */
  pred *ess_preds;
  size_t num_ess_preds;
  uint32_t max_arity = 2;
  get_essential_predicates(max_arity, &ess_preds, &num_ess_preds);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  size_t uniq_sz = 0;
  pred uniq_preds[num_ess_preds];
  clone uniq_closures[num_ess_preds];

  for(pred *p = ess_preds; p < ess_preds + num_ess_preds; ++p) {
    clone p_closure;
    closure_one_pred(clop, p, &p_closure);

    int j;
    for(j = 0; j < uniq_sz; ++j) {
      if(clone_eq(&p_closure, &uniq_closures[j])) break;
    }
    
    /* if not found, add to the list of unique clones */
    if(j == uniq_sz) {
      uniq_preds[uniq_sz] = *p;
      clone_copy(&p_closure, &uniq_closures[uniq_sz]);
      ++uniq_sz;
    }
  }

  free(ess_preds);
  
  /* copy the result */
  *_uniq_preds = malloc(uniq_sz * sizeof(pred));
  assert(_uniq_preds);
  memcpy(*_uniq_preds, uniq_preds, uniq_sz * sizeof(pred));
  *_uniq_sz = uniq_sz;
}

void lattice_construct_step(const closure_operator *clop, lattice *lt, const pred *p) {
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *current = *cp;

    clone closure;
    if(current->parent == NULL) {
      /* compute the closure of the union {p} ∪ current */
      clone clone_p;
      clone_init(&clone_p);
      clone_insert_pred(&clone_p, p);
      clone_closure_ex(clop, &current->clone, &clone_p, &closure);
      
    } else {
      /* we compute the closure <{p} ∪ current> using the result of closure
       * of its parent and `p`. */
      class *parent_p = class_get_child(current->parent, p);
      /* that closure <{p} ∪ parent> should have already been computed */
      assert(parent_p != NULL);

      /* <{p} ∪ current> = <<{p} ∪ parent> ∪ (current\parent)> */
      clone_closure_ex(clop, &parent_p->clone, &current->diff_parent, &closure);
    }

    /* test if we've constructed a new class */
    class *child = lattice_lookup(lt, &closure);

    /* if we've constructed a new class, add it to the lattice */
    if(child == NULL) {
      child = class_alloc();
      child->parent = current;
      clone_diff(&closure, &current->clone, &child->diff_parent);
      clone_copy(&current->basis, &child->basis);
      clone_insert_pred(&child->basis, p);
      clone_copy(&closure, &child->clone);
      lattice_insert_class(lt, child);
    }
    
    /* link the current class and the child class */
    class_set_child(current, p, child);
  }
}

void latice_construct(const closure_operator *clop, lattice *lt) {
  lattice_init(lt);
  
  /* start from a lattice containing just one clone */
  class *top = class_alloc();
  closure_zero_preds(clop, &top->clone);

  lattice_insert_class(lt, top);

  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  pred *uniq_preds;
  size_t uniq_sz;
  construct_uniq_ess_preds(clop, &uniq_preds, &uniq_sz);

  int idx = 0;
  /* iteratively construct new classes */
  for(pred *p = uniq_preds; p < uniq_preds + uniq_sz; ++p) {
    printf("%d\t %ld\n", idx, lt->num_classes);
    lattice_construct_step(clop, lt, p);
    ++idx;
  }

  free(uniq_preds);
}

