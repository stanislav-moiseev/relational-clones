/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "algorithms/alg-maj.h"
#include "z3/z3-search.h"
#include "binary/common.h"

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
