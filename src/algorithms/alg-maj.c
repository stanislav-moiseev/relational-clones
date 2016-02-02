/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "algorithms/alg-maj.h"
#include "z3/gen-spec.h"
#include "binary/binary-2016.h"

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


int test_discr_function(const clone *clone1, const clone *clone2, const fun *fun) {
  /* check that the function preserves all predicates in the upper clone */
  for(clone_iterator it = clone_iterator_begin(clone1); !clone_iterator_end(clone1, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    if(!fun_preserves_pred(fun, &pred)) return 0;
  }
  
  /* check that there exists a predicate in the lower clone basis such that
   * the function does not preserve that predicate */
  int flag = 0;
  for(clone_iterator it = clone_iterator_begin(clone2); !clone_iterator_end(clone2, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    if(!fun_preserves_pred(fun, &pred)) { flag = 1; break; }
  }
  if(!flag) return 0;
  
  return 1;
}


/******************************************************************************/
/* Binary file-related part */

void write_classes_with_one_subclass_discr_fun(FILE *fd, const maj_lattice *lattice, maj_class * const *classes, size_t num_classes, const fun *funs) {
  uint64_write(fd, num_classes);
  for(maj_class * const *pclass = classes; pclass < classes + num_classes; ++pclass) {
    maj_class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct maj_class *subclass = maj_lattice_get_class(lattice, class->subclasses[0]);
    maj_class_id_write(fd, &class->id);
    maj_class_id_write(fd, &subclass->id);
    fun_write(fd, funs);
    ++funs;
  }  
}

void read_classes_with_one_subclass_discr_fun(FILE *fd, const maj_lattice *lattice, maj_class ***classes, size_t *num_classes, fun **funs) {
  *num_classes = uint64_read(fd);
  *classes = malloc(*num_classes * sizeof(maj_class *));
  assert(*classes != NULL);
  *funs = malloc(*num_classes * sizeof(fun));
  assert(*funs != NULL);
  for(size_t i = 0; i < *num_classes; ++i) {
    maj_class_id class_id, subclass_id;
    maj_class_id_read(fd, &class_id);
    maj_class_id_read(fd, &subclass_id);
    fun_read(fd, *funs + i);
    (*classes)[i] = maj_lattice_get_class(lattice, class_id);
  }  
}
