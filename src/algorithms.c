/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "algorithms.h"
#include "z3/gen-spec.h"
#include "binary-2016.h"

void find_classes_with_one_subclass(const lattice *lattice, class ***classes, uint64_t *num_classes) {
  size_t capacity = 128;
  size_t size = 0;
  *classes = malloc(capacity * sizeof(class *));
  assert(*classes);
  for(layer *layer = lattice->layers; layer < lattice->layers + lattice->num_layers; ++layer) {
    for(class *class = layer->classes; class < layer->classes + layer->num_classes; ++class) {
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

Z3_lbool find_discr_function(const class *class, const struct class *subclass, int max_fun_arity, fun *fun) {
  int fun_arity;
  Z3_lbool final_rc = Z3_L_FALSE;     /* the flag shows if we have proved that
                                         the discriminating function of current
                                         arity does not exist */
  for(fun_arity = 0; fun_arity <= max_fun_arity; ++fun_arity) {
    Z3_lbool rc = z3_find_discr_function(class, subclass, fun_arity, fun);
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


/******************************************************************************/
/* Binary file-related part */

void write_classes_with_one_subclass_discr_fun(FILE *fd, const lattice *lattice, class * const *classes, size_t num_classes, const fun *funs) {
  uint64_write(fd, num_classes);
  for(class * const *pclass = classes; pclass < classes + num_classes; ++pclass) {
    class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct class *subclass = lattice_get_class(lattice, class->subclasses[0]);
    class_id_write(fd, &class->id);
    class_id_write(fd, &subclass->id);
    fun_write(fd, funs);
    ++funs;
  }  
}

void read_classes_with_one_subclass_discr_fun(FILE *fd, const lattice *lattice, class ***classes, size_t *num_classes, fun **funs) {
  *num_classes = uint64_read(fd);
  *classes = malloc(*num_classes * sizeof(class *));
  assert(*classes != NULL);
  *funs = malloc(*num_classes * sizeof(fun));
  assert(*funs != NULL);
  for(size_t i = 0; i < *num_classes; ++i) {
    class_id class_id, subclass_id;
    class_id_read(fd, &class_id);
    class_id_read(fd, &subclass_id);
    fun_read(fd, *funs + i);
    (*classes)[i] = lattice_get_class(lattice, class_id);
  }  
}
