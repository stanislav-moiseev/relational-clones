/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

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


int test_discr_function(const class *class1, const class *class2, const fun *fun) {
  /* check that the function preserves all predicates in the upper clone */
  for(clone_iterator it = clone_iterator_begin(&class1->clone); !clone_iterator_end(&class1->clone, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    if(!fun_preserves_pred(fun, &pred)) return 0;
  }
  
  /* check that there exists a predicate in the lower class basis such that
   * the function does not preserve that predicate */
  int flag = 0;
  for(clone_iterator it = clone_iterator_begin(&class2->basis); !clone_iterator_end(&class2->basis, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    if(!fun_preserves_pred(fun, &pred)) { flag = 1; break; }
  }
  if(!flag) return 0;
  
  return 1;
}

static void clone_closure_two_essential_preds_construct_table(clone *(*table)[3][3]) {
  /* we insert these predicates to every clone */
  pred p_false, p_true, p_eq;
  pred_construct(0, "0", &p_false);
  pred_construct(0, "1", &p_true);
  pred_construct(2, "100010001", &p_eq);

  for(uint32_t ar1 = 0; ar1 <= 2; ++ar1) {
    for(uint32_t ar2 = 0; ar2 <= 2; ++ar2) {
      /* number of predicates of the given arity */
      uint64_t num1 = int_pow2(int_pow(K, ar1));
      uint64_t num2 = int_pow2(int_pow(K, ar2));
      
      (*table)[ar1][ar2] = malloc(num1 * num2 * sizeof(clone));
      assert((*table)[ar1][ar2] != NULL);
      memset((*table)[ar1][ar2], 0, num1 * num2 * sizeof(clone));
      
      for(uint64_t data1 = 0; data1 < num1; ++data1) {
        pred p1 = { .arity = ar1, .data = data1 };
        if(!pred_is_essential(&p1)) continue;
        for(uint64_t data2 = 0; data2 < num2; ++data2) {
          pred p2 = { .arity = ar2, .data = data2 };
          if(!pred_is_essential(&p2)) continue;
          
          clone cl;
          clone_init(&cl);
          clone_insert_pred(&cl, &p_false);
          clone_insert_pred(&cl, &p_true);
          clone_insert_pred(&cl, &p_eq);
          clone_insert_pred(&cl, &p1);
          clone_insert_pred(&cl, &p2);
          
          clone_closure(&cl, &(*table)[ar1][ar2][data1*num2 + data2]);
        }
      }
    }
  }
}

void clone_closure_two_preds(const pred *p1, const pred *p2, clone *closure) {
  assert(p1->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");
  assert(p2->arity <= 2 && "predicate operations have been implemented for pred->arity <= 2 only");

  static int table_ready = 0;
  static clone *table[3][3];
  if(!table_ready) {
    table_ready = 1;
    clone_closure_two_essential_preds_construct_table(&table);
  }

  /* add new predicates to `closure` */
  clone_union(table[p1->arity][p2->arity], closure, closure);
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
