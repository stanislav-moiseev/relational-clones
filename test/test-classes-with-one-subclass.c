/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary-2016.h"
#include "z3/gen-spec.h"

struct search_result {
  Z3_lbool rc;
  /* If rc==Z3_L_TRUE, the discriminating function of the smallest arity
   * will be stored here. */
  fun fun;
};

void write_class_subclass_discr_fun(FILE *fd, const class *class, const struct class *subclass, const struct search_result *res) {
  class_id_write(fd, &class->id);
  class_id_write(fd, &subclass->id);
  uint32_write(fd, res->rc);
  if(res->rc == Z3_L_TRUE) {
    fun_write(fd, &res->fun);
  }
}

void write_results(FILE *fd, const lattice *lattice, class **classes, size_t num_classes, struct search_result *res) {
  uint64_write(fd, num_classes);
  size_t idx = 0;
  for(class **pclass = classes; pclass < classes + num_classes; ++pclass) {
    class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct class *subclass = lattice_get_class(lattice, class->subclasses[0]);
    write_class_subclass_discr_fun(fd, class, subclass, res+idx);
    ++idx;
  }  
}

/** For each pair of two classes, we search for a discriminating function
 * of arity from 0 up to 5. */
void find_discr_function(FILE *flog, const class *class, const struct class *subclass, struct search_result *res) {
  int fun_arity;
  res->rc = Z3_L_FALSE; /* the flag shows if we have proved that the
                          discriminating function of current arity does not
                          exist */
  for(fun_arity = 0; fun_arity <= 5; ++fun_arity) {
    Z3_lbool rc = z3_find_discr_function(class, subclass, fun_arity, &res->fun);
    if(rc == Z3_L_UNDEF) {
      /* we no longer have a proof that the discriminating function does not
         exist */
      res->rc = Z3_L_UNDEF;
    }
    if(rc == Z3_L_TRUE) {
      res->rc = Z3_L_TRUE;
      break;    /* do not search for functions of higher arities */
    }
  }
}

void test_find_classes_with_one_subclass(const char *fname, const char *flogname, const char *foutname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);
  
  lattice lattice;
  lattice_read(fd, &lattice);
  fclose(fd);
  
  class **classes;
  uint64_t num_classes;
  lattice_find_classes_with_one_subclass(&lattice, &classes, &num_classes);

  struct search_result *res = malloc(num_classes * sizeof(struct search_result));
  assert(res != NULL);  
  
  FILE *flog = fopen(flogname, "w");
  assert(flog != NULL);

  size_t idx = 0;
  for(class **pclass = classes; pclass < classes + num_classes; ++pclass) {
    class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct class *subclass = lattice_get_class(&lattice, class->subclasses[0]);

    fprintf(flog, "%lu:\t class %2d:%-6d\t subclass %2d:%-6d\t ",
            idx,
            class->id.layer_id, class->id.class_id,
            subclass->id.layer_id, subclass->id.class_id);
    fflush(flog);

    find_discr_function(flog, class, subclass, res + idx);

    switch(res[idx].rc) {
    case Z3_L_FALSE:
      fprintf(flog, "unsat\n");
      break;
    case Z3_L_UNDEF:
      fprintf(flog, "unknown\n");
      break;
    case Z3_L_TRUE: {
      char *str = fun_print(&res[idx].fun);
      fprintf(flog, "%s\n", str);
      free(str);
      break;
    }
    }
    ++idx;
  }

  /* save results to a binary file */
  FILE *fout = fopen(foutname, "wb");
  assert(fout != NULL);
  write_results(fout, &lattice, classes, num_classes, res);
  
  free(res);
  fclose(flog);
  free(classes);
  lattice_free(&lattice);
}

int main() {
  printf("test-classes-with-one-subclass: "); fflush(stdout);
  test_find_classes_with_one_subclass("data/all-maj.2016",
                                      "output/classes-with-one-subclass/log.txt",
                                      "output/classes-with-one-subclass/result.2016");
  printf("Ok.\n");
}
