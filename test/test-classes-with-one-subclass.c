/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/binary-2016.h"
#include "algorithms/alg-maj.h"

void test_find_classes_with_one_subclass(const char *fname, const char *flogname, const char *foutname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);
  
  maj_lattice lattice;
  maj_lattice_read(fd, &lattice);
  fclose(fd);
  
  maj_class **classes;
  uint64_t num_classes;
  find_classes_with_one_subclass(&lattice, &classes, &num_classes);

  fun *funs = malloc(num_classes * sizeof(struct fun));
  assert(funs != NULL);  
  
  FILE *flog = fopen(flogname, "w");
  assert(flog != NULL);

  /** For each pair of class—subclass, we search for a discriminating function
   * of arity from 0 up to 5. */
  size_t idx = 0;
  for(maj_class **pclass = classes; pclass < classes + num_classes; ++pclass) {
    maj_class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct maj_class *subclass = maj_lattice_get_class(&lattice, class->subclasses[0]);

    fprintf(flog, "%lu:\t class %2d:%-6d\t subclass %2d:%-6d\t ",
            idx,
            class->id.layer_id, class->id.class_id,
            subclass->id.layer_id, subclass->id.class_id);
    fflush(flog);

    Z3_lbool rc = find_discr_function(class, subclass, 5, funs+idx);

    switch(rc) {
    case Z3_L_FALSE:
      fprintf(flog, "unsat\n");
      funs[idx].arity = -1;
      break;
    case Z3_L_UNDEF:
      fprintf(flog, "unknown\n");
      funs[idx].arity = -2;
      break;
    case Z3_L_TRUE: {
      /* verify the result */
      assert(test_discr_function(&class->clone, &subclass->basis, funs+idx));
      char *str = fun_print(funs+idx);
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
  write_classes_with_one_subclass_discr_fun(fout, &lattice, classes, num_classes, funs);
  
  free(funs);
  fclose(flog);
  free(classes);
  maj_lattice_free(&lattice);
}

int verify_classes_with_one_subclass(const char *fname, const char *fclasses_name) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);
  
  maj_lattice lattice;
  maj_lattice_read(fd, &lattice);
  fclose(fd);

  FILE *fclasses = fopen(fclasses_name, "rb");
  assert(fclasses != NULL);
  
  maj_class **classes;
  uint64_t num_classes;
  fun *funs;
  read_classes_with_one_subclass_discr_fun(fclasses, &lattice, &classes, &num_classes, &funs);
  fclose(fclasses);

  int rc = 1;
  for(size_t i = 0; i < num_classes; ++i) {
    maj_class *class = classes[i];
    fun *fun = funs + i;
    if(class->num_subclasses != 1) { rc = 0; break; }
    struct maj_class *subclass = maj_lattice_get_class(&lattice, class->subclasses[0]);

    if(!test_discr_function(&class->clone, &subclass->basis, fun)) { rc = 0; break; }
  }
  
  free(classes);
  free(funs);
  return rc;
}


int main() {
  /* printf("test-classes-with-one-subclass: "); fflush(stdout); */
  /* test_find_classes_with_one_subclass("data/all-maj.2016", */
  /*                                     "output/classes-with-one-subclass.txt", */
  /*                                     "output/classes-with-one-subclass.2016"); */
  /* printf("Ok.\n"); */

  printf("verify-classes-with-one-subclass: "); fflush(stdout);
  if(verify_classes_with_one_subclass("data/all-maj.2016",
                                      "output/classes-with-one-subclass.2016")) {
    printf("Ok.\n");
  } else {
    printf("Error.\n");
  }
}
