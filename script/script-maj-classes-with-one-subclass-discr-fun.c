/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/bin-maj-lattice.h"
#include "binary/bin-maj-classes-with-one-subclass-discr-fun.h"
#include "z3/z3-search.h"


void test_majclasses_with_one_subclass_discr_fun(const char *fname, const char *flogname, const char *foutname) {
  majlattice *lattice = majlattice_read(fname);
  
  majclass **classes;
  uint64_t num_classes;
  majlattice_classes_with_one_subclass(lattice, &classes, &num_classes);

  fun *funs = malloc(num_classes * sizeof(struct fun));
  assert(funs != NULL);  
  
  FILE *flog = fopen(flogname, "w");
  assert(flog != NULL);

  /** For each pair of class—subclass, we search for a discriminating function
   * of arity from 0 up to 5. */
  size_t idx = 0;
  for(majclass **pclass = classes; pclass < classes + num_classes; ++pclass) {
    majclass *class = *pclass;
    assert(class->num_subclasses == 1);
    struct majclass *subclass = majlattice_get_class(lattice, class->subclasses[0]);

    fprintf(flog, "%lu:\t class %2d:%-6d\t subclass %2d:%-6d\t ",
            idx,
            class->id.layer_id, class->id.class_id,
            subclass->id.layer_id, subclass->id.class_id);
    fflush(flog);

    Z3_lbool rc = z3_find_discr_function(&class->basis, &class->clone, &subclass->clone, 5, funs+idx);

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
  write_classes_with_one_subclass_discr_fun(fout, lattice, classes, num_classes, funs);

  fclose(flog);
  fclose(fout);
  free(funs);
  free(classes);
  majlattice_free(lattice);
}

int verify(const char *fname, const char *fclasses_name) {
  majlattice *lattice = majlattice_read(fname);

  FILE *fclasses = fopen(fclasses_name, "rb");
  assert(fclasses != NULL);
  
  majclass **classes;
  uint64_t num_classes;
  fun *funs;
  read_classes_with_one_subclass_discr_fun(fclasses, lattice, &classes, &num_classes, &funs);
  fclose(fclasses);

  int rc = 1;
  for(size_t i = 0; i < num_classes; ++i) {
    majclass *class = classes[i];
    fun *fun = funs + i;
    if(class->num_subclasses != 1) { rc = 0; break; }
    struct majclass *subclass = majlattice_get_class(lattice, class->subclasses[0]);

    if(!test_discr_function(&class->clone, &subclass->basis, fun)) { rc = 0; break; }
  }
  
  free(classes);
  free(funs);
  return rc;
}

int main() {
  printf("script-maj-classes-with-one-subclass-discr-fun:\n"); fflush(stdout);
  test_majclasses_with_one_subclass_discr_fun("data/all-maj.2016",
                                              "output/maj-classes-with-one-subclass-disr-fun.txt",
                                              "output/maj-classes-with-one-subclass-disr-fun.2016");
  printf("Ok.\n");

  printf("verify-maj-classes-with-one-subclass-discr-fun: "); fflush(stdout);
  if(verify("data/all-maj.2016",
            "output/classes-with-one-subclass.2016")) {
    printf("Ok.\n");
  } else {
    printf("Error.\n");
  }
}

