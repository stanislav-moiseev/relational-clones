/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary-2016.h"
#include "z3/gen-spec.h"

void test_find_classes_with_one_subclass(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd != NULL);
  
  lattice lattice;
  lattice_read(fd, &lattice);
  
  class **classes;
  uint64_t num_classes;
  lattice_find_classes_with_one_subclass(&lattice, &classes, &num_classes);

  const char *flogname = "output/classes-with-one-subclass/result.txt";
  FILE *flog = fopen(flogname, "w");
  assert(flog != NULL);

  int idx = 1;
  for(class **pclass = classes; pclass < classes + num_classes; ++pclass) {
    class *class = *pclass;
    assert(class->num_subclasses == 1);
    struct class *subclass = lattice_get_class(&lattice, class->subclasses[0]);
    fprintf(flog, "%d:\t class %2d:%-6d ~~>  subclass %2d:%-6d\t",
           idx,
           class->id.layer_id, class->id.class_id,
           subclass->id.layer_id, subclass->id.class_id);
    ++idx;
    
    /* generate verification conditions */
    /* char *foutname; */
    /* asprintf(&foutname, "output/classes-with-one-subclass/z3/class-%d-%d.z3", */
    /*          class->id.layer_id, class->id.class_id); */
    /* FILE *fout = fopen(foutname, "w"); */
    /* assert(fout != NULL); */
    z3_wrapper z3;
    z3_wrapper_init(&z3);
    
    gen_assert_discr_fun_two_classes(&z3, class, subclass, 1);
    switch(Z3_solver_check(z3.ctx, z3.solver)) {
    case Z3_L_FALSE:
      fprintf(flog, "unsat\n");
      break;
    case Z3_L_UNDEF:
      fprintf(flog, "unknown\n");
      break;
    case Z3_L_TRUE:
      fprintf(flog, "sat\n");
      break;
    }
    
    z3_wrapper_free(&z3);
    /* free(foutname); */
    /* fclose(fout); */
  }

  fclose(flog);
  free(classes);
  lattice_free(&lattice);
  fclose(fd);
}

int main() {
  printf("test-classes-with-one-subclass: "); fflush(stdout);
  test_find_classes_with_one_subclass("data/all-maj.2016");
  printf("Ok.\n");
}
