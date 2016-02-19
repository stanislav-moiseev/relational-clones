/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "binary/bin-common.h"
#include "binary/bin-maj-lattice.h"
#include "binary/bin-maj-classes-with-one-subclass-discr-fun.h"

void write_classes_with_one_subclass_discr_fun(FILE *fd, const majlattice *lattice, majclass * const *classes, size_t num_classes, const fun *funs) {
  uint64_write(fd, num_classes);
  for(majclass * const *pclass = classes; pclass < classes + num_classes; ++pclass) {
    majclass *class = *pclass;
    assert(class->num_subclasses == 1);
    struct majclass *subclass = majlattice_get_class(lattice, class->subclasses[0]);
    majclass_id_write(fd, &class->id);
    majclass_id_write(fd, &subclass->id);
    fun_write(fd, funs);
    ++funs;
  }  
}

void read_classes_with_one_subclass_discr_fun(FILE *fd, const majlattice *lattice, majclass ***classes, size_t *num_classes, fun **funs) {
  *num_classes = uint64_read(fd);
  *classes = malloc(*num_classes * sizeof(majclass *));
  assert(*classes != NULL);
  *funs = malloc(*num_classes * sizeof(fun));
  assert(*funs != NULL);
  for(size_t i = 0; i < *num_classes; ++i) {
    majclass_id class_id, subclass_id;
    majclass_id_read(fd, &class_id);
    majclass_id_read(fd, &subclass_id);
    fun_read(fd, *funs + i);
    (*classes)[i] = majlattice_get_class(lattice, class_id);
  }  
}
