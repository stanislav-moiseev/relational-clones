/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "binary/maj-classes-with-one-subclass-discr-fun.h"
#include "binary/binary-2016.h"

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
