/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "class.h"

void class_free(class *class) {
  if(class->subclasses) {
    free(class->subclasses);
    class->subclasses = NULL;
  }
}

void class_print_verbosely(FILE *fd, const class *class) {
  fprintf(fd, "class %2d:%-6d\n", class->id.layer_id, class->id.class_id);
  fprintf(fd, "class basis:\n");
  clone_print_verbosely(fd, &class->basis);
  fprintf(fd, "class clone:\n");
  clone_print_verbosely(fd, &class->clone);
}
