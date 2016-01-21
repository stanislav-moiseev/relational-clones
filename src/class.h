/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef CLASS_H
#define CLASS_H

#include <stdint.h>
#include "clone.h"

/** `class_id` is a unique class identifier.
 */
struct class_id {
  uint32_t layer_id;
  /* class number withing a layer */
  uint32_t class_id;
};
typedef struct class_id class_id;


struct class {
  class_id id;
  clone basis;
  clone clone;
  uint64_t num_subclasses;
  class_id *subclasses;
};

typedef struct class class;

/** `class_free` releases the memory allocated to store the list of 
 * subclasses.
 */
void class_free(class *class);

/** `class_print_verbosely` writes
 *   1) a list of all basis predicates of the class `class`.
 *   2) a list of all predicates from the `class->clone`.
 */
void class_print_verbosely(FILE *fd, const class *class);

#endif

