/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef CLASS_H
#define CLASS_H

#include <stdint.h>
#include "clone.h"

struct class {
  clone basis;
  clone clone;
};

typedef struct class class;


/** `class_print_verbosely` writes
 *   1) a list of all basis predicates of the class `class`.
 *   2) a list of all predicates from the `class->clone`.
 */
void class_print_verbosely(FILE *fd, const class *class);

#endif
