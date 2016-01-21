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
#endif
