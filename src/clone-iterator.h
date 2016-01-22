/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef CLONE_ITERATOR_H
#define CLONE_ITERATOR_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"

/** clone iterators */
struct clone_iterator {
  const clone *clone;
  int64_t offset;
  int64_t shift;
};
typedef struct clone_iterator clone_iterator;

clone_iterator clone_iterator_begin(const clone *clone);

int clone_iterator_end(const clone *clone, clone_iterator *it);

void clone_iterator_next(clone_iterator *it);

pred clone_iterator_deref(const clone_iterator *it);

#endif
