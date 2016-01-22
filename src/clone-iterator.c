/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "pred.h"
#include "clone.h"
#include "clone-iterator.h"

clone_iterator clone_iterator_begin(const clone *clone) {
  clone_iterator it = { .clone = clone,
                        .offset = -3 };
  clone_iterator_next(&it);
  return it;
}

int clone_iterator_end(const clone *clone, clone_iterator *it) {
  if(it->offset == CLONE_DATA2_SIZE) return 1;
  else return 0;
}

void clone_iterator_next(clone_iterator *it) {
  switch(it->offset) {
  case -3:      /* `it` is uninitialized */
    it->offset = -2;
    it->shift  = -1;
    
  case -2:      /* arity == 0 */
    ++it->shift;
    for(; it->shift < 2; ++it->shift) {
      if(it->clone->data0 & ((uint32_t)1 << it->shift)) return;
    }
    it->offset = -1;
    it->shift  = -1;
    
  case -1:      /* arity == 1 */
    ++it->shift;
    for(; it->shift < int_pow2(K); ++it->shift) {
      if(it->clone->data1 & ((uint32_t)1 << it->shift)) return;
    }
    it->shift  = 63;
    
  default:      /* arity == 2 */
    ++it->shift;
    if(it->shift == 64) { ++it->offset; it->shift = 0; };
    /* max_offset = int_pow2(K*K) / 64; */
    for(; it->offset < CLONE_DATA2_SIZE; ++it->offset) {
      for(; it->shift < 64; ++it->shift) {
        if(it->clone->data2[it->offset] & ((uint64_t)1 << it->shift)) return;
      }
      it->shift = 0;
    }
  }
}

pred clone_iterator_deref(const clone_iterator *it) {
  pred p;
  switch(it->offset) {
  case -2:
    p.arity = 0;
    p.data = it->shift;
    break;
  case -1:
    p.arity = 1;
    p.data = it->shift;
    break;
  default:
    p.arity = 2;
    p.data = (64*it->offset) + it->shift;
    break;
  }
  return p;
}
