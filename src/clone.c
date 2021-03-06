/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <immintrin.h>

#include "utils.h"
#include "pred.h"
#include "clone.h"
#include "fasthash/fasthash.h"

int clone_consistent(const clone *clone) {
  /* arity == 0 */
  if(2 > 32) return 0;
  /* arity == 1 */
  if(int_pow2(K) > 32) return 0;
  /* arity == 2 */
  if(int_pow2(K*K) > 64*CLONE_DATA2_SIZE) return 0;
  return 1;
}

uint32_t clone_hash(const void *cl) {
  return fasthash32(cl, 8+8*CLONE_DATA2_SIZE, 0);
}

size_t clone_fingerprint_size() {
  return (8                             /* for "clone___" string */
          + 8                           /* for arity 0 preds */
          + 8                           /* for arrty 1 preds */
          + (16*CLONE_DATA2_SIZE)       /* for arity 2 preds */
          + 1);                         /* for terminating null byte */
}

void clone_print_fingerprint(char *str, const clone *clone) {
  str += sprintf(str, "clone%u_%x_%x_", K, clone->data0, clone->data1);

  int flag = 1; /* 1 means not to print preceding zeros */
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if(flag) {
      if(clone->data2[offset] == 0) continue;
      flag = 0;
      str += sprintf(str, "%lx", clone->data2[offset]);
    } else {
      /* print `pred->data[offset]` with all preceding zeros (up to 8 zeros) */
      str += sprintf(str, "%.8lx", clone->data2[offset]);
    }
  }

  /* if the clone contains no predicates of arity 2 */
  if(flag) {
    sprintf(str, "0");
  }
}

void clone_print_verbosely(FILE *fd, const clone *clone) {
  uint64_t size;
  pred *pred_list;
  clone_get_predicates(clone, &pred_list, &size);
  for(size_t idx = 0; idx < size; ++idx) {
    const pred *p = pred_list + idx;
    const char *s = pred_name(p);
    if(s == NULL) s = "?";
    
    fprintf(fd, "%lu:\t%s \t%-32s%s\n",
            idx,
            pred_print_fingerprint(p),
            s,
            pred_print_extensional_ex(p));
  }
  free(pred_list);
}

void clone_insert_pred(clone *clone, const pred *pred) {
  assert(pred->arity <= 2);
  switch(pred->arity) {
  case 0:
    clone->data0 |= ((uint32_t)1 << pred->data);
    break;
  case 1:
    clone->data1 |= ((uint32_t)1 << pred->data);
    break;
  case 2: {
    uint64_t offset, shift;
    get_offset_shift(pred->data, &offset, &shift);
    assert(offset < CLONE_DATA2_SIZE);
    clone->data2[offset] |= ((uint64_t)1 << shift);
    break;
  }
  }
}

void clone_remove_pred(clone *clone, const pred *pred) {
    assert(pred->arity <= 2);
  switch(pred->arity) {
  case 0:
    clone->data0 &= ~((uint32_t)1 << pred->data);
    break;
  case 1:
    clone->data1 &= ~((uint32_t)1 << pred->data);
    break;
  case 2: {
    uint64_t offset, shift;
    get_offset_shift(pred->data, &offset, &shift);
    assert(offset < CLONE_DATA2_SIZE);
    clone->data2[offset] &= ~((uint64_t)1 << shift);
    break;
  }
  }
}


int clone_test_pred(const clone *clone, const pred *pred) {
  assert(pred->arity <= 2);
  switch(pred->arity) {
  case 0:
    return (clone->data0 & ((uint32_t)1 << pred->data));
    break;
  case 1:
    return (clone->data1 & ((uint32_t)1 << pred->data));
    break;
  case 2: {
    uint64_t offset, shift;
    get_offset_shift(pred->data, &offset, &shift);
    assert(offset < CLONE_DATA2_SIZE);
    return (clone->data2[offset] & ((uint64_t)1 << shift)) != 0;
    break;
  }
  }
  /* unreachable */
  return 0;
}

uint64_t clone_cardinality(const clone *clone) {
  /* for preds of arity 0 and 1 */
  uint64_t card = popcount32(clone->data0) + popcount32(clone->data1);
  /* arity == 2 */
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    card += popcount64(clone->data2[offset]);
  }
  return card;
}

void clone_init(clone *clone) {
  clone->data0 = 0;
  clone->data1 = 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = 0;
  }
}

/******************************************************************************/
/** clone iterators */

void clone_get_predicates(const clone *clone, pred **pred_list, uint64_t *size) {
  *pred_list = malloc(clone_cardinality(clone) * sizeof(pred));
  assert(*pred_list != NULL);
  
  uint64_t _size = 0;
  pred *current_pred = *pred_list;

  for(clone_iterator it = clone_iterator_begin(clone); !clone_iterator_end(clone, &it); clone_iterator_next(&it)) {
    *current_pred = clone_iterator_deref(&it);
    ++_size;
    ++current_pred;
  }

  if(size != NULL) *size = _size;
}

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


/******************************************************************************/
/** relations over clones */


int clone_is_empty(const clone *clone) {
  if(clone->data0) return 0;
  if(clone->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if(clone->data2[offset]) return 0;
  }
  return 1;
}

int clone_eq(const clone *clone1, const clone *clone2) {
  if(clone1->data0 != clone2->data0) return 0;
  if(clone1->data1 != clone2->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if(clone1->data2[offset] != clone2->data2[offset]) return 0;
  }
  return 1;
}

int clone_subset(const clone *clone1, const clone *clone2) {
  if((clone1->data0 | clone2->data0) != clone2->data0) return 0;
  if((clone1->data1 | clone2->data1) != clone2->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if((clone1->data2[offset] | clone2->data2[offset]) != clone2->data2[offset]) return 0;
  }
  return 1;
}

/******************************************************************************/
/** operations over clones */

void clone_copy(const clone *clone, struct clone *copy) {
  copy->data0 = clone->data0;
  copy->data1 = clone->data1;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    copy->data2[offset] = clone->data2[offset];
  }  
}

void clone_union(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 | clone2->data0;
  clone->data1 = clone1->data1 | clone2->data1;
  for(int64_t offset = CLONE_DATA2_SIZE/4 - 1; offset >= 0; --offset) {
    __m256i ymm1 = _mm256_load_si256((__m256i *)&clone1->data2 + offset);
    __m256i ymm2 = _mm256_load_si256((__m256i *)&clone2->data2 + offset);
    __m256i ymm3 = _mm256_or_si256(ymm1, ymm2);
    _mm256_store_si256((__m256i *)&clone->data2 + offset, ymm3);
  }
}

void clone_intersection(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 & clone2->data0;
  clone->data1 = clone1->data1 & clone2->data1;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = clone1->data2[offset] & clone2->data2[offset];
  }
}

void clone_diff(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 & (~clone2->data0);
  clone->data1 = clone1->data1 & (~clone2->data1);
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = clone1->data2[offset] & (~clone2->data2[offset]);
  }
}
