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

int clone_consistent(const clone *clone) {
  /* arity == 0 */
  if(2 > 32) return 0;
  /* arity == 1 */
  if(int_pow2(K) > 32) return 0;
  /* arity == 2 */
  if(int_pow2(K*K) > 64*CLONE_DATA2_SIZE) return 0;
  return 1;
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
      /* print `pred->data[offset]` with all preceding zeros (up to 8 zeors) */
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
  for(int64_t i = 0; i < size; ++i) {
    char str[pred_fingerprint_size()];
    char str2[pred_print_extensional_size()];
    pred_print_fingerprint(str, &pred_list[i]);
    pred_print_extensional(str2, &pred_list[i]);
    fprintf(fd, "%s: \t%s\n", str, str2);
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
    return (clone->data2[offset] & ((uint64_t)1 << shift));
    break;
  }
  }
  /* unreachable */
  return 0;
}

int64_t clone_cardinality(const clone *clone) {
  /* fro preds f airty 0 and 1 */
  int64_t card = popcount32(clone->data0) + popcount32(clone->data1);
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

int clone_is_empty(const clone *clone) {
  if(clone->data0) return 0;
  if(clone->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if(clone->data2[offset]) return 0;
  }
  return 1;
}

void clone_get_predicates(const clone *clone, pred **pred_list, uint64_t *size) {
  /* TODO: use actual size of clone here, not the maximum possible */
  *pred_list = malloc((2 + int_pow2(K) + int_pow2(K*K)) * sizeof(pred));
  assert(*pred_list != NULL);
  
  uint64_t _size = 0;
  pred *current_pred = *pred_list;

  for(clone_iterator it = clone_iterator_begin(clone); !clone_iterator_end(clone, &it); clone_iterator_next(&it)) {
    *current_pred = clone_iterator_deref(&it);
    ++_size;
    ++current_pred;
  }
  *size = _size;
}

int clone_eq(const clone *clone1, const clone *clone2) {
  if(clone1->data0 != clone2->data0) return 0;
  if(clone1->data1 != clone2->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if(clone1->data2[offset] != clone2->data2[offset]) return 0;
  }
  return 1;
}

void clone_copy(const clone *clone, struct clone *copy) {
  copy->data0 = clone->data0;
  copy->data1 = clone->data1;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    copy->data2[offset] = clone->data2[offset];
  }  
}

int clone_subset(const clone *clone1, const clone *clone2) {
  if((clone1->data0 | clone2->data0) != clone2->data0) return 0;
  if((clone1->data1 | clone2->data1) != clone2->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if((clone1->data2[offset] | clone2->data2[offset]) != clone2->data2[offset]) return 0;
  }
  return 1;
}

void clone_union(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 | clone2->data0;
  clone->data1 = clone1->data1 | clone2->data1;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = clone1->data2[offset] | clone2->data2[offset];
  }
}

void clone_diff(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 & (~clone2->data0);
  clone->data1 = clone1->data1 & (~clone2->data1);
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = clone1->data2[offset] & (~clone2->data2[offset]);
  }
}
