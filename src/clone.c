/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "pred.h"
#include "clone.h"
#include "utils.h"

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

int clone_read(FILE *fd, clone *clone, pred **pred_list, uint64_t *size) {
  /* the size of the basis */
  uint64_t n = read_uint64(fd);
  /* DBG */
  /* printf("basis size: \t%lu\n", n); */
  if(pred_list != NULL) { /* if we need to store the basis */
    *size = n;
    *pred_list = malloc(n * sizeof(pred));
    if(*pred_list == NULL) return 0;
    for(int64_t i = 0; i < n; ++i) {
      pred_read(fd, &(*pred_list)[i]);
    }
  } else { /* if there is no need to store the basis */
    /* read the basis but do not write the predicates anywhere */
    for(int64_t i = 0; i < n; ++i) {
      pred pred;
      pred_read(fd, &pred);
    }
  }    

  clone->data0 = read_uint32(fd);
  clone->data1 = read_uint32(fd);
  assert(CLONE_DATA2_SIZE == 8);
  for(int64_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    clone->data2[offset] = read_uint64(fd);
  }

  /* DBG */
  /* printf("---\n"); */
  /* uint64_t card; */
  /* pred pred_list[600]; */
  /* clone_get_predicates(clone, pred_list, 600, &card); */
  /* for(int64_t i = 0; i < card; ++i) { */
  /*   char str[pred_extensional_size()]; */
  /*   pred_print_extensional(str, &pred_list[i]); */
  /*   char str2[pred_fingerprint_size()]; */
  /*   pred_print_fingerprint(str2, &pred_list[i]); */
  /*   printf("%s: \t%s\n", str2, str); */
  /* } */
  return 1;
}

int clone_aread_layer(FILE *fd, clone **clones, size_t *size) {
  *size = read_uint64(fd);
  /* DBG */
  /* printf("layer size: \t%lu\n", *size); */
  
  (*clones) = malloc(*size * sizeof(clone));
  assert(*clones != NULL);
  for(int64_t i = 0; i < *size; ++i) {
    /* DBG */
    /* printf("clone index2: \t%ld\n", i); */
    clone_read(fd, (*clones) + i, NULL, NULL);
  }

  /* test EOF */
  char c;
  assert(fread(&c, 1, 1, fd) == 0);
  return 1;
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


int clone_is_empty(const clone *clone) {
  if(clone->data0) return 0;
  if(clone->data1) return 0;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    if(clone->data2[offset]) return 0;
  }
  return 1;
}


int clone_get_predicates(const clone *clone, pred **pred_list, uint64_t *size) {
  /* TODO: use actual size of clone here, not the maximum possible */
  *pred_list = malloc((2 + int_pow2(K) + int_pow2(K*K)) * sizeof(pred));
  if(*pred_list == NULL) return 0;
  
  uint64_t _size = 0;
  pred *current_pred = *pred_list;
  
  /* arity == 0 */
  for(int64_t shift = 1; shift >= 0; --shift) {
    if(clone->data0 & ((uint32_t)1 << shift)) {
      ++_size;
      current_pred->arity = 0;
      current_pred->data  = shift;
      ++current_pred;
    }
  }

  /* arity == 1 */
  for(int64_t shift = int_pow2(K)-1; shift >= 0; --shift) {
    if(clone->data1 & ((uint32_t)1 << shift)) {
      ++_size;
      current_pred->arity = 1;
      current_pred->data  = shift;
      ++current_pred;
    }
  }
  
  /* arity == 2 */
  /* max_offset = int_pow2(K*K) / 64; */
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    for(int64_t shift = 63; shift >= 0; --shift) {
      if(clone->data2[offset] & ((uint64_t)1 << shift)) {
        ++_size;
        current_pred->arity = 2;
        current_pred->data  = (64*offset) + shift;
        ++current_pred;
      }
    }
  }
  
  *size = _size;
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
