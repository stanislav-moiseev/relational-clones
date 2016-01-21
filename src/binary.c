/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "binary.h"

void pred_read(FILE *fd, pred *pred) {
  uint64_t k = read_uint64(fd);
  assert(k == K);
  
  pred->arity = read_uint64(fd);
  pred->data = read_uint64(fd);
}

int class_read(FILE *fd, class *class) {
  /* the size of the basis */
  uint64_t size = read_uint64(fd);

  for(int64_t i = size; i > 0; --i) {
    pred pred;
    pred_read(fd, &pred);
    clone_insert_pred(&class->clone, &pred);
  }
  
  class->clone.data0 = read_uint32(fd);
  class->clone.data1 = read_uint32(fd);
  assert(CLONE_DATA2_SIZE == 8);
  for(int64_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    class->clone.data2[offset] = read_uint64(fd);
  }
  
  return 1;
}

int class_aread_layer(FILE *fd, class **classes, size_t *size) {
  *size = read_uint64(fd);
  
  (*classes) = malloc(*size * sizeof(class));
  assert(*classes != NULL);
  for(int64_t i = 0; i < *size; ++i) {
    /* DBG */
    /* printf("class index2: \t%ld\n", i); */
    class_read(fd, (*classes) + i);
  }

  /* test EOF */
  char c;
  assert(fread(&c, 1, 1, fd) == 0);
  return 1;
}


