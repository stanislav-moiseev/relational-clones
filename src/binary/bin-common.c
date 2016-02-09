/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "binary/bin-common.h"

void uint32_write(FILE *fd, uint32_t x) {
  assert(fwrite(&x, 4, 1, fd) == 1);
}

void uint64_write(FILE *fd, uint64_t x) {
  assert(fwrite(&x, 8, 1, fd) == 1);
}

uint32_t uint32_read(FILE *fd) {
  uint32_t x;
  assert(fread(&x, 4, 1, fd) == 1);
  return x;
}

uint64_t uint64_read(FILE *fd) {
  uint64_t x;
  assert(fread(&x, 8, 1, fd) == 1);
  return x;
}


/******************************************************************************/
/** WRITE part */

void fun_write(FILE *fd, const fun *fun) {
  uint32_write(fd, fun->arity);
  for(size_t offset = 0; offset < FUN_DATA_SIZE; ++offset) {
    uint64_write(fd, fun->data[offset]);
  }
}

void pred_write(FILE *fd, const pred *pred) {
  uint32_write(fd, K);
  uint32_write(fd, pred->arity);
  uint64_write(fd, pred->data);
}

void clone_write(FILE *fd, const clone *clone) {
  assert(CLONE_DATA2_SIZE == 8);
  uint32_write(fd, clone->data0);
  uint32_write(fd, clone->data1);
  for(size_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    uint64_write(fd, clone->data2[offset]);
  }
}


/******************************************************************************/
/** READ part */

void fun_read(FILE *fd, fun *fun) {
  fun->arity = uint32_read(fd);
  for(size_t offset = 0; offset < FUN_DATA_SIZE; ++offset) {
    fun->data[offset] = uint64_read(fd);
  }
}

void pred_read(FILE *fd, pred *pred) {
  assert(uint32_read(fd) == K);
  pred->arity = uint32_read(fd);
  pred->data = uint64_read(fd);
}

void clone_read(FILE *fd, clone *clone) {
  assert(CLONE_DATA2_SIZE == 8);
  clone->data0 = uint32_read(fd);
  clone->data1 = uint32_read(fd);
  for(size_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    clone->data2[offset] = uint64_read(fd);
  }
}

