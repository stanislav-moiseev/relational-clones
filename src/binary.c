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

  /* DBG */
  /* char str[pred_extensional_size()]; */
  /* pred_print_extensional(str, pred); */
  /* printf("pred: \t%s\n", str); */
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


