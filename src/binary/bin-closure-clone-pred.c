/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "binary/bin-common.h"
#include "binary/bin-closure-clone-pred.h"

static void ccpnode_write(FILE *fd, const ccpnode *c) {
  uint32_write(fd, c->cidx);
  clone_write(fd, &c->generator);
  clone_write(fd, &c->clone);
  uint32_write(fd, c->pidx_begin);
  /* uint64_write(fd, c->num_children); */
  for(class_idx *child_idx = c->children; child_idx < c->children + c->num_children; ++child_idx) {
    uint32_write(fd, *child_idx);
  }
}

static void predicate_numerator_write(FILE *fd, const predicate_numerator *pred_num) {
  uint64_write(fd, pred_num->uniq_sz);
  for(pred *p = pred_num->uniq_preds; p < pred_num->uniq_preds + pred_num->uniq_sz; ++p) {
    pred_write(fd, p);
  }
}

void ccplt_write(const char *fname, const ccplt *lt) {
  FILE *fd = fopen(fname, "wb");
  assert(fd);

  uint64_write(fd, lt->num_nodes);
  predicate_numerator_write(fd, lt->pred_num);
  
  for(ccpnode **ccpnodep = lt->nodes; ccpnodep < lt->nodes + lt->num_nodes; ++ccpnodep) {
    ccpnode *c = *ccpnodep;
    ccpnode_write(fd, c);
  }

  fclose(fd);
}

static void ccpnode_read(FILE *fd, const ccplt *lt, ccpnode *c) {
  c->cidx         = uint32_read(fd);
  clone_read(fd, &c->generator);
  clone_read(fd, &c->clone);
  c->pidx_begin   = uint32_read(fd);
  c->num_children = lt->pred_num->uniq_sz - c->pidx_begin;
  /* c->num_children = uint64_read(fd); */
  c->children     = malloc(c->num_children * sizeof(class_idx)); 
  assert(c->children != NULL);
  for(class_idx *child_idx = c->children; child_idx < c->children + c->num_children; ++child_idx) {
    *child_idx = uint32_read(fd);
  }
  hashtable_insert(lt->ht, &c->clone, c);
}

predicate_numerator *predicate_numerator_read(FILE *fd) {
  predicate_numerator *pred_num = malloc(sizeof(struct predicate_numerator));
  assert(pred_num);
  
  size_t sz = uint64_read(fd);
  pred *preds = malloc(sz * sizeof(struct pred));
  assert(preds);
  for(pred *p = preds; p < preds + sz; ++p) {
    pred_read(fd, p);
  }

  return predicate_numerator_alloc(preds, sz);
  free(preds);
}

ccplt *ccplt_read(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  ccplt *lt = malloc(sizeof(ccplt));
  assert(lt);
  lt->num_nodes = uint64_read(fd);
  lt->capacity  = lt->num_nodes;
  lt->nodes     = malloc(lt->capacity * sizeof(ccpnode *));
  assert(lt->nodes);
  lt->ht        = hashtable_alloc(2*lt->capacity, clone_hash, (int (*)(const void *, const void *))clone_eq);
  lt->pred_num  = predicate_numerator_read(fd);

  /* Alloc memory for ccpnodes. We need the pointers to ccpnodes be ready before
   * calling `ccpnode_read`. */
  for(ccpnode **ccpnodep = lt->nodes; ccpnodep < lt->nodes + lt->num_nodes; ++ccpnodep) {
    *ccpnodep = ccpnode_alloc();
  }
  
  /* read ccpnodes from file and connect them together */
  class_idx idx = 0;
  for(ccpnode **ccpnodep = lt->nodes; ccpnodep < lt->nodes + lt->num_nodes; ++ccpnodep) {
    ccpnode *c = *ccpnodep;
    c->lt = lt;
    ccpnode_read(fd, lt, c);
    assert(c->cidx == idx);
    ++idx;
  }

  fclose(fd);
  return lt;
}

