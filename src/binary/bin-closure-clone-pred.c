/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "binary/bin-common.h"
#include "binary/bin-closure-clone-pred.h"

static void class_write(FILE *fd, const class *c) {
  uint32_write(fd, c->idx);
  clone_write(fd, &c->generator);
  clone_write(fd, &c->clone);
  for(class_idx *child_idx = c->children; child_idx < c->children + c->lt->pred_num->uniq_sz; ++child_idx) {
    uint32_write(fd, *child_idx);
  }
}

static void predicate_numerator_write(FILE *fd, const predicate_numerator *pred_num) {
  uint64_write(fd, pred_num->uniq_sz);
  for(pred *p = pred_num->uniq_preds; p < pred_num->uniq_preds + pred_num->uniq_sz; ++p) {
    pred_write(fd, p);
  }
}

void lattice_write(const char *fname, const lattice *lt) {
  FILE *fd = fopen(fname, "wb");
  assert(fd);

  uint64_write(fd, lt->num_classes);
  predicate_numerator_write(fd, lt->pred_num);
  for(class **classp = lt->classes; classp < lt->classes + lt->num_classes; ++classp) {
    class *c = *classp;
    class_write(fd, c);
  }

  fclose(fd);
}

static void class_read(FILE *fd, const lattice *lt, class *c) {
  c->idx = uint32_read(fd);
  clone_read(fd, &c->generator);
  clone_read(fd, &c->clone);
  for(class_idx *child_idx = c->children; child_idx < c->children + c->lt->pred_num->uniq_sz; ++child_idx) {
    *child_idx = uint32_read(fd);
  }
}

lattice *lattice_read(const char *fname) {
  FILE *fd = fopen(fname, "rb");
  assert(fd);

  lattice *lt = malloc(sizeof(lattice));
  assert(lt);
  lt->num_classes = uint64_read(fd);
  lt->capacity    = lt->num_classes;
  lt->classes     = malloc(lt->capacity * sizeof(class *));
  assert(lt->classes);
  lt->ht = NULL;
  lt->pred_num = predicate_numerator_construct();

  /* verify that the generated predicate numerator and that in the file are
   * identical */
  size_t uniq_sz2 = uint64_read(fd);
  assert(lt->pred_num->uniq_sz == uniq_sz2);
  for(pred *p = lt->pred_num->uniq_preds; p < lt->pred_num->uniq_preds + lt->pred_num->uniq_sz; ++p) {
    pred p2;
    pred_read(fd, &p2);
    assert(pred_eq(p, &p2));
  }

  /* alloc memory for classes; make pointers to classes be ready */
  for(class **classp = lt->classes; classp < lt->classes + lt->num_classes; ++classp) {
    *classp = class_alloc();
    (*classp)->children = malloc(lt->pred_num->uniq_sz * sizeof(class_idx)); 
    assert((*classp)->children != NULL);
  }
  
  /* read classes from file and connect them together */
  class_idx idx = 0;
  for(class **classp = lt->classes; classp < lt->classes + lt->num_classes; ++classp) {
    class *c = *classp;
    c->lt = lt;
    class_read(fd, lt, c);
    assert(c->idx == idx);
    ++idx;
  }

  fclose(fd);
  return lt;
}

