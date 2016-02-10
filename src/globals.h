/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/


#ifndef GLOBALS_H
#define GLOBALS_H

#include <stdint.h>

#include "pred.h"

/** K-valued logic. Global constant
 */
static const uint32_t K = 3;

/** log2(K) rounded to ceiling */
static const uint32_t INT_LOG2K = 2;


/******************************************************************************/
struct predicate_numerator {
  /* uniq_preds maps a predicate index to the predicate */
  size_t uniq_sz;
  pred *uniq_preds;
  /* reverse index: uniq_pred_idx maps a predicate to its index */
  size_t *uniq_pred_idx[3];
};
typedef struct predicate_numerator predicate_numerator;

predicate_numerator *predicate_numerator_alloc();

void predicate_numerator_free(predicate_numerator *pred_num);

struct globals {
  predicate_numerator *pred_num;
} globals;

static inline size_t pred_idx(const pred *p) {
  assert(p->arity <= 2);
  return globals.pred_num->uniq_pred_idx[p->arity][p->data];
}

static inline pred idx_pred(size_t idx) {
  assert(idx < globals.pred_num->uniq_sz);
  return globals.pred_num->uniq_preds[idx];
}

#endif
