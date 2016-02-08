/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef PREDICATE_H
#define PREDICATE_H

#include <stdint.h>
#include <stdio.h>

#include "utils.h"

/**
 * Possible combinations of `k` and `arity`
 *      k:              2       3       4       5       6
 *      max pred arity: 6       3       3       2       2
 */
struct pred {
  uint64_t arity;
  uint64_t data;
};

typedef struct pred pred;

/** `pred_construct` constructs a predicate from a string representing its
 * extensional.
 * `pred_construct` returns non-zero if the construction have proceeded well;
 * otherwise, it returns zero (e.g. when `str` is too short or too long).
 */
int pred_construct(uint32_t arity, const char *str, pred *pred);

/** `pred_consistent` returns non-zero if the internal structure of `p` is
 * consistent. In particular, it checks that `struct pred` contains enough bits
 * to store all `k^arity` values of the predicate.
 */
int pred_consistent(const pred *pred);

/** `pred_fingerprint_size` return the minimum buffer size for
 *  `pred_print_fingerprint`.
 */
size_t pred_fingerprint_size();

/** `pred_print` prints the short name of the predicate.
 * The short name contains `k`, `pred->arity` and a string representation
 * of `pred->data` (in hexadecimal format, without preceding zeros).
 */
void pred_print_fingerprint(char *str, const pred *pred);

/** `pred_extensional_size` return the minimum buffer size for
 *  `pred_print_extensional`.
 */
size_t pred_print_extensional_size();

/** `pred_print_extensional` prints the predicate's extensional.
 */
void pred_print_extensional(char *str, const pred *pred);

/** `pred_extensional` return the set of all tuples satisfying the predicate.
 * The tuples are returned in an unspecified order.
 */
void pred_extensional(const pred *pred, uint32_t **ext, size_t *size);

/** `pred_cardinality` returns the number of tuples satisfying the predicate.
 */
int64_t pred_cardinality(const pred *pred);


static inline int pred_eq(const pred *p1, const pred *p2) {
  return p1->arity == p2->arity && p1->data == p2->data;;
}

/** `pred_init` initializes the predicate to be equal to zero.
 */
static inline void pred_init(pred *pred, uint64_t arity) {
  pred->arity = arity;
  pred->data  = 0;
}

/** `pred_set` sets the value of predicate on the tuple to be true.
 */
static inline void pred_set(pred *pred, uint64_t tuple) {
  pred->data |= ((uint64_t)1 << tuple);
}

/** `pre_compute` returns non-zero if the predicate return true on the given
 *  tuple.
 */

static inline int pred_compute(const pred *pred, uint64_t tuple) {
  return pred->data & ((uint64_t)1 << tuple);
}

/** `pred_is_essential` returns non-zero if the predicate is an essential Zhuk
 *  predicate.
 */
int pred_is_essential(const pred *pred);

/** `all_essential_predicates` returns a clone containing the set of all
 * essential predicates of arity <= max_arity.
 */
void get_essential_predicates(uint32_t max_arity, pred **ess_preds, size_t *size);


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
