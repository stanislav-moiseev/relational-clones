/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef PREDICATE_H
#define PREDICATE_H

#include <stdint.h>
#include <stdio.h>

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

/** `pred_consistent` returns non-zero if the internal structure of `p` is
 * consistent. In particular, it checks that `struct pred` contains enough bits
 * to store all `k^arity` values of the predicate.
 */
int pred_consistent(const pred *pred);


/******************************************************************************/
/** printing and scanning */

/** `pred_construct` constructs a predicate from a string representing its
 * extensional.
 * `pred_construct` returns non-zero if the construction have proceeded well;
 * otherwise, it returns zero (e.g. when `str` is too short or too long).
 */
int pred_construct(uint32_t arity, const char *str, pred *pred);

/** `pred_print` prints the short name of the predicate.
 * The short name contains `k`, `pred->arity` and a string representation
 * of `pred->data` (in hexadecimal format, without preceding zeros).
 *
 * The function returns a pointer to a statically allocated memory region.
 * The contents of the string will be updated on next function call.
 */
const char *pred_print_fingerprint(const pred *pred);

/** `pred_extensional_size` return the minimum buffer size for
 *  `pred_print_extensional`.
 */
size_t pred_print_extensional_size();

/** `pred_print_extensional` prints a vector of 0s and 1s representing 
 * to the values of the predicate of the corresponding tuples,
 * starting from the largest tuple <k-1,...,k-1>.
 */
void pred_print_extensional(char *str, const pred *pred);

/** The function pretty prints all the tuples from the predicate.
 *
 * The function returns a pointer to a statically allocated memory region.
 * The contents of the string will be updated on next function call.
 */
const char *pred_print_extensional_ex(const pred *p);

/** `pred_scan` returns a predicate designated by a verbose string
 * representation of its extensional (a set of tuples where the predicate is
 * true), e.g.
 *
 *     pred_scan(2, "{00, 11, 22}");
 *
 * construct an identity predicate.
 *
 * All tuples must be of length == `arity`; the order of the tuples is
 * insignificant.
 */
pred pred_scan_ex(uint32_t arity, const char *ext);

/** `pred_name` looks up a database of predicates known in mathematical
 * theory. If found, the function returns a verbose human-friendly mathematical
 * name.
 */
const char *pred_name(const pred *p);

/** `pred_get` looks up a database of known predicates, and returns the
 * predicate designated by the given name (if any). If the name is unknown, an
 * assertion will fail.
 */
const pred *pred_get(const char *pred_name);


/******************************************************************************/
/** basic operations */

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

/** `pred_clear` sets the value of predicate on the tuple to be false.
 */
static inline void pred_clear(pred *pred, uint64_t tuple) {
  pred->data &= ~((uint64_t)1 << tuple);
}


/** `pre_compute` returns non-zero if the predicate return true on the given
 *  tuple.
 */
static inline int pred_compute(const pred *pred, uint64_t tuple) {
  return pred->data & ((uint64_t)1 << tuple);
}


#endif
