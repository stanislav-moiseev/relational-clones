/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef CLONE_H
#define CLONE_H

#include <stdint.h>

#include "pred.h"

#define CLONE_DATA2_SIZE 8

struct clone {
  /* predicates of arity 0 */
  uint32_t data0;
  /* predicates of arity 1 */
  uint32_t data1;
  /* predicates of arity 2 */
  uint64_t data2[CLONE_DATA2_SIZE];
};

typedef struct clone clone;

/** `clone_consistent` returns non-zero if the internal structure of the clone
 * is consistent. In particular, it checks that the `struct clone` contains
 * enough bits to store the predicates of arity <= 2.
 */
int clone_consistent(const clone *clone);

/** `clone_fingerprint_size` return the minimum buffer size required 
 * to write the clone fingerprint name.
 */
size_t clone_fingerprint_size();

/** `clone_print` writes the unique clone's name.
 * It assumes that the buffer has at least `clone_fingerprint_size()` bytes.
 */
void clone_print_fingerprint(char *str, const clone *clone);

/** `clone_insert_pred` inserts the predicate to the predicate set.
 */
void clone_insert_pred(clone *clone, const pred *pred);

/** `clone_test_pred` returns non-zero if the predicate is a member of the
 * clone.
 */
int clone_test_pred(const clone *clone, const pred *pred);

/** `clone_cardinality` returns the number of predicates that the clone
 * contains.
 */
int64_t clone_cardinality(const clone *clone);

/** `clone_get_predicates` stores all clone's predicates to the `pred_list`. If
 * `card != NULL`, then the number of predicates having been stored is written
 * to `*card`.
 * 
 * At maximum `size` predicates is stored. If `size` is less than the clone
 * cardinality, `clone_get_predicates` returns zero; otherwise it returns
 * non-zero.
 */
int clone_get_predicates(const clone *clone, pred *pred_list, size_t size, uint64_t *card);

/** `clone_eq` returns non-zero if two clones are equal.
 */
int clone_eq(const clone *clone1, const clone *clone2);

/** `clone_union` computes the union of two clones and write the result to the
 * third clone.
 */
void clone_union(const clone *clone1, const clone *clone2, clone *clone);

/** `clone_diff` computes the difference of two clones and write the result to
 * the third clone.
 */
void clone_diff(const clone *clone1, const clone *clone2, clone *clone);

#endif
