/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef CLONE_H
#define CLONE_H

#include <stdint.h>

#include "pred.h"

#define CLONE_DATA2_SIZE 8      /* for K==3 */

struct clone {
  /* predicates of arity 2
   * data2 should be 32 byte aligned to support AVX instructions in clone_union. */
  uint64_t data2[CLONE_DATA2_SIZE];
  /* predicates of arity 1 */
  uint32_t data1;
  /* predicates of arity 0 */
  uint32_t data0;
} __attribute__ ((aligned (32)));

typedef struct clone clone;

/** `clone_consistent` returns non-zero if the internal structure of the clone
 * is consistent. In particular, it checks that the `struct clone` contains
 * enough bits to store the predicates of arity <= 2.
 */
int clone_consistent(const clone *clone);

/** `clone_hash` is a 32-bit hashing function for clones.
 */
uint32_t clone_hash(const void *clone);


/******************************************************************************/
/** printing functions */

/** `clone_fingerprint_size` return the minimum buffer size required 
 * to write the clone fingerprint name.
 */
size_t clone_fingerprint_size();

/** `clone_print` writes the unique clone's name.
 * It assumes that the buffer has at least `clone_fingerprint_size()` bytes.
 */
void clone_print_fingerprint(char *str, const clone *clone);

/** `clone_print_verbosely` writes a list of all predicates from the clone
 * `clone`.
 */
void clone_print_verbosely(FILE *fd, const clone *clone);


/******************************************************************************/
/** operations over clones and predicates */

/** `clone_insert_pred` inserts the predicate to the predicate set.
 */
void clone_insert_pred(clone *clone, const pred *pred);

void clone_remove_pred(clone *clone, const pred *pred);

/** `clone_test_pred` returns non-zero if the predicate is a member of the
 * clone.
 */
int clone_test_pred(const clone *clone, const pred *pred);

/** `clone_cardinality` returns the number of predicates that the clone
 * contains.
 */
uint64_t clone_cardinality(const clone *clone);


/******************************************************************************/
/** operations over clones */

/** `clone_init` initializes the clone to be an empty clone.
 */
void clone_init(clone *clone);

/** `clone_copy` copies `clone` to `copy`.
 */
void clone_copy(const clone *clone, struct clone *copy);

/** `clone_union` computes the union of two clones and write the result to the
 * third clone.
 */
void clone_union(const clone *clone1, const clone *clone2, clone *clone);

void clone_intersection(const clone *clone1, const clone *clone2, clone *clone);

/** `clone_diff` computes the difference of two clones and write the result to
 * the third clone.
 */
void clone_diff(const clone *clone1, const clone *clone2, clone *clone);


/******************************************************************************/
/** relations over clones */

/** `clone_is_empty` returns non-zero if the clone is empty.
 */
int clone_is_empty(const clone *clone);

/** `clone_eq` returns non-zero if two clones are equal.
 */
int clone_eq(const clone *clone1, const clone *clone2);

/** `clone_subset` returns non-zero if `clone1` is a subset of `clone2`.
 */
int clone_subset(const clone *clone1, const clone *clone2);


/******************************************************************************/
/** clone iterators */

/** clone_iterator makes possible to iterate over all predicates of the clone. */
struct clone_iterator {
  const clone *clone;
  int64_t offset;
  int64_t shift;
};

typedef struct clone_iterator clone_iterator;

clone_iterator clone_iterator_begin(const clone *clone);

int clone_iterator_end(const clone *clone, clone_iterator *it);

void clone_iterator_next(clone_iterator *it);

/** `clone_iterator_deref` returns the predicate the iterator is currently
    pointing to. */
pred clone_iterator_deref(const clone_iterator *it);

/** `clone_get_predicates` stores all clone's predicates to the `pred_list`;
 * the number of predicates having been stored is written to `*size`.
 * The function allocates an array large enough to hold all the predicates.
 * The pointer should be free'd to release the storage.
 * On success, `clone_get_predicates` returns non-zero.
 */
void clone_get_predicates(const clone *clone, pred **pred_list, uint64_t *size);


#endif

