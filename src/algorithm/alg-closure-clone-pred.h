/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ALG_CLOSURE_CLONE_PRED_H
#define ALG_CLOSURE_CLONE_PRED_H

#include <assert.h>

#include "clone.h"
#include "hashtable.h"
#include "globals.h"
#include "closure.h"

typedef uint32_t class_idx;
typedef uint32_t pred_idx_t;

struct ccpnode {
  /** Unique identifier. */
  class_idx cidx;
  
  /** Some parent of the clone.
   * A parent of `clone` is a clone `parent` such that there exists a
   * predicate `p` such that
   *    clone == <{p} ∪ parent>.
   *
   * We heuristically select the parent such that the different between the
   * current clone and the parent is the smallest. */
  struct ccpnode *parent;
  
  /** `diff_parent` is a difference between current clone and its parent.
   * It is used to optimize the computation of the closure of the union
   * <p ∪ clone>. */
  clone diff_parent;

  /** A generator of the clone is a set of predicates such that
   *    <generator> == clone.
   *
   * The generator reflects the way how the clone was constructed first time.
   * The elements of the generator are not necessary independent.
   *
   * In theory, every clone can have many generating sets. The choice of the
   * generator for a given clone is determined by the lattice construction
   * procedure. In the current implementation the generator is initialized when
   * the clone is constructed first time and it never changes in future (even if
   * we encounter a new set of predicates that generate the same clone). */
  clone generator;

  /** A closed set of predicates, a closure of the generator. */
  clone clone;

  /** A clone-predicate closure table.
   *
   * table[ar] maps a predicate `p` of arity `ar` to the closure
   *    <{p} ∪ this_clone>
   *
   * The clone-predicate closure table requires up to 1KiB memory. We minimize
   * the memory consumption in many ways:
   *
   *   1) We consider closure-unique predicates only.
   *
   *   2) We store a part of the table for closure-unique predicates with
   *      indices >= `pidx_begin` (up to 251 inclusive) only. The predicates
   *      numbering scheme is determined by the ccplt predicate numerator.
   *
   *   3) We use 32-but class indices instead of 64-bit pointers to nodes.
   *      The node enumeration is determined to ccplt.
   */
  class_idx *children;

  size_t num_children;

  /** The index of the first predicate we use in clone-predicate closure table
   * `children`. */
  pred_idx_t pidx_begin;

  /** Enumeration functions for predicates and nodes. */
  const struct ccplt *lt;

} __attribute__ ((aligned (32)));

typedef struct ccpnode ccpnode;

/** `ccpnode_alloc` allocates memory for a ccpnode and its closure table.
 * One should call `ccpnode_free` to release the memory.
 */
ccpnode *ccpnode_alloc();

void ccpnode_free(ccpnode *c);

/** `ccpnode_parent` returns some parent of the ccpnode.
 */
ccpnode *ccpnode_parent(const ccpnode *c);

/** `ccpnode_get_child` searches the predicate-clone closure table
 * for a clone the clone <{p} ∪ c> */
ccpnode *ccpnode_get_child(const ccpnode *c, const pred *p);

/** `ccpnode_set_child` sets the result of the closure <{p} ∪ parent> to be equal
 *  to `child`.  */
void ccpnode_set_child(ccpnode *parent, const pred *p, ccpnode *child);


/******************************************************************************/
/** CCPLT (Closure Clone-Pred Lattice) */

/** Lattice representing the closure of a (closed) clone plus a predicate.
 * Only closure-unique essential predicates are considered.
 */
struct ccplt {
  /** Number of nodes in the lattice. */
  size_t num_nodes;
  
  /** A list of all lattice members (pointers to nodes).
   *
   * We store pointers to nodes here (not nodes itself) because
   * 1) we need a resizable storage;
   * 2) we want pointers to nodes be fixed (because we store them in
   *    clone-pred closure table). */
  ccpnode **nodes;
  
  /** The current capacity of `nodes` array. We realloc the memory when the
   * space becomes exhausted. The reallocation can occur only when a new node
   * is inserted to the lattice. */
  size_t capacity;

  /** A hash table to support efficient clone membership test.
   * See `lattice_lookup` */
  hashtable *ht;

  /** A structure that enumerates all closure-unique predicates with natural
   * numbers (pred_idx_t). The numbering is used in clone-predicate closure
   * table. */
  struct predicate_numerator *pred_num;
};
typedef struct ccplt ccplt;

ccplt *ccplt_alloc();

void ccplt_free(ccplt *lt);

/** `ccplt_top_clone` returns the top clone of the lattice. */
ccpnode *ccplt_top_clone(const ccplt *lt);

/** `ccplt_insert_node` inserts a new ccpnode to the lattice.
 *
 * pidx_begin is the least index of a predicate to be added to this node.
 * If a node is created on step number `s`, then pidx_begin == s+1.
 */
void ccplt_insert_node(ccplt *lt, ccpnode *c, pred_idx_t pidx_begin);

/** `ccplt_lookup` efficiently searches the lattice for a node corresponding
 * to a given clone. If it's been found, the function returns the corresponding
 * node.
 * The function returns NULL if the clone is not present in the lattice.
 */
ccpnode *ccplt_lookup(const ccplt *lt, const clone *cl);

ccpnode *ccplt_get_node(const ccplt *lt, class_idx idx);


/******************************************************************************/
struct predicate_numerator {
  /* Number of predicates. */
  size_t uniq_sz;
  
  /* uniq_preds maps a predicate index to the predicate. */
  pred *uniq_preds;
  
  /* reverse index:
   * uniq_pred_idx[ar] maps a predicate of arity `ar` to its index. */
  pred_idx_t *uniq_pred_idx[3];
};
typedef struct predicate_numerator predicate_numerator;

predicate_numerator *predicate_numerator_construct();

void predicate_numerator_free(predicate_numerator *pred_num);

static inline pred_idx_t pred_idx(const predicate_numerator *pred_num, const pred *p) {
  assert(p->arity <= 2 && "predicate numerator supports predicates of arity <= 2 only");
  pred_idx_t idx = pred_num->uniq_pred_idx[p->arity][p->data];
  assert(idx != -1 && "predicate numerator does not know this predicate");
  return idx;
}

static inline pred *idx_pred(const predicate_numerator *pred_num, size_t idx) {
  assert(idx < pred_num->uniq_sz && "predicate idx is too large");
  return &pred_num->uniq_preds[idx];
}


/******************************************************************************/
/** Lattice of all clones in R3(2) */

/** The main algorithm.
 * Construct the lattice R3(2) of predicates of arity <= 2.
 */
void latice_construct(const closure_operator *clop, ccplt *lt);

/** `ccplt_closure_clone` uses CCPLT to efficiently compute the closure of the
 * given clone. We assume that the given clone consists of closure-unique
 * essential predicates only.
 *
 * The algorithms starts traversing the lattice from the dummy clone and adds
 * predicates from `cl` one by one.
*/
ccpnode *ccplt_closure_clone(const ccplt* lt, const clone *cl);

#endif

