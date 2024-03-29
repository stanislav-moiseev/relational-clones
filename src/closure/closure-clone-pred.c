/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "pred-essential.h"
#include "closure/closure-clone-pred.h"
#include "binary/bin-closure-clone-pred.h"

struct clop_clone_pred_internals {
  ccplt *ccplt;
  clone cl_uniq;
};
typedef struct clop_clone_pred_internals clop_clone_pred_internals;

void clop_clone_pred_closure_clone_ex(void *_internals, const clone *base, const clone *suppl, clone *closure) {
  clop_clone_pred_internals *internals = (clop_clone_pred_internals *)_internals;
  clone cl;
  clone_union(base, suppl, &cl);
  assert(clone_subset(&cl, &internals->cl_uniq) && "clop_clone_pred is defined for closure-unique essential predicates only");
  
  ccpnode *closure_nd = ccplt_closure_clone(internals->ccplt, &cl);
  clone_copy(&closure_nd->clone, closure);
}

static void clop_clone_pred_internals_free(void *internals) {
  ccplt_free(((clop_clone_pred_internals *)internals)->ccplt);
  free(internals);
}

closure_operator *clop_clone_pred_read(const char *fname) {
  closure_operator *clop = malloc(sizeof(closure_operator));
  
  ccplt *ccplt = ccplt_read(fname);

  clop->ops.closure_clone_ex = clop_clone_pred_closure_clone_ex;
  clop->ops.internals_free   = clop_clone_pred_internals_free;
  
  clop->internals            = aligned_alloc(32, sizeof(clop_clone_pred_internals));
  ((clop_clone_pred_internals *)clop->internals)->ccplt = ccplt;
  closure_uniq_ess_preds(2, &((clop_clone_pred_internals *)clop->internals)->cl_uniq);

  return clop;
}

closure_operator *clop_clone_pred_alloc(ccplt *ccplt) {
  closure_operator *clop = malloc(sizeof(closure_operator));
 
  clop->ops.closure_clone_ex = clop_clone_pred_closure_clone_ex;
  clop->ops.internals_free   = clop_clone_pred_internals_free;
  clop->internals            = malloc(sizeof(clop_clone_pred_internals));
  ((clop_clone_pred_internals *)clop->internals)->ccplt = ccplt;
  closure_uniq_ess_preds(2, &((clop_clone_pred_internals *)clop->internals)->cl_uniq);

  return clop;
} 



/******************************************************************************/
/** Table of closure "clone + unique essential predicate" */

ccpnode *ccpnode_alloc() {
  ccpnode *c = aligned_alloc(32, sizeof(ccpnode));
  assert(c);

  c->cidx         = -1;
  c->parent       = NULL;
  c->children     = NULL;
  c->num_children = 0;
  c->pidx_begin   = -1;
  c->lt           = NULL;
  clone_init(&c->diff_parent);
  clone_init(&c->generator);
  clone_init(&c->clone);
  
  return c;
}

void ccpnode_free(ccpnode *c) {
  free(c->children);
  free(c);
}

ccpnode *ccpnode_parent(const ccpnode *c) {
  return c->parent;
}

ccpnode *ccpnode_get_child(const ccpnode *c, const pred *p) {
  pred_idx_t pidx = pred_idx(c->lt->pred_num, p);
  assert(pidx >= c->pidx_begin);
  return ccplt_get_node(c->lt, c->children[pidx - c->pidx_begin]);
}

void ccpnode_set_child(ccpnode *parent, const pred *p, ccpnode *child) {
  pred_idx_t pidx = pred_idx(parent->lt->pred_num, p);
  assert(pidx >= parent->pidx_begin);
  parent->children[pidx - parent->pidx_begin] = child->cidx;
}

ccplt *ccplt_alloc() {
  ccplt *lt = malloc(sizeof(ccplt));
  assert(lt);
  lt->num_nodes = 0;
  lt->capacity  = 2<<20;
  lt->nodes     = malloc(lt->capacity * sizeof(ccpnode *));
  assert(lt->nodes);
  lt->ht        = hashtable_alloc(2*lt->capacity, clone_hash, (int (*)(const void *, const void *))clone_eq);
  lt->pred_num  = NULL;
  return lt;
}

void ccplt_free(ccplt *lt) {
  for(ccpnode **c = lt->nodes; c < lt->nodes + lt->num_nodes; ++c) {
    ccpnode_free(*c);
  }
  free(lt->nodes);
  if(lt->ht) hashtable_free(lt->ht);
  if(lt->pred_num) predicate_numerator_free(lt->pred_num);
  free(lt);
}

ccpnode *ccplt_top_clone(const ccplt *lt) {
  assert(lt->num_nodes >= 1);
  return lt->nodes[0];
}

void ccplt_insert_node(ccplt *lt, ccpnode *c, pred_idx_t pidx_begin) {
  /* resize ccpnode storage if needed */
  if(lt->num_nodes == lt->capacity) {
    lt->capacity *= 2;
    lt->nodes     = realloc(lt->nodes, lt->capacity);
    assert(lt->nodes);
  }

  /* initialize uninitialized ccpnode fields*/
  c->cidx            = lt->num_nodes;
  c->lt              = lt;
  c->pidx_begin      = pidx_begin;
  assert(pidx_begin <= lt->pred_num->uniq_sz);
  c->num_children    = lt->pred_num->uniq_sz - pidx_begin;
  c->children        = malloc(c->num_children * sizeof(class_idx)); 
  assert(c->children != NULL);
  memset(c->children, 0xFF, c->num_children * sizeof(class_idx));

  /* insert ccpnode to ccplt */
  lt->nodes[lt->num_nodes] = c;
  hashtable_insert(lt->ht, &c->clone, c);

  ++lt->num_nodes;
}

ccpnode *ccplt_lookup(const ccplt *lt, const clone *cl) {
  return hashtable_lookup(lt->ht, cl);
}

ccpnode *ccplt_get_node(const ccplt *lt, class_idx idx) {
  assert(idx < lt->num_nodes && "class_idx too large");
  ccpnode *nd = lt->nodes[idx];
  assert(nd->cidx == idx);
  return nd;
}

predicate_numerator *predicate_numerator_alloc(const pred *preds, size_t sz) {
  predicate_numerator *pred_num = malloc(sizeof(predicate_numerator));
  assert(pred_num);

  pred_num->uniq_sz    = sz;
  pred_num->uniq_preds = malloc(sz * sizeof(struct pred));
  assert(pred_num->uniq_preds);
  memcpy(pred_num->uniq_preds, preds, sz * sizeof(struct pred));
  
  /* alloc mem for reverse index */
  for(uint32_t ar = 0; ar <= 2; ++ar) {
    uint64_t num = int_pow2(int_pow(K, ar));
    pred_num->uniq_pred_idx[ar] = malloc(num * sizeof(pred_idx_t)); 
    assert(pred_num->uniq_pred_idx[ar] != NULL);
    memset(pred_num->uniq_pred_idx[ar], 0xFF, num * sizeof(pred_idx_t));
  }
  
  /* construct reverse index */  
  for(size_t pidx = 0; pidx < pred_num->uniq_sz; ++pidx) {
    pred *p = pred_num->uniq_preds + pidx;
    assert(p->arity <= 2 && "predicate numerator supports predicates of arity <= 2 only");
    assert(p->data <= int_pow2(int_pow(K, p->arity)) && "predicate_numerator: broken predicate");
    pred_num->uniq_pred_idx[p->arity][p->data] = pidx;
  }
  
  return pred_num;
}

void predicate_numerator_free(predicate_numerator *pred_num) {
  free(pred_num->uniq_preds);
  for(int ar = 0; ar <= 2; ++ar) {
    free(pred_num->uniq_pred_idx[ar]);
  }
  free(pred_num);
}

void ccplt_construct_step(const closure_operator *clop, ccplt *lt, pred_idx_t pidx) {
  const pred *p = idx_pred(lt->pred_num, pidx);
  size_t cur_step_num_nodes = lt->num_nodes;
  for(ccpnode **cp = lt->nodes; cp < lt->nodes + cur_step_num_nodes; ++cp) {
    ccpnode *current = *cp;
    
    /* if the current ccpnode contains the predicate to be added, skip it */
    if(clone_test_pred(&current->clone, p)) {
      ccpnode_set_child(current, p, current);
      continue;
    }

    /* compute the closure of the union {p} ∪ current */
    clone closure;
    if(current->parent == NULL) {
      /* if the current clone is the top clone, use a direct approach */
      clone clone_p;
      clone_init(&clone_p);
      clone_insert_pred(&clone_p, p);
      closure_clone_ex(clop, &current->clone, &clone_p, &closure);
    } else {
      /* if the current clone has a parent, compute the closure <{p} ∪ current>
       * using the result of the closure of `p` and its parent:
       * <{p}∪current> == <<{p}∪parent> ∪ (current\parent)> ==
       *               == <<{p}∪parent> ∪ (current\parent\<{p}∪parent>)> */
      
      /* parent_p == <{p}∪parent> */
      ccpnode *parent_p = ccpnode_get_child(current->parent, p);
      /* the closure <{p} ∪ parent> should have already been computed */
      assert(parent_p != NULL);
      /* tmp == (current\parent) \ <{p}∪parent> */
      clone tmp;
      clone_diff(&current->diff_parent, &parent_p->clone, &tmp);
      
      closure_clone_ex(clop, &parent_p->clone, &tmp, &closure);
    }

    /* test if we've constructed a new ccpnode */
    ccpnode *child = ccplt_lookup(lt, &closure);
    assert(child != current);
    if(child == NULL) {
      /* if we've constructed a new ccpnode, add it to the ccplt */
      child = ccpnode_alloc(lt);
      child->parent = current;
      clone_diff(&closure, &current->clone, &child->diff_parent);
      clone_copy(&current->generator, &child->generator);
      clone_insert_pred(&child->generator, p);
      clone_copy(&closure, &child->clone);
      ccplt_insert_node(lt, child, pidx+1);
    } else {
      /* If we've found a new parent for current clone, check if the difference
       * between it and the clone is smaller than the current child->diff_parent.
       * We want to select the parent such that the different is the smallest.
       * This heuristics gives significant overall computation speed-up.
       *
       * We apply this heuristics for `current < child` only because on each step
       * the parents must be proceeded strictly before their children,
       * otherwise the closure of a child will depend on a not-yet-computed
       * closure of its parent */
      if(current < child) {
        size_t diff_card1 = clone_cardinality(&child->diff_parent);
        clone diff2;
        clone_diff(&closure, &current->clone, &diff2);
        size_t diff_card2 = clone_cardinality(&diff2);
        if(diff_card2 < diff_card1) {
          child->parent = current;
          clone_copy(&diff2, &child->diff_parent);
        }
      }
    }

    /* link the current ccpnode and the child ccpnode */
    ccpnode_set_child(current, p, child);
  }
}

void ccplt_construct(const closure_operator *clop, ccplt *lt) {
  /* factorize all essential predicates by their closure
   * and select predicates with unique closure */
  size_t sz;
  pred *preds;
  construct_closure_uniq_ess_preds(2, &preds, &sz);
  lt->pred_num = predicate_numerator_alloc(preds, sz);
  free(preds);

  /* start from a ccplt containing just one clone */
  ccpnode *top = ccpnode_alloc(lt);
  top->clone = *top_clone();
  ccplt_insert_node(lt, top, 0);
  
  /* iteratively construct new ccpnodes */
  for(pred_idx_t pidx = 0; pidx < lt->pred_num->uniq_sz; ++pidx) {
    ccplt_construct_step(clop, lt, pidx);
    fprintf(stderr, "%u\t %lu\n", pidx, lt->num_nodes);
  }
}


/** `ccplt_closure_clone` uses CCPLT to efficiently compute the closure of the
 * given clone .*/
ccpnode *ccplt_closure_clone(const ccplt* lt, const clone *cl) {
  /* Start traversing the lattice from the top clone and add predicates from
   * `cl` one by one. */
  ccpnode *nd = ccplt_top_clone(lt);
  assert(nd != NULL);
  /* In order to use LT, we need to process predicates form the given clone
   * in a specific order. */
  assert(lt->pred_num != NULL);
  for(pred *p = lt->pred_num->uniq_preds; p < lt->pred_num->uniq_preds + lt->pred_num->uniq_sz; ++p) {
    if(clone_test_pred(cl, p)) {
      nd = ccpnode_get_child(nd, p);
    }
  }
  return nd;
}
