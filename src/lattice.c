/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "lattice.h"
#include "hashtable.h"

class *class_alloc(const clone *cl) {
  class *c = aligned_alloc(32, sizeof(class));
  c->cidx        = -1;
  c->lidx        = -1;
  c->cpos        = -1;
  clone_copy(cl, &c->clone);
  c->num_maxsubs = 0;
  c->cap_maxsubs = 64;
  c->maxsubs     = malloc(c->cap_maxsubs * sizeof(class_idx));
  return c;
}

void class_free(class *c) {
  free(c->maxsubs);
  free(c);
}

void class_add_subclass(class *c, class_idx subclass_idx) {
  if(c->num_maxsubs == c->cap_maxsubs) {
    assert(c->cap_maxsubs > 0);
    c->cap_maxsubs *= 2;
    c->maxsubs = realloc(c->maxsubs, c->cap_maxsubs * sizeof(class_idx));
    assert(c->maxsubs);
  }
  assert(c->num_maxsubs < c->cap_maxsubs);
  c->maxsubs[c->num_maxsubs] = subclass_idx;
  ++c->num_maxsubs;
}

layer *layer_alloc() {
  layer *lr = malloc(sizeof(layer));
  lr->lidx        = -1;
  lr->num_classes = 0;
  lr->cap_classes = 4096;
  lr->classes     = malloc(lr->cap_classes * sizeof(class_idx));
  return lr;
}

void layer_free(layer *lr) {
  free(lr->classes);
  free(lr);
}

void layer_add_class(layer *lr, class *c) {
  if(lr->num_classes == lr->cap_classes) {
    lr->cap_classes *= 2;
    lr->classes = realloc(lr->classes, lr->cap_classes * sizeof(class_idx));
  }
  assert(lr->num_classes < lr->cap_classes);
  lr->classes[lr->num_classes] = c->cidx;

  c->lidx = lr->lidx;
  c->cpos = lr->num_classes;

  ++lr->num_classes;
}

lattice *lattice_alloc() {
  lattice *lt = malloc(sizeof(lattice));
  lt->num_layers  = 0;
  lt->cap_layers  = 64;
  lt->layers      = malloc(lt->cap_layers * sizeof(layer *));
  lt->num_classes = 0;
  lt->cap_classes = 1024;
  lt->classes     = aligned_alloc(32, lt->cap_classes * sizeof(class *));
  return lt;
}

void lattice_free(lattice *lt) {
  for(layer **lrp = lt->layers; lrp < lt->layers + lt->num_layers; ++lrp) {
    layer_free(*lrp);
  }
  free(lt->layers);
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class_free(*cp);
  }
  free(lt->classes);
  free(lt);
}

void lattice_add_class(lattice *lt, class *c) {
  if(lt->num_classes == lt->cap_classes) {
    lt->cap_classes *= 2;
    lt->classes = realloc(lt->classes, lt->cap_classes * sizeof(class *));
  }
  assert(lt->num_classes < lt->cap_classes);
  lt->classes[lt->num_classes] = c;

  c->cidx = lt->num_classes;
  
  ++lt->num_classes;
}

void lattice_add_layer(lattice *lt, layer *lr) {
  if(lt->num_layers == lt->cap_layers) {
    lt->cap_layers *= 2;
    lt->layers = realloc(lt->layers, lt->cap_layers * sizeof(layer *));
  }
  assert(lt->num_layers < lt->cap_layers);
  lt->layers[lt->num_layers] = lr;

  lr->lidx = lt->num_layers;
  
  ++lt->num_layers;
}

void lattice_load_classes_from_ccplt(lattice *lt, const ccplt *ccplt) {
  /* copy clones from ccplt */
  assert(lt->num_classes == 0);  /* We suppose that the lattice is empty. */
  for(class_idx cidx = 0; cidx < lt->num_classes; ++cidx) {
    ccpnode *nd = ccplt_get_node(ccplt, cidx);
    class *c    = class_alloc(&nd->clone);
    lattice_add_class(lt, c);
    assert(c->cidx == nd->cidx);
  }
  assert(lt->num_classes = ccplt->num_nodes);
}

/* Hash function that computes hashes for class indices.
 * In current implementation the functions uses `cidx` itself as its hash value.
 * The hashing function is used in a hash table at `lattice_construct_layers`
 */
static uint32_t class_idx_hash(const void *cidx) {
  return *(class_idx *)cidx;
}
/* Comparison function used in a hash table at `lattice_construct_layers`
 */
static int class_idx_eq(const void *cidx1, const void *cidx2) {
  return *(class_idx *)cidx1 == *(class_idx *)cidx2;
}
  
void lattice_construct_layers_ccplt(lattice *lt, const ccplt *ccplt) {
  /* We will construct layers iteratively. On each step, `ht` is the bunch of
   * clones where to select maximal clones from.
   *
   *   1. We start from the set M(0) containing just one top clone.
   *
   *   2. Then we select the set `M(0)_maximal` of all maximal clones among the
   *      direct proper subclones of the top clone. M(0)_maximal will form the
   *      layer(1).
   *
   *   3. At each step we compute the set M(n)_maximal of all maximal clones in
   *      M(n). This set forms the current layer, layer(n) = M(n)_maximal.
   *
   *      M(n+1) = (M(n) \ M(n)_maximal) ∪ (direct_subclones_of_M(n)_maximal),
   *
   *      where by direct proper subclones of clone `c` we mean the set
   *      {<c ∪ p> | p is a closure-unique essential predicate,
   *                 <c ∪ p> ≠ c}.
   */
  hashtable *ht = hashtable_alloc(lt->num_classes, class_idx_hash, class_idx_eq);

  /* Create the top layer containing just one top clone. */
  ccpnode *top_node = ccplt_top_clone(ccplt);
  hashtable_insert(ht, &top_node->cidx, &top_node->cidx);

  printf("layer\tclones to search\tlayer size\t\tprogress\n");
  printf("idx\tfor maximal\t\t(num of maximal clones)\n");
  size_t classes_constr = 0;    /* number of classes constructed so far */
  while(ht->size > 0) {
    printf("%lu\t%lu\t\t\t", lt->num_layers, ht->size); fflush(stdout);
        
    layer *lr = layer_alloc();    /* next layer, to be constructed */
    lattice_add_layer(lt, lr);

    /* [optimization] temporary copy all class indices from hash table to normal
     * list not to traverse the whole hash table in the double for-loop
     * below. */
    class_idx *bunch = malloc(ht->size * sizeof(class_idx));
    size_t i = 0;
    for(hashtable_iterator it = hashtable_iterator_begin(ht); !hashtable_iterator_end(&it); hashtable_iterator_next(&it)) {
      class_idx *cidx = hashtable_iterator_deref(&it)->key;
      bunch[i] = *cidx;
      ++i;
    }

    /* Find all maximal clones in the current bunch of clones */
    for(class_idx *cidx = bunch; cidx < bunch + ht->size; ++cidx) {
      clone *cl = &lattice_get_class(lt, *cidx)->clone;
      int flag = 1;
      for(class_idx *cidx2 = bunch; cidx2 < bunch + ht->size; ++cidx2) {
        if(cidx2 == cidx) continue;
        clone *cl2 = &lattice_get_class(lt, *cidx2)->clone;
        if(clone_subset(cl2, cl)) {
          flag = 0;
          break;
        }
      }
      /* If `cl` is a maximal clone, insert it to the layer being constructed. */
      if(flag) {
        layer_add_class(lr, lattice_get_class(lt, *cidx));
      }
    }

    free(bunch);

    /* Remove maximal clones that's been found from further consideration. */
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      hashtable_remove(ht, cidx);
    }

    /* Insert all direct proper subclones of the clones from the new layer to
     * the bunch of clones from where to select maximal on the next step. */
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      const ccpnode *nd = ccplt_get_node(ccplt, *cidx);
      for(pred *p = ccplt->pred_num->uniq_preds; p < ccplt->pred_num->uniq_preds + ccplt->pred_num->uniq_sz; ++p) {
        clone cl;
        clone_copy(&nd->clone, &cl);
        clone_insert_pred(&cl, p);
        ccpnode *sub = ccplt_closure_clone(ccplt, &cl);
        if(sub->cidx != *cidx) {
          hashtable_insert(ht, &sub->cidx, &sub->cidx);
        }
      }
    }

    classes_constr += lr->num_classes;
    printf("%lu\t\t\t%.0f%%\n", lr->num_classes,
           100. * classes_constr / lt->num_classes);
  }

  assert(classes_constr == lt->num_classes);
  hashtable_free(ht);
}

void lattice_construct_maximal_subclones_ccplt(lattice *lt, const ccplt *ccplt) {
  printf("constructing maximal proper subclones"); fflush(stdout);
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;

    /* If some maximal proper subclones were added to `c` previously, just skip
     * them. We will recompute all them. */
    c->num_maxsubs = 0;
    
    /* Get a list of all direct proper subclones of `c`. */
    ccpnode *dirsubs[ccplt->pred_num->uniq_sz];
    size_t dirsubs_sz = 0;
    for(pred *p = ccplt->pred_num->uniq_preds; p < ccplt->pred_num->uniq_preds + ccplt->pred_num->uniq_sz; ++p) {
      clone cl;
      clone_copy(&c->clone, &cl);
      clone_insert_pred(&cl, p);
      ccpnode *sub = ccplt_closure_clone(ccplt, &cl);
      /* check that `sub` is a proper subset. */
      if(sub->cidx == c->cidx) continue;
      /* check that `sub` is new. */
      int flag = 1;
      for(ccpnode **sub2 = dirsubs; sub2 < dirsubs + dirsubs_sz; ++sub2) {
        if((*sub2)->cidx == sub->cidx) {
          flag = 0;
          break;
        }
      }
      /* If we've found a new direct proper subclone, insert it the list. */
      if(flag) {
        assert(dirsubs_sz < ccplt->pred_num->uniq_sz);
        dirsubs[dirsubs_sz] = sub;
        ++dirsubs_sz;
      }
    }

    /* Find all maximal subclones among direct proper subclones of `c`. */
    for(ccpnode **subp = dirsubs; subp < dirsubs + dirsubs_sz; ++subp) {
      ccpnode *sub = *subp;

      /* test that we haven't inserted this subclone yet. */
      int flag = 1;
      for(class_idx *sub2_cidx = c->maxsubs; sub2_cidx < c->maxsubs + c->num_maxsubs; ++sub2_cidx) {
        if(*sub2_cidx == sub->cidx) {
          flag = 0;
          break;
        }
      }
      if(!flag) continue;

      /* test that the current child clone is a maximal subclone of `c`. */
      flag = 1;
      for(ccpnode **sub2p = dirsubs; sub2p < dirsubs + dirsubs_sz; ++sub2p) {
        ccpnode *sub2 = *sub2p;
        if(sub2->cidx == sub->cidx) continue;
        if(clone_subset(&sub2->clone, &sub->clone)) {
          flag = 0;
          break;
        }
      }

      /* if `sub` is a new maximal subclone, insert it to the list of maximal
       * subclones of `c`. */
      if(flag) {
        class_add_subclass(c, sub->cidx);
      }
    }

    if(lt->num_classes >= 40);
    if(c->cidx % (lt->num_classes / 40) == 0) {
      printf("."); fflush(stdout);
    }
  }
  printf("Ok.\n");
}

/** Sorting function for maximal proper subclones of a given clone. */
static int subcl_cmp(const void *cidx1p, const void *cidx2p, void *lt) {
  class *sub1 = lattice_get_class((lattice *)lt, *(class_idx *)cidx1p);
  class *sub2 = lattice_get_class((lattice *)lt, *(class_idx *)cidx2p);
  if(sub1->lidx < sub2->lidx) return -1;
  if(sub1->lidx == sub2->lidx) {
    if(sub1->cpos < sub2->cpos) return -1;
    if(sub1->cpos == sub2->cpos) return 0;
    return 1;
  }
  return 1;
}

void lattice_sort_maximal_subclones(lattice *lt) {
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    qsort_r(c->maxsubs, c->num_maxsubs, sizeof(class_idx), subcl_cmp, lt);
  }
}
