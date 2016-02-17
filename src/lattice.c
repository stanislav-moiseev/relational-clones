/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "lattice.h"
#include "hashtable.h"

class *class_alloc(const ccpnode *nd) {
  class *c = aligned_alloc(32, sizeof(class));
  c->cidx           = nd->cidx;
  c->lidx           = -1;
  c->cpos           = -1;
  clone_copy(&nd->clone, &c->clone);
  c->num_subclasses = 0;
  c->cap_subclasses = 64;
  c->subclasses     = malloc(c->cap_subclasses * sizeof(class_idx));
  return c;
}

void class_free(class *c) {
  free(c->subclasses);
  free(c);
}

void class_add_subclass(class *c, class_idx subclass_idx) {
  if(c->num_subclasses == c->cap_subclasses) {
    c->cap_subclasses *= 2;
    c->subclasses = realloc(c->subclasses, c->cap_subclasses * sizeof(class_idx));
    assert(c->subclasses);
  }
  assert(c->num_subclasses < c->cap_subclasses);
  c->subclasses[c->num_subclasses] = subclass_idx;
  ++c->num_subclasses;
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
  lt->classes     = NULL;
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

static uint32_t class_idx_hash(const void *cidx) {
  return *(class_idx *)cidx;
}

static int class_idx_eq(const void *cidx1, const void *cidx2) {
  return *(class_idx *)cidx1 == *(class_idx *)cidx2;
}
  
void lattice_construct_layers(lattice *lt, const ccplt *ccplt) {
  /* copy clones from ccplt */
  assert(lt->classes == NULL);  /* We suppose that the lattice is empty. */
  lt->num_classes = ccplt->num_nodes;
  lt->classes = aligned_alloc(32, lt->num_classes * sizeof(class *));
  for(size_t i = 0; i < lt->num_classes; ++i) {
    lt->classes[i] = class_alloc(ccplt->nodes[i]);
  }

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
  layer *lr = layer_alloc();
  lattice_add_layer(lt, lr);
  ccpnode *top_node = ccplt_top_clone(ccplt);
  layer_add_class(lr, lattice_get_class(lt, top_node->cidx));
  hashtable_insert(ht, &top_node->cidx, &top_node->cidx);

  printf("layer\tclones to search\tlayer size\t\tprogress\n");
  printf("idx\tfor maximal\t\t(num of maximal clones)\n");
  size_t classes_constr = 0;    /* number of classes constructed so far */
  while(ht->size > 0) {
    printf("%lu\t%lu\t\t\t", lt->num_layers-1, ht->size); fflush(stdout);
        
    layer *new_lr = layer_alloc();    /* next layer, to be constructed */
    lattice_add_layer(lt, new_lr);

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
        layer_add_class(new_lr, lattice_get_class(lt, *cidx));
      }
    }

    free(bunch);

    /* Remove maximal clones that's been found from further consideration. */
    for(class_idx *cidx = new_lr->classes; cidx < new_lr->classes + new_lr->num_classes; ++cidx) {
      hashtable_remove(ht, cidx);
    }

    /* Insert all direct proper subclones of the clones from the new layer to
     * the bunch of clones from where to select maximal on the next step. */
    for(class_idx *cidx = new_lr->classes; cidx < new_lr->classes + new_lr->num_classes; ++cidx) {
      const ccpnode *nd = ccplt_get_node(ccplt, *cidx);
      for(class_idx *child_cidx = nd->children; child_cidx < nd->children + nd->num_children; ++child_cidx) {
        if(*child_cidx != *cidx) {
          hashtable_insert(ht, child_cidx, child_cidx);
        }
      }
    }

    lr = new_lr;
    classes_constr += lr->num_classes;
    printf("%lu\t\t\t%.0f%%\n", lr->num_classes,
           100. * classes_constr / lt->num_classes);
  }

  assert(classes_constr == lt->num_classes);
  hashtable_free(ht);
}

