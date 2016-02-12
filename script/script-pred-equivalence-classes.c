/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This script constructs all 251 equivalence classes of predicates.
 *
 * Two essential predicates p1 and p2 are called /closure-equivalent/
 * if <false(0), true(1), eq(2), p1}> == <false(0), true(1), eq(2), p2}>.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "pred-essential.h"
#include "clone.h"
#include "closure/closure-straightforward.h"
#include "hashtable.h"

void script_closure_pred_equivalence_classes() {
  closure_operator *clop = clop_alloc_straightforward();

  pred *ess_preds;
  size_t ess_sz;
  get_essential_predicates(2, &ess_preds, &ess_sz);

  /** We use a hash table to store a mapping between clones (equivalence
   * classes) and predicates that generate those clones (closure-equivalent
   * predicates). */
  hashtable *ht = hashtable_alloc(512, clone_hash, (int (*)(const void *, const void *))clone_eq);

  /* construct the closure of all essential predicates */
  for(pred *p = ess_preds; p < ess_preds + ess_sz; ++p) {
    clone *closure = aligned_alloc(32, sizeof(clone));
    assert(closure);
    closure_one_pred(clop, p, closure);
    /* lookup equivalence class corresponding to `p` */
    clone *equiv_preds = hashtable_lookup(ht, closure);
    if(equiv_preds == NULL) {
      equiv_preds = malloc(sizeof(clone));
      assert(equiv_preds);
      clone_init(equiv_preds);
      hashtable_insert(ht, closure, equiv_preds);
    } else {
      free(closure);
    }
    clone_insert_pred(equiv_preds, p);
  }

  /* print the equivalence classes */
  int idx = 1;
  for(hashtable_iterator it = hashtable_iterator_begin(ht); !hashtable_iterator_end(&it); hashtable_iterator_next(&it)) {
    hash_elem *elem = hashtable_iterator_deref(&it);
    printf("====== class %u ====================================\n", idx);
    for(clone_iterator itc = clone_iterator_begin((clone *)elem->value); !clone_iterator_end((clone *)elem->value, &itc); clone_iterator_next(&itc)) {
      pred p = clone_iterator_deref(&itc);
      printf("%s\t%s\n",
             pred_print_fingerprint(&p),
             pred_print_extensional_ex(&p));
    }
    printf("\n");

    free(elem->key);
    free(elem->value);
    ++idx;
  }
  
  hashtable_free(ht);
  free(ess_preds);
  clop_free(clop);
}

int main() {
  printf("script-pred-equivalence-classes:\n"); fflush(stdout);
  script_closure_pred_equivalence_classes();
  printf("Ok.\n");
}
