/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "fun-majority.h"
#include "pred-essential.h"
#include "closure.h"
#include "closure/closure-straightforward.h"
#include "closure/closure-clone-pred.h"
#include "binary/bin-common.h"
#include "binary/bin-closure-clone-pred.h"

#include "test-random.h"

void test_pred_is_essential() {
  pred p_false, p_true, p_eq0, p_eq1, p_eq2, p_eq, p_neq;
  assert(pred_construct(0, "0", &p_false));
  assert(pred_construct(0, "1", &p_true));
  assert(pred_construct(1, "001", &p_eq0));
  assert(pred_construct(1, "010", &p_eq1));
  assert(pred_construct(1, "100", &p_eq2));
  assert(pred_construct(2, "100010001", &p_eq));
  assert(pred_construct(2, "011101110", &p_neq));

  assert(pred_is_essential(&p_false));
  assert(pred_is_essential(&p_true));
  assert(pred_is_essential(&p_eq));
  assert(pred_is_essential(&p_neq));
  assert(pred_is_essential(&p_eq0));
  assert(pred_is_essential(&p_eq1));
  assert(pred_is_essential(&p_eq2));
  
  pred p_12;
  assert(pred_construct(1, "110", &p_12));
  assert(pred_is_essential(&p_12));
}

void test_pred_preserves_majority() {
  pred *ess_preds;
  size_t ess_sz;
  get_essential_predicates(2, &ess_preds, &ess_sz);

 
  size_t num = 0;
  for(const pred *p = p = ess_preds; p < ess_preds + ess_sz; ++p) {
    if(pred_preserves_majority(p)) ++num;
  }
  assert(num == 410);
}


/** Check the number of all essential predicates of arity <= 2. */
void test_pred_num_essential_preds() {
  pred *ess_preds;
  size_t ess_sz;
  
  get_essential_predicates(0, &ess_preds, &ess_sz);
  assert(ess_sz == 2);
    
  get_essential_predicates(1, &ess_preds, &ess_sz);
  assert(ess_sz == 2 + 6);

  get_essential_predicates(2, &ess_preds, &ess_sz);
  assert(ess_sz == 2 + 6 + 462);

  free(ess_preds);
}

/* Check the number of all closure-unique essential predicates of arity <= 2. */
void test_pred_num_closure_uniq_preds() {
  pred *uniq_preds;
  size_t uniq_sz;

  construct_closure_uniq_ess_preds(0, &uniq_preds, &uniq_sz);
  assert(uniq_sz == 1);
  
  construct_closure_uniq_ess_preds(1, &uniq_preds, &uniq_sz);
  assert(uniq_sz == 1 + 6);

  construct_closure_uniq_ess_preds(2, &uniq_preds, &uniq_sz);
  assert(uniq_sz == 1 + 6 + 244);
  
  free(uniq_preds);
}

void test_clone_closure1() {
  closure_operator *clop = clop_alloc_straightforward();

  pred p_false, p_true, p_eq0, p_eq1, p_eq2, p_eq, p_neq;
  assert(pred_construct(0, "0", &p_false));
  assert(pred_construct(0, "1", &p_true));
  assert(pred_construct(1, "001", &p_eq0));
  assert(pred_construct(1, "010", &p_eq1));
  assert(pred_construct(1, "100", &p_eq2));
  assert(pred_construct(2, "100010001", &p_eq));
  assert(pred_construct(2, "011101110", &p_neq));

  struct clone clone;
  clone_init(&clone);
  clone_insert_pred(&clone, &p_false);
  clone_insert_pred(&clone, &p_true);
  clone_insert_pred(&clone, &p_eq);
  clone_insert_pred(&clone, &p_eq0);
  clone_insert_pred(&clone, &p_eq1);
  clone_insert_pred(&clone, &p_eq2);

  struct clone closure;
  closure_clone(clop, &clone, &closure);
  assert(clone_eq(&clone, &closure));

  clone_insert_pred(&clone, &p_neq);
  closure_clone(clop, &clone, &closure);
  for(clone_iterator it = clone_iterator_begin(&closure); !clone_iterator_end(&closure, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    assert(pred_is_essential(&pred));
  }

  clop_free(clop);
}

void test_clone_closure2() {
  closure_operator *clop = clop_alloc_straightforward();

  pred p3_1_1, p3_1_3, p3_2_b, p3_2_11;
  pred_construct(1, "001", &p3_1_1);
  pred_construct(1, "011", &p3_1_3);
  pred_construct(2, "000001011", &p3_2_b);
  pred_construct(2, "000010001", &p3_2_11);
  
  struct clone cl = *top_clone();
  clone_insert_pred(&cl, &p3_2_b);
  
  struct clone closure;
  closure_clone(clop, &cl, &closure);

  struct clone expected_closure = *top_clone();
  clone_insert_pred(&expected_closure, &p3_1_1);
  clone_insert_pred(&expected_closure, &p3_1_3);
  clone_insert_pred(&expected_closure, &p3_2_b);
  clone_insert_pred(&expected_closure, &p3_2_11);
  
  assert(clone_eq(&closure, &expected_closure));

  clop_free(clop);
}


/** Test that the implementation of the closure operator based on the precomputed
 * closure of clone plus a predicate gives the same result as the
 * straightforward implementation. */
void test_closure_clone_pred(const char *fname) {
  closure_operator *clop_sf = clop_alloc_straightforward();
  closure_operator *clop_cp = clop_clone_pred_read(fname);

  clone uniq_ess;
  closure_uniq_ess_preds(2, &uniq_ess);

  for(int i = 0; i < 1000; ++i) {
    /* Generate a random clone and compute its closure using different
     * implementations of closure operator. */
    clone cl;
    random_clone(&cl);
    clone_union(top_clone(), &cl, &cl);
    clone_intersection(&cl, &uniq_ess, &cl);
        
    clone closure_sf, closure_cp;
    clone_union(top_clone(), &cl, &cl);
    closure_clone(clop_sf, &cl, &closure_sf);

    /* remove dummy true(0) and eq(2) that are not closure-uniq;
     * otherwise an assertion in clop_closure_clone_pred will fail. */
    clone_intersection(&cl, &uniq_ess, &cl);
    closure_clone(clop_cp, &cl, &closure_cp);
    
    /* As long as `closure_cp` constains closure-unique essential predicates
    * only, but `closure_sf` contains all essential predicates, we need to
    * filter `closure_sf`. */
    clone_intersection(&closure_sf, &uniq_ess, &closure_sf);

    if(!clone_eq(&closure_sf, &closure_cp)) {
      printf("Error\n");
      printf("================================================================\n");
      printf("Initial set of predicates:\n");
      clone_print_verbosely(stdout, &cl);
      
      printf("================================================================\n");
      printf("Difference closure_sf \\ closure_cp:\n");
      clone diff1;
      clone_diff(&closure_sf, &closure_cp, &diff1);
      clone_print_verbosely(stdout, &diff1);
      
      printf("================================================================\n");
      printf("Difference closure_cp \\ closure_sf:\n");
      clone diff2;
      clone_diff(&closure_cp, &closure_sf, &diff2);
      clone_print_verbosely(stdout, &diff2);
      
      printf("================================================================\n");
      printf("Intersection closure_cp ∩ closure_sf:\n");
      clone inter;
      clone_intersection(&closure_sf, &closure_cp, &inter);
      clone_print_verbosely(stdout, &inter);
      
      printf("================================================================\n");
      exit(1);
    }
  }
  
  clop_free(clop_cp);
  clop_free(clop_sf);
}

int main() {
  printf("test-essential-predicates:\t"); fflush(stdout);
  test_pred_is_essential();
  test_pred_num_essential_preds();
  test_pred_num_closure_uniq_preds();
  printf("Ok.\n");

  printf("test-pred-preserves-majority:\t"); fflush(stdout);
  test_pred_preserves_majority();
  printf("Ok.\n");
 
  printf("test-clone-closure:\t\t"); fflush(stdout);
  test_clone_closure1();
  test_clone_closure2();
  printf("Ok.\n");

  printf("test-closure-clone-pred:\t"); fflush(stdout);
  test_closure_clone_pred("data/closure-clone-pred.2016");
  printf("Ok.\n");
}
