#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "fun.h"
#include "pred.h"
#include "utils.h"

/** Construct a random string representing predicate's extensional. */
void random_pred_extensional(uint64_t arity, char *str) {
  srand(clock());
  
  int shift = int_pow(K, arity);
  /* char str[shift+1]; */
  for(int i = 0; i < shift; ++i) {
    if((float)rand()/RAND_MAX > 0.5) {
      str[i] = '1';
    } else {
      str[i] = '0';
    }
  }
  str[shift] = 0;
}

void random_pred(pred *p) {
  uint32_t ar = rand() % 3;
  char str[pred_print_extensional_size()];
  random_pred_extensional(ar, str);
  pred_construct(ar, str, p);
}

void random_clone(clone *cl) {
  clone_init(cl);
  int num = rand() % (int_pow2(int_pow(K, 2)));
  for(int i = 0; i < num; ++i) {
    pred p;
    random_pred(&p);
    clone_insert_pred(cl, &p);
  }
}


/** Test that `pred_construct` returns a valid predicate.
 */
void test_pred_construct() {
  srand(clock());

  uint64_t arity = 0;
  do {
  int shift = int_pow(K, arity);
    for(int j = 0; j < 2*shift; ++j) {
      char str[pred_print_extensional_size()];
      random_pred_extensional(arity, str);
      
      pred pred;
      assert(pred_construct(arity, str, &pred));
      assert(pred_consistent(&pred));
      
      char str2[pred_print_extensional_size()];
      pred_print_extensional(str2, &pred);
      assert(strcmp(str, str2) == 0);
    }
      
    ++arity;
  } while (int_pow(K, arity) <= 64);
}

void test_fun_scan() {
  const char str[] = "fun3_5_200000000000000000000000000000011011010000000010000000000000000010000000010000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
  fun fun;
  fun_scan(str, &fun);

  char *str2 = fun_print(&fun);
  assert(strcmp(str, str2) == 0);
  free(str2);
}

static void clone_union_straightforward(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 | clone2->data0;
  clone->data1 = clone1->data1 | clone2->data1;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = clone1->data2[offset] | clone2->data2[offset];
  }
}

/** Test that the implementation of clone_union using AVX instructions is
 * equivalent to the straightforward implementation. */
void test_clone_union() {
  for(int i = 0; i < 100; ++i) {
    clone cl1, cl2;
    random_clone(&cl1);
    random_clone(&cl2);
    
    clone cl3, cl4;
    clone_union_straightforward(&cl1, &cl2, &cl3);
    clone_union(&cl1, &cl2, &cl4);
    
    assert(clone_eq(&cl3, &cl4));
  }
}


void test_clone_iterator() {
  for(int i = 0; i < 1000; ++i) {
    /* construct random clone, but store the list of predicates it consist of */
    clone cl;
    clone_init(&cl);
  
    size_t num = 10;
    pred preds[num];
    for(int i = 0; i < num; ++i) {
      random_pred(preds+i);
      clone_insert_pred(&cl, preds+i);
    }

    /* use clon iterator to extract predicates */
    pred *plist;
    size_t sz;
    clone_get_predicates(&cl, &plist, &sz);

    /* compare that the result of clone iterator coincide with original list of
     * predicates */
    int flag = 1;
    for(int i = 0; i < num; ++i) {
      int j;
      for(j = 0; j < sz; ++j) {
        if(pred_eq(preds+i, plist+j)) break;
      }
      if(j == sz) { flag = 0; break; }
    }
    if(flag) {
      for(int j = 0; j < sz; ++j) {
        int i;
        for(i = 0; i < num; ++i) {
          if(pred_eq(preds+i, plist+j)) break;
        }
        if(i == num) { flag = 0; break; }
      }
    }

    if(!flag) {
      printf("\nError. Clone iterator gives:\n");
      clone_print_verbosely(stdout, &cl);
      printf("\nBut original predicates were:\n");
      for(pred *p = preds; p < preds + num; ++p) {
        char str[pred_print_extensional_size()];
        pred_print_extensional(str, p);
        printf("%s\n", str);
      }
      return;
    }

    free(plist);
  }
}

int main() {
  printf("test-pred-construct:\t\t"); fflush(stdout);
  test_pred_construct();
  printf("Ok.\n");

  printf("test-fun-scan:\t\t\t"); fflush(stdout);
  test_fun_scan();
  printf("Ok.\n");

  printf("test-clone-union:\t\t"); fflush(stdout);
  test_clone_union();
  printf("Ok.\n");

  printf("test-clone-iterator:\t\t"); fflush(stdout);
  test_clone_iterator();
  printf("Ok.\n");

  return 0;
}
