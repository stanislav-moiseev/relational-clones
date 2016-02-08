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

void clone_union_straightforward(const clone *clone1, const clone *clone2, clone *clone) {
  clone->data0 = clone1->data0 | clone2->data0;
  clone->data1 = clone1->data1 | clone2->data1;
  for(int64_t offset = CLONE_DATA2_SIZE-1; offset >= 0; --offset) {
    clone->data2[offset] = clone1->data2[offset] | clone2->data2[offset];
  }
}

void test_clone_union() {
  char str1[pred_print_extensional_size()];
  char str2[pred_print_extensional_size()];

  for(int i = 0; i < 100; ++i) {
    clone cl1, cl2;
    clone_init(&cl1);
    clone_init(&cl2);

    size_t sz[3] = { 1, 3, 64 };
    for(int ar = 0; ar <= 2 ;++ ar) {
      for(int j = 0; j < sz[ar]; ++j) {
        pred p1, p2;
        random_pred_extensional(ar, str1);
        pred_construct(ar, str1, &p1);
        clone_insert_pred(&cl1, &p1);
      
        random_pred_extensional(ar, str2);
        pred_construct(ar, str2, &p2);
        clone_insert_pred(&cl2, &p2);
      }

      clone cl3, cl4;
      clone_union_straightforward(&cl1, &cl2, &cl3);
      clone_union(&cl1, &cl2, &cl4);

      assert(clone_eq(&cl3, &cl4));
    }
  }
}


int main() {
  printf("test-pred-construct:\t"); fflush(stdout);
  test_pred_construct();
  printf("Ok.\n");

  printf("test-fun-scan:\t\t"); fflush(stdout);
  test_fun_scan();
  printf("Ok.\n");

  printf("test_clone_union:\t"); fflush(stdout);
  test_clone_union();
  printf("Ok.\n");
  
  return 0;
}
