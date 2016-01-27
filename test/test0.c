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

int main() {
  printf("test_pred_construct: "); fflush(stdout);
  test_pred_construct();
  printf("Ok.\n");

  printf("test_fun_scan: "); fflush(stdout);
  test_fun_scan();
  printf("Ok.\n");
  
  return 0;
}
