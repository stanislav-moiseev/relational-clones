#include <assert.h>
#include <time.h>
#include <stdlib.h>

#include "pred.h"

/** Test that `pred_construct` return a valid predicate.
 */
void test_pred_construct() {
  srand(clock());
  
  uint32_t k = 2;
  while(k < 10) {
    uint32_t arity = 0;
    
    int max_bits;
    pred_max_bits(k, arity, &max_bits);
    while(max_bits <= 64*PRED_DATA_SIZE) {
      for(int j = 0; j < 10; ++j) {
        /* construct a random string representing predicate's extensional */
        char str[max_bits+1];
        for(int i = 0; i < max_bits; ++i) {
          if((float)rand()/RAND_MAX > 0.5) {
            str[i] = '1';
          } else {
            str[i] = '0';
          }
        }
        str[max_bits] = 0x00;

        printf("pred_construct(%d, %d, \"%s\", &pred)\n", k, arity, str);
        pred pred;
        pred_construct(k, arity, str, &pred);
        printf("                      ");
        pred_print_extensional(stdout, &pred); printf("\n");
        assert(pred_consistent(&pred));
      }
      
      ++arity;
      pred_max_bits(k, arity, &max_bits);
      if(max_bits > 64*PRED_DATA_SIZE) break;
    }
    ++k;
  }
}


int main() {
  
  test_pred_construct();
  
  return 0;
}
