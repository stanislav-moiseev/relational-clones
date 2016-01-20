/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "pred.h"
#include "utils.h"
#include "clone.h"
#include "z3/gen.h"


void test_gen_assert_disrc_fun() {
  char filename50[1024];
  sprintf((char*)&filename50, "data/all_maj_cpp/%d.bin", 50);
  FILE *fd50 = fopen(filename50, "rb");
  assert(fd50 != NULL);
  size_t size50;
  clone *clones50;
  assert(clone_aread_layer(fd50, &size50, &clones50));

  char filename51[1024];
  sprintf((char*)&filename51, "data/all_maj_cpp/%d.bin", 51);
  FILE *fd51 = fopen(filename51, "rb");
  assert(fd51 != NULL);
  size_t size51;
  clone *clones51;
  assert(clone_aread_layer(fd51, &size51, &clones51));
  

  for(int i = 0; i < size50; ++i) {
    for(int j = 0; j < size51; ++j) {
      const clone *clone50 = &clones50[i];
      const clone *clone51 = &clones51[j];
      clone clone_d;
      clone_diff(clone51, clone50, &clone_d);

      clone clone_d2;
      clone_diff(clone50, clone51, &clone_d2);
      
      if(clone_cardinality(&clone_d2) == 0) {
        pred diff_preds[600];
        uint64_t card;
        clone_get_predicates(&clone_d, diff_preds, 600, &card);
        assert(card > 0);
        
        const pred *pred = &diff_preds[0];
        if(pred->data == (1<<9)-1) {
          assert(card >= 2);
          pred = &diff_preds[1];
        }
        
        char out_name[100];
        sprintf(out_name, "test/z3/%d-%d.z3", i, j);
        FILE *out = fopen(out_name, "w");
        gen_assert_discr_fun(out, clone50, pred, 2);
        }
    }
  }
}

int main() {
  printf("test_gen_assert_disrc_fun: ");
  test_gen_assert_disrc_fun();
  printf("Ok.\n");
}

