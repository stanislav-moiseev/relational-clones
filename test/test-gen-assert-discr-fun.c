/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "pred.h"
#include "utils.h"
#include "class.h"
#include "z3/gen.h"
#include "binary.h"


void test_gen_assert_disrc_fun() {
  char *filename50;
  assert(asprintf(&filename50, "data/all_maj_cpp/%d.bin", 50) >= 0);
  FILE *fd50 = fopen(filename50, "rb");
  assert(fd50 != NULL);
  size_t size50;
  class *layer50;
  assert(class_aread_layer(fd50, &layer50, &size50));
  free(filename50);
  fclose(fd50);
  
  char *filename51;
  assert(asprintf(&filename51, "data/all_maj_cpp/%d.bin", 51) >= 0);
  FILE *fd51 = fopen(filename51, "rb");
  assert(fd51 != NULL);
  size_t size51;
  class *layer51;
  assert(class_aread_layer(fd51, &layer51, &size51));
  free(filename51);
  fclose(fd51);
  

  for(int i = 0; i < size50; ++i) {
    for(int j = 0; j < size51; ++j) {
      const class *class50 = &layer50[i];
      const class *class51 = &layer51[j];
      clone clone_d;
      clone_diff(&class51->clone, &class50->clone, &clone_d);

      clone clone_d2;
      clone_diff(&class50->clone, &class51->clone, &clone_d2);

      /* if one set is a subset of the other set */
      if(clone_is_empty(&clone_d2)) {
        pred *diff_preds;
        uint64_t card;
        clone_get_predicates(&clone_d, &diff_preds, &card);
        assert(card > 0);       /* class are not identical */

        /* select some discriminating predicate */
        const pred *pred = &diff_preds[0];
        
        char *out_name;
        assert(asprintf(&out_name, "test/z3/%d-%d.z3", i, j) >= 0);
        FILE *out = fopen(out_name, "w");
        assert(out != NULL);
        gen_assert_discr_fun(out, class50, pred, 5);

        free(diff_preds);
        free(out_name);
        fclose(out);
      }
    }
  }

  free(layer50);
  free(layer51);
}

int main() {
  printf("test_gen_assert_disrc_fun: ");
  test_gen_assert_disrc_fun();
  printf("Ok.\n");
}

