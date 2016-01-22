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
#include "gen/z3.h"
#include "binary-2013.h"

void get_assert_two_layers(layer *layer1, layer *layer2) {
  for(int i = 0; i < layer1->num_classes; ++i) {
    for(int j = 0; j < layer2->num_classes; ++j) {
      const class *class1 = layer1->classes + i;
      const class *class2 = layer2->classes + j;

      /* if one set is a subset of the other set */
      if(clone_subset(&class1->clone, &class2->clone)) {
        char *out_name;
        assert(asprintf(&out_name, "output/disrc-fun-two-layers/z3/%d-%d.z3", i, j) >= 0);
        FILE *out = fopen(out_name, "w");
        assert(out != NULL);
        
        gen_assert_discr_fun_two_classes(out, class1, class2, 3);

        free(out_name);
        fclose(out);
      }
    }
  }
}

void test_gen_assert_disrc_fun_two_layers(int layer1_id, int layer2_id) {
  char *fname[2];
  FILE *fd[2];
  layer layer[2];
  for(int i = 0; i < 2; ++i) {
    if(i == 0) asprintf(&fname[i], "data/all_maj_cpp/%d.bin", layer1_id);
    else asprintf(&fname[i], "data/all_maj_cpp/%d.bin", layer2_id);
    
    fd[i] = fopen(fname[i], "rb");
    assert(fd[i] != NULL);
    
    layer_aread_classes_2013(fd[i], &layer[i]);
    
    free(fname[i]);
    fclose(fd[i]);
  }

  get_assert_two_layers(&layer[0], &layer[1]);
  
  layer_free(&layer[0]);
  layer_free(&layer[1]);
}

int main() {
  printf("test-gen-assert-disrc-fun-two-layers: "); fflush(stdout);
  test_gen_assert_disrc_fun_two_layers(50, 51);
  printf("Ok.\n");
}

