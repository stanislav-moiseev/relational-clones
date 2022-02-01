/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "lattice.h"
#include "binary/bin-lattice.h"
#include "hashtable.h"

void compute_statistics(const lattice *lt) {
  /** Print average number of precomplete clones for a layer. */
  printf("Number of precomplete clones for a given layer:\n");
  printf("\n");
  
  printf("---------------------------------------------\n");
  printf("layer\t\t number of maximal subclasses\n");
  printf("index\t\t for  classes  of this  layer\n");
  printf("\n");
  printf("     \t\t total           average\n");
  printf("---------------------------------------------\n");
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    size_t num_maxsubs = 0;
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);
      num_maxsubs += c->num_maxsubs;
    }
    printf("%2u\t\t %-8lu\t %.2f\n", lidx, num_maxsubs, (double)num_maxsubs / lr->num_classes);
  }

  /** Print the number of classes that has a given number of precomplete classes. */
  printf("\n");
  printf("The number of classes that has a given number of precomplete classes:\n");
  size_t max_num_maxsubs = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(c->num_maxsubs > max_num_maxsubs) max_num_maxsubs = c->num_maxsubs;
  }
  assert(max_num_maxsubs < 1024);
  size_t nums[max_num_maxsubs + 1]; /* nums[k] is the number of classes that
                                     * has exactly `k` precomplete classes. */
  memset(nums, 0, (max_num_maxsubs + 1) * sizeof(size_t));
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    ++nums[c->num_maxsubs];
  }
  for(size_t k = 0; k <= max_num_maxsubs; ++k) {
    printf("%2lu\t %lu\n", k, nums[k]);
  }
}



void test_submaximal(const lattice *lt) {
  size_t num_maxsubs = 0;
  layer *lr = lattice_get_layer(lt, 1);
  for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
    class *c = lattice_get_class(lt, *cidx);
    printf("\n");
    printf("================================================================================\n");
    printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos);
    clone_print_verbosely(stdout, &c->clone);
    printf("\n");
      
    for(class_idx *cidx2 = c->maxsubs; cidx2 < c->maxsubs + c->num_maxsubs; ++cidx2) {
      class *sub = lattice_get_class(lt, *cidx2);
      printf("====== subclass %u (%u:%u) ====================================\n", sub->cidx, sub->lidx, sub->cpos);
      clone_print_verbosely(stdout, &sub->clone);
      printf("\n");
    }
    
    num_maxsubs += c->num_maxsubs;
  }
  
  printf("================\n");
  printf("sublattice size: %lu\n", num_maxsubs);
}

int main() {
  const char *lt_name = "data/lattice.2016";
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf("\tOk.\n");

  compute_statistics(lt);

  test_submaximal(lt);
  
  lattice_free(lt);
}
