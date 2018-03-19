/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes some sublattices of R3(2):
 *  - The sublattice of clones containing the function x+1.
 *  - The sublattice of clones containing the function 2x+2y.
 *  - The submaximal clones.
 *  - The sublattice of clones containing 0, 1, 2, min, max.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "lattice.h"
#include "binary/bin-lattice.h"

void test_lattice_x_plus_1(const lattice *lt) {
  fun f;
  fun_scan("fun3_1_021", &f);
  
  /* Select clones containing x+1 */
  size_t size = 0;
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);
              
      if(fun_preserves_clone(&f, &c->clone)) {
        printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos);
        clone_print_verbosely(stdout, &c->clone);
        ++size;
      }
    }
  }
  printf("================\n");
  printf("sublattice size: %lu\n", size);
}

void test_lattice_2x_plus_2y(const lattice *lt) {
  fun f;
  fun_scan("fun3_2_201012120", &f);
  
  /* Select clones containing 2x+2y */
  size_t size = 0;
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);
              
      if(fun_preserves_clone(&f, &c->clone)) {
        printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos);
        clone_print_verbosely(stdout, &c->clone);
        ++size;
      }
    }
  }
  printf("================\n");
  printf("sublattice size: %lu\n", size);
}

void test_submaximal(const lattice *lt) {
  size_t size = 0;
  layer *lr = lattice_get_layer(lt, 2);
  for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
    class *c = lattice_get_class(lt, *cidx);
    printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos);
    clone_print_verbosely(stdout, &c->clone);
    ++size;
  }
  printf("================\n");
  printf("sublattice size: %lu\n", size);
}


int main() {
  const char *lt_name = "data/lattice.2016";
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf("\tOk.\n");

  printf("\n");
  printf("computing the sublattice containing the function x+1...\n");
  time_t t0 = time(NULL);
  test_lattice_x_plus_1(lt);
  printf("%.2f min. Ok.\n", difftime(time(NULL), t0) / 60.);

  printf("\n");
  printf("computing the sublattice containing the function 2x+2y...\n");
  time_t t1 = time(NULL);
  test_lattice_2x_plus_2y(lt);
  printf("%.2f min. Ok.\n", difftime(time(NULL), t1) / 60.);

  printf("\n");
  printf("computing the submaximal clones...\n");
  time_t t2 = time(NULL);
  test_submaximal(lt);
  printf("%.2f min. Ok.\n", difftime(time(NULL), t2) / 60.);

  lattice_free(lt);
}
