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

void test_lattice_0_1_2_min_max(const lattice *lt) {
  fun f_0, f_1, f_2;
  fun_scan("fun3_0_0", &f_0);
  fun_scan("fun3_0_1", &f_1);
  fun_scan("fun3_0_2", &f_2);
  fun f_min, f_max;
  fun_scan("fun3_2_210110000", &f_min);
  fun_scan("fun3_2_222211210", &f_max);
  
  /* Select clones containing 0, 1, 2, min, max */
  lattice *sublt = lattice_alloc();
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);
              
      if(fun_preserves_clone(&f_0, &c->clone) &&
         fun_preserves_clone(&f_1, &c->clone) &&
         fun_preserves_clone(&f_2, &c->clone) &&
         fun_preserves_clone(&f_min, &c->clone) &&
         fun_preserves_clone(&f_max, &c->clone)) {
        printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos);
        clone_print_verbosely(stdout, &c->clone);

        class *sublt_c = class_alloc(&c->clone);
        lattice_add_class(sublt, sublt_c);
        /* NB. Copy class indices from the main lattice. */
        sublt_c->cidx = c->cidx;
        sublt_c->lidx = c->lidx;
        sublt_c->cpos = c->cpos;
      }
    }
  }

  printf("\ncomputing the list of maximal proper subclasses for every class...\n");
  lattice_construct_maximal_subclones(sublt);
  for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) {
    class *c = *cp;
    printf("====== class %u (%u:%u) ======\n", c->cidx, c->lidx, c->cpos);
    for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
      class *sub = lattice_get_class(lt, *sub_idx);
      printf("%u (%u:%u)\n", sub->cidx, sub->lidx, sub->cpos);
    }
    printf("\n");
  }

  printf("================\n");
  printf("sublattice size: %lu\n", sublt->num_classes);

  lattice_free(sublt);
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

  printf("\n");
  printf("computing the sublattice containing the functions 0, 1, 2, min(x,y), max(x,y)...\n");
  time_t t3 = time(NULL);
  test_lattice_0_1_2_min_max(lt);
  printf("%.2f min. Ok.\n", difftime(time(NULL), t3) / 60.);

  lattice_free(lt);
}
