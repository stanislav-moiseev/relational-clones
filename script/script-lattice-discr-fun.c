/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "lattice.h"
#include "binary/bin-maj-lattice.h"
#include "binary/bin-maj-classes-with-one-subclass-discr-fun.h"
#include "binary/bin-lattice.h"
#include "binary/bin-lattice-discr-fun.h"
#include "z3/z3-search.h"

/** This procedure searches for a discriminating function for every pair "clone
 * — maximal proper subclone". For every pair of clones the searching procedure
 * has two stages:
 *
 *   1. First, we test functions from the previously computed list of function
 *      discriminating the clones of majlattice'2013.

 *   2. If we've been unsuccessful, we execute Z3 solver to search for a
 *      discriminating function of arity <= 5.
 */
void script_lattice_discr_fun(const char *lt_name, const char *maj_name, const char *fccpnodes_name, const char *ldf_name) {
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf("\tOk.\n");

  /* Read discriminating functions for lattice of clones containing a majority
   * operation. We will try to apply these functions for a new lattice first. */
  fun *majdiscr_funs;
  size_t majdiscr_funs_sz;
  {
    printf("reading \"%s\"...", maj_name); fflush(stdout);
    majlattice *majlt = majlattice_read(maj_name);
    printf("\tOk.\n");

    printf("reading \"%s\"...", fccpnodes_name); fflush(stdout);
    FILE *fccpnodes = fopen(fccpnodes_name, "rb");
    assert(fccpnodes);
    majclass **majclasss;
    read_classes_with_one_subclass_discr_fun(fccpnodes, majlt, &majclasss, &majdiscr_funs_sz, &majdiscr_funs);
    fclose(fccpnodes);
    printf("\tOk.\n");

    free(majclasss);
  }

  /* The total number of pairs "clone — maximal proper subclone" */
  size_t num_pairs = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++ cp) {
    num_pairs += (*cp)->num_maxsubs;
  }
  printf("\nNumber of pairs \"clone — maximal proper subclone\": %lu\n", num_pairs);
    
  /* Statistics */
  size_t pairs_processed = 0;   /* number of pairs having been processed so far */
  size_t num_maj_pairs   = 0;   /* number of pairs having been discriminated by
                                 * a function discriminating classes of
                                 * majlattice'2013 */
  size_t num_z3_pairs    = 0;   /* number of pairs that were not discriminated
                                 * by a function from majlattice'2013 but were
                                 * discriminated by Z3 solver */

  /* A list of discriminating function.
  * We will write the results of our search here. */
  discrfun *dfs = malloc(num_pairs * sizeof(discrfun));
  size_t num_dfs = 0;
  
  printf("\n");
  printf("================================================================================\n");
  printf("progress       discr functions   z3 functions     undiscriminated   elapsed time\n");
  printf("       layer   from majlattice   (num of pairs)   (num of pairs)    (min)       \n");
  printf("       index   (num of pairs)                                                   \n");
  printf("================================================================================\n");

  time_t t0 = time(NULL);
  
  /* We process classes from top layer to bottom. */
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);

      for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
        class *sub = lattice_get_class(lt, *sub_idx);
        assert(sub->cidx != c->cidx);

        dfs[num_dfs].parent = *cidx;
        dfs[num_dfs].child  = *sub_idx;

        /* [Stage 1] We search for a discriminating function among those that
         * discriminate classes with majority operation. */
        int flag = 0;
        fun *f;
        for(f = majdiscr_funs; f < majdiscr_funs + majdiscr_funs_sz; ++f) {
          if(test_discr_function(&c->clone, &sub->clone, f)) {
            flag = 1;
            break;
          }
        }
        if(flag) {
          dfs[num_dfs].fun    = *f;
          ++num_maj_pairs;
        }

        /* [Stage 2] If no function has been found, try to find a discriminating
         * function by invoking Z3 solver. */
        if(!flag) {
          fun f;
          Z3_lbool rc = z3_find_discr_function(&c->clone, &c->clone, &sub->clone, 5, &f);

          if(rc == Z3_L_TRUE) {
            dfs[num_dfs].fun = f;
            ++num_z3_pairs;
          } else {
            /* printf("class %-8u (%u:%u)\t\tsubclass %-8u (%u:%u)\t    ", */
            /*        c->cidx, c->lidx, c->cpos, */
            /*        sub->cidx, sub->lidx, sub->cpos); */
            if(rc == Z3_L_FALSE) {
              /* printf("unsat\n"); */
              fun f_unsat      = { .arity = -1 };
              dfs[num_dfs].fun = f_unsat;
            }
            if(rc == Z3_L_UNDEF) {
              /* printf("unknown\n"); */
              fun f_undef      = { .arity = -2 };
              dfs[num_dfs].fun = f_undef;
            }
          }
        }

        ++pairs_processed;
        ++num_dfs;

        /* print stats */
        if(pairs_processed % (num_pairs / 1000) == 0) {
          printf("%.1f%%\t%2u\t  %8lu\t  %8lu\t  %8lu\t     +%.1f min\n",
                 100. * pairs_processed / num_pairs,
                 lidx,
                 num_maj_pairs,
                 num_z3_pairs,
                 (pairs_processed - num_maj_pairs - num_z3_pairs),
                 difftime(time(NULL), t0) / 60.);
          t0 = time(NULL);
        }
      }
    }
  }
  printf("================================================================================\n");

  assert(num_dfs == num_pairs);
  
  printf("\nwriting \"%s\"...", ldf_name); fflush(stdout);
  lattice_discr_fun_write(ldf_name, dfs, num_pairs);
  printf("\tOk.\n");

  free(dfs);  
  free(majdiscr_funs);
  lattice_free(lt);
}

int main() {
  printf("script-lattice-discr-fun:\n");
  time_t t0 = time(NULL);
  script_lattice_discr_fun("data/lattice.2016",
                           "data/all-maj.2016",
                           "data/maj-classes-with-one-subclass-discr-fun.2016",
                           "output/lattice-discr-fun.2016");
  printf("%.2f min. Ok.\n", difftime(time(NULL), t0) / 60.);
}
