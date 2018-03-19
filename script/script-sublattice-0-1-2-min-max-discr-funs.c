/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "colors.h"
#include "lattice.h"
#include "sublattice-0-1-2-min-max/sublattice33.h"
#include "z3/z3-search.h"

static int fun_cmp(const fun *f1, const fun *f2) {
  assert(f1->arity == f2->arity);
  return memcmp(&f1->data, &f2->data, sizeof(f1->data));
}

static void print_statistics(layer_idx lidx,
                             size_t pairs_discr_ar[6],
                             clock_t t0,
                             clock_t z3_time,
                             size_t num_pairs,
                             size_t pairs_processed,
                             size_t pairs_discriminated) {
  double z3_mins_dbl    = z3_time / CLOCKS_PER_SEC;
  unsigned z3_mins      = z3_mins_dbl / 60.;
  unsigned z3_secs      = (z3_mins_dbl - 60.*z3_mins) + 0.5;
  double other_mins_dbl = (clock() - t0 - z3_time) / CLOCKS_PER_SEC;
  unsigned other_mins   = other_mins_dbl / 60.;
  unsigned other_secs   = (other_mins_dbl - 60.*other_mins) + 0.5;
  double progress       = (pairs_processed == num_pairs) ? (100.) : (100. * pairs_processed / num_pairs);

  printf("%5.0f%%   %2u  | %1lu %5lu %5lu %5lu %5lu %5lu |  %3lu          %+6d:%02u %+3d:%02u\n",
         progress,
         lidx,
         pairs_discr_ar[0],
         pairs_discr_ar[1],
         pairs_discr_ar[2],
         pairs_discr_ar[3],
         pairs_discr_ar[4],
         pairs_discr_ar[5],
         (pairs_processed - pairs_discriminated),
         z3_mins, z3_secs,
         other_mins, other_secs);
}


void script_sublattice33_discr_fun() {
  ccplt *ccplt = get_ccplt33();
  printf("\n");
  
  lattice *lt = lattice_alloc();
  lattice_load_classes_from_ccplt(lt, ccplt);
  lattice_construct_layers_ccplt(lt, ccplt);
  lattice_construct_maximal_subclones(lt);


  size_t num_pairs = 0;

  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++ cp) {
    class *c = *cp;
    num_pairs += c->num_maxsubs;
  }

  printf("\nNumber of pairs \"class — the only maximum proper subclass\": %lu\n", num_pairs);

  fun *discr_funs            = malloc(num_pairs * sizeof(struct fun));     /* We will collect here the discriminating functions we construct. */
  assert(discr_funs);
  size_t num_discr_funs      = 0;

  size_t pairs_processed     = 0;       /* Number of pairs having been processed
                                           so far. */
  size_t pairs_discriminated = 0;       /* Total number of pairs discriminated
                                           successfully. */

  size_t pairs_discr_ar[6]   = {0};     /* Pairs_discr_ar[ar] is the number of
                                         * pairs discriminated by a function of
                                         * arity `ar` */
  clock_t z3_time            = 0.;      /* Total time spent by Z3 solver for
                                           current step. */
  clock_t t0                 = clock(); /* Time stamp to measure elapsed time. */


  printf("\n");
  printf(COLOR_BOLD COLOR_CYAN "[Starting Computation]\n\n" COLOR_RESET);

  printf("================================================================================\n");
  printf("progress     | number of new functions found   | undiscriminated                \n");
  printf("       layer | by Z3 solver (for given arity)  | (num of pairs)   elapsed time  \n");
  printf("       index | 0     1     2     3     4     5 |                (z3 time, other)\n");
  printf("================================================================================\n");

  /* We process classes from the bottom layer to the top. */
  for(layer_idx lidx = lt->num_layers - 1; (int)lidx >= 0; --lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);

      for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
        class *sub = lattice_get_class(lt, *sub_idx);
        assert(sub->cidx != c->cidx);

        /* We want to find a discriminating function of the smallest arity,
         * that's why we iterate over arity from 0 to 5. */
        for(int arity = 0; arity <= 5; ++arity) {

          /* [Stage 1] Search for a discriminating function among
           * those found by Z3 solve on previous steps. */
          int flag = 0;

          for(const fun *f = discr_funs; f < discr_funs + num_discr_funs; ++f) {
            if(f->arity == arity) {
              if(fun_preserves_clone(f, &c->clone) && !fun_preserves_clone(f, &sub->clone)) {
                ++pairs_discriminated;
                flag = 1;
                break;
              }
            }
          }
          if(flag) break;


          /* [Stage 2] If no suitable function of the given arity found,
           * invoke Z3 solver. */
          fun discr_fun;  /* A discriminating function for the current pair of classes. */
        
          clock_t t1 = clock();
          /* Note that we use a clone generator (clone base) here to speed up
           * Z3 computation. */
          Z3_lbool rc = z3_find_one_discr_function(&c->generator, &c->clone, &sub->clone, arity, &discr_fun);

          z3_time += clock() - t1;


          if(rc == Z3_L_TRUE) {
            assert(fun_preserves_clone(&discr_fun, &c->clone) && !fun_preserves_clone(&discr_fun, &sub->clone));
            
            /* Save the function so tat we can test it on future steps. */
            discr_funs[num_discr_funs] = discr_fun;
            ++num_discr_funs;

            assert(discr_fun.arity <= 5);
            ++pairs_discr_ar[discr_fun.arity];
            ++pairs_discriminated;
            break;
          }

          /* If arity == 5 and we haven't found a discriminating function yet,
           * report an error. */
          if(arity == 5) {
            if(rc == Z3_L_FALSE) {
              fun f_unsat = { .arity = -1, .data = { 0 } };
              discr_fun   = f_unsat;
            }
            if(rc == Z3_L_UNDEF) {
              fun f_undef = { .arity = -2, .data = { 0 } };
              discr_fun   = f_undef;
            }
          }
        }

        ++pairs_processed;
      }
    }
    
    /* Print statistics */
    print_statistics(lidx, pairs_discr_ar, t0, z3_time, num_pairs, pairs_processed, pairs_discriminated);
    t0      = clock();
    z3_time = 0;
  }

  printf("================================================================================\n");

  assert(pairs_processed == num_pairs);

  printf("\n");
  printf("Number of other pairs discriminated successfully: %lu\n", pairs_discriminated);
  printf("Number of undiscriminated pairs: %lu\n", pairs_processed - pairs_discriminated);


  printf(COLOR_BOLD COLOR_CYAN "\n\n[Functions used]\n\n" COLOR_RESET);
  
  for(const fun *f = discr_funs; f < discr_funs + num_discr_funs; ++f) {
    assert(f->arity >= 0 && f->arity <= 5);
    char *s = fun_print(f);
    printf("%s = ", s);
    fun_print_verbosely(stdout, f);
    free(s);
  }

  
  printf(COLOR_BOLD COLOR_CYAN "\n\n[Functions Used (LaTeX Format)]\n\n" COLOR_RESET);

  printf("\\begin{tabular}{ | c || ");
  for(size_t k = 0; k < num_discr_funs; ++k) {
    printf("c | ");
  }
  printf("}\n");
  
  printf("  \\hline\n");
  printf("$x$ &");
  for(size_t k = 0; k < num_discr_funs; ++k) {
    printf(" $f_{%lu}(x)$", k+1);
    if(k < num_discr_funs - 1) {
      printf(" &");
    } else {
      printf(" \\\\ \\hline \\hline \n");
    }
  }

  qsort(discr_funs, num_discr_funs, sizeof(struct fun), (int (*)(const void *, const void *))fun_cmp);
  
  for(uint64_t tuple = 0; tuple < 3; ++tuple) {
    printf("%lu   & ", tuple);
    size_t idx = 1;
    for(const fun *f = discr_funs; f < discr_funs + num_discr_funs; ++f) {
      assert(f->arity == 1);
      printf("        %u", fun_compute(f, tuple));
      if(idx < num_discr_funs) {
        printf("  & ");
      } else {
        printf("  \\\\ \\hline\n");
      }
      ++idx;
    }
  }

  printf("\\end{tabular}\n");


  printf(COLOR_BOLD COLOR_CYAN "\n\n[Classes and Functions (LaTeX Format)]\n\n" COLOR_RESET);

  printf("\\begin{tabular}{ | l || ");
  for(size_t k = 0; k < num_discr_funs; ++k) {
    printf("c | ");
  }
  printf("}\n");
  
  printf("  \\hline\n");
  printf("        &");
  for(size_t k = 0; k < num_discr_funs; ++k) {
    printf(" $f_{%lu}$ ", k+1);
    if(k < num_discr_funs - 1) {
      printf(" &");
    } else {
      printf(" \\\\ \\hline \\hline \n");
    }
  }


  for(ccpnode **nodep = ccplt->nodes; nodep < ccplt->nodes + ccplt->num_nodes; ++nodep) {
    ccpnode *node = *nodep;
    
    printf("$C_{%u}$ & ", node->cidx+1);
    size_t idx = 1;
    for(const fun *f = discr_funs; f < discr_funs + num_discr_funs; ++f) {
      assert(f->arity == 1);
      const char *s = fun_preserves_clone(f, &node->clone) ? "+" : " ";
      printf("      %s", s);
      if(idx < num_discr_funs) {
        printf("  & ");
      } else {
        printf("  \\\\ \\hline\n");
      }
      ++idx;
    }
  }

  printf("\\end{tabular}\n");

  
  
  free(discr_funs);
  ccplt_free(ccplt);
  lattice_free(lt);
}


int main() {
  script_sublattice33_discr_fun();

  return 0;
}
