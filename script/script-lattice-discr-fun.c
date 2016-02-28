/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This scripts searches for functions discriminating every pair "clone —
 * maximal proper subclone".
 *
 * The search applies to pairs where the upper clone does not contain a majority
 * operation. We consider pairs of other types to have been discriminated
 * already.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "lattice.h"
#include "fun-majority.h"
#include "binary/bin-maj-lattice.h"
#include "binary/bin-maj-classes-with-one-subclass-discr-fun.h"
#include "binary/bin-lattice.h"
#include "binary/bin-lattice-discr-fun.h"
#include "z3/z3-search.h"

/** This procedure searches for a discriminating function for every pair "clone
 * — maximal proper subclone".
 *
 * For every pair of clones we want to find a discriminating function of the
 * smallest arity. That's why we first try functions of arity 0, the of arity 1,
 * and so on up to arity 5 (inclusive). For every arity from 0 to 5 the
 * searching procedure has two stages:
 *
 *   1. First, we test functions of the given arity from the previously computed
 *      list of function discriminating the clones of majlattice'2013 and the
 *      functions found by Z3 solver on previous steps.
 *
 *   2. If we've been unsuccessful, we execute Z3 solver to search for a
 *      discriminating function of the given arity.
 *
 * If we haven't found a discriminating function of arity <= 5, we stop the
 * search for this pair of classes.
 */
void script_lattice_discr_fun(const char *lt_name, const char *maj_name, const char *fccpnodes_name, const char *discr_fun_txt_name, const char *log_name, const char *ldf_name) {
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf("\tOk.\n");

  /* A table to store functions discriminating classes with majority operation
   * and functions found by Z3 solver.
   *
   * On every step, we test these functions first. It is only if no suitable
   * function has been found, we invoke Z3 solver. */
  hashtable *ht = hashtable_alloc(4096, fun_hash, (int (*) (const void *, const void *))fun_eq);
  
  /* Read discriminating functions for lattice of clones containing a majority
   * operation and store unique functions to hash table. */
  fun *majdiscr_funs;
  {
    printf("reading \"%s\"...", maj_name); fflush(stdout);
    majlattice *majlt = majlattice_read(maj_name);
    printf("\tOk.\n");

    printf("reading \"%s\"...", fccpnodes_name); fflush(stdout);
    FILE *fccpnodes = fopen(fccpnodes_name, "rb");
    assert(fccpnodes);
    majclass **majclasss;

    size_t majdiscr_funs_sz;
    read_classes_with_one_subclass_discr_fun(fccpnodes, majlt, &majclasss, &majdiscr_funs_sz, &majdiscr_funs);
    fclose(fccpnodes);
    printf("\tOk.\n");

    /* Insert functions to hashtable for further look-up. */
    for(fun *f = majdiscr_funs; f < majdiscr_funs + majdiscr_funs_sz; ++f) {
      hashtable_insert(ht, f, f);
    }
    free(majclasss);
  }

  /** Read functions from a text file and add them to hash table. */
  {
    printf("reading \"%s\"...", discr_fun_txt_name); fflush(stdout);
    fun *funs;
    size_t funs_sz;
    lattice_discr_fun_txt_read(discr_fun_txt_name, &funs, &funs_sz);
    printf("\tOk.\n");

    for(fun *f = funs; f < funs + funs_sz; ++f) {
      hashtable_insert(ht, f, f);
    }
  }

  printf("opening log file \"%s\"...", log_name); fflush(stdout);
  FILE *log = fopen(log_name, "w");
  assert(log);
  printf("\tOk.\n");

  /* The total number of pairs "clone — maximal proper subclone" */
  size_t num_pairs = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++ cp) {
    num_pairs += (*cp)->num_maxsubs;
  }
  printf("\nNumber of pairs \"clone — maximal proper subclone\": %lu\n", num_pairs);

  printf("Number of unique functions loaded: %lu\n", ht->size);
    
  /* Statistics */
  size_t pairs_processed     = 0;   /* Number of pairs having been processed so
                                       far */
  size_t maj_pairs           = 0;   /* Number of pairs where the upper class
                                     * contains a majority operation. */
  size_t pairs_discr_ar[6]   = {0}; /* Pairs_discr_ar[ar] is the number of pairs
                                     * discriminated by a function of arity `ar` */
  size_t pairs_discriminated = 0;   /* Total number of pairs discriminated
                                     * successfully */
  clock_t z3_time            = 0.;  /* Total time spent by Z3 solver for current
                                     * step. */
  clock_t t0                 = clock(); /* time stamp to measure elapsed
                                         * time. */

  printf("\n");
  printf("================================================================================\n");
  printf("progress     | number of new functions found   | undiscriminated                \n");
  printf("       layer | by Z3 solver (for given arity)  | (num of pairs)   elapsed time  \n");
  printf("       index | 0     1     2     3     4     5 |                (z3 time, other)\n");
  printf("================================================================================\n");

  discrfun *discrfuns  = malloc(num_pairs * sizeof(discrfun));
  size_t discrfuns_sz  = 0;     /* A list of discriminating functions. We will
                                 * save these functions to a file at the end of
                                 * computation. */
  fun discr_fun;                /* Discriminating function for the current pair
                                 * of classes. */
  
  /* We process classes from top layer to bottom. */
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);

      /* First, test if the clone contains a majority operation. */
      int maj_class_flag = 0;
      if(clone_contains_majority(&c->clone)) {
        maj_class_flag = 1;
        maj_pairs += c->num_maxsubs;
      }
      
      for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
        class *sub = lattice_get_class(lt, *sub_idx);
        assert(sub->cidx != c->cidx);

        /* If the clone contains a majority operation, we conclude that it is
         * different from all its maximal proper subclones. */
        if(maj_class_flag) {
          ++pairs_discriminated;
        }

        if(!maj_class_flag) {
          /* We want to find a discriminating function of the smallest arity,
           * that's why we iterate over arity from 0 to 5. */
          for(int arity = 0; arity <= 5; ++arity) {
            int flag = 0;
            
            /* [Stage 1] Search for a discriminating function among those that
             * discriminate classes with majority operation and those found by
             * Z3 solve on previous steps. */
            for(hashtable_iterator it = hashtable_iterator_begin(ht); !hashtable_iterator_end(&it); hashtable_iterator_next(&it)) {
              hash_elem *elem = hashtable_iterator_deref(&it);
              fun *f = elem->key;
              if(f->arity == arity) {
                if(fun_preserves_clone(f, &c->clone) && !fun_preserves_clone(f, &sub->clone)) {
                  discr_fun = *f;
                  ++pairs_discriminated;
                  flag = 1;
                  break;
                }
              }
            }
            if(flag) break;

            /* [Stage 2] If no suitable function of the given arity found,
             * invoke Z3 solver. */

            clock_t t1 = clock();            
            /* Note that we use a clone generator (clone base) here to speed up
             * Z3 computation. */
            Z3_lbool rc = z3_find_one_discr_function(&c->generator, &c->clone, &sub->clone, arity, &discr_fun);
            
            z3_time += clock() - t1;

            if(rc == Z3_L_TRUE) {
              /* Save the function so tat we can test it on future steps.
               *
               * We must put to hashtable a pointer to a permanent location
               * (not local variable), that's why we first write the function
               * to `discrfuns`. */
              discrfuns[discrfuns_sz].fun = discr_fun;
              hashtable_insert(ht, &discrfuns[discrfuns_sz].fun, &discrfuns[discrfuns_sz].fun);

              assert(discr_fun.arity <= 5);
              ++pairs_discr_ar[discr_fun.arity];
              ++pairs_discriminated;
              flag = 1;
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
          } /* for(int arity = 0; arity <= 5; ++arity) */
        
          /* Save the discriminating function for a given pair of clones 
           * (or an indicator that the function has not been found). */
          discrfuns[discrfuns_sz].parent = *cidx;
          discrfuns[discrfuns_sz].child  = *sub_idx;
          discrfuns[discrfuns_sz].fun    = discr_fun;
          ++discrfuns_sz;
          
          /* Print verbose log */
          char s1[80], s2[80];
          sprintf(s1, "class %-8u (%u:%u)", c->cidx, c->lidx, c->cpos);
          sprintf(s2, "subclass %-8u (%u:%u)", sub->cidx, sub->lidx, sub->cpos);
          fprintf(log, "%-40s%-40s", s1, s2);
          assert(discr_fun.arity >= -2 && discr_fun.arity <= 5);
          switch(discr_fun.arity) {
          case -1: fprintf(log, "unsat\n"); break;
          case -2: fprintf(log, "undef\n"); break;
          default: {
            char *s = fun_print(&discr_fun);
            fprintf(log, "%s\n", s);
            free(s);
            break;
          }}
          fflush(log);
        } /* if(!maj_class_flag) */
              
        ++pairs_processed;
        
        /* Print statistics */
        if(pairs_processed % (num_pairs / 1000) == 0) {
          double z3_mins_dbl    = z3_time / CLOCKS_PER_SEC;
          unsigned z3_mins      = z3_mins_dbl / 60.;
          unsigned z3_secs      = (z3_mins_dbl - 60.*z3_mins) + 0.5;
          double other_mins_dbl = (clock() - t0 - z3_time) / CLOCKS_PER_SEC;
          unsigned other_mins   = other_mins_dbl / 60.;
          unsigned other_secs   = (other_mins_dbl - 60.*other_mins) + 0.5;
          printf("%4.1f%%   %2u   | %1lu %5lu %5lu %5lu %5lu %5lu |  %3lu          %+6d:%02u %+4d:%02u\n",
                 (100. * pairs_processed / num_pairs),
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
          t0      = clock();
          z3_time = 0;
        }
      }
    }
  }  
  printf("================================================================================\n");

  assert(pairs_processed == num_pairs);
  
  printf("\n");
  printf("Number of pairs where the top class contains a majority operation: %lu\n", maj_pairs);
  printf("Number of other pairs discriminated successfully: %lu\n", discrfuns_sz);
  printf("Number of undiscriminated pairs: %lu\n", pairs_processed - pairs_discriminated);
  
  printf("\n");
  printf("writing \"%s\"...", ldf_name); fflush(stdout);
  lattice_discr_fun_write(ldf_name, discrfuns, discrfuns_sz);
  printf("\tOk.\n");

  free(discrfuns);
  hashtable_free(ht);
  free(majdiscr_funs);
  lattice_free(lt);
  fclose(log);
}

int main() {
  script_lattice_discr_fun("data/lattice.2016",
                           "data/all-maj.2016",
                           "data/maj-classes-with-one-subclass-discr-fun.2016",
                           "data/lattice-discr-fun.txt",
                           "output/lattice-discr-fun.log",
                           "output/lattice-discr-fun.2016");
  printf("Thank you.\n");
}
