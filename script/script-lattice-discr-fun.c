/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This scripts searches for functions discriminating every pair "clone —
 * maximal proper subclone".
 *
 * The search applies to pairs where the upper clone does not contain a majority
 * operation. We consider pairs of other types to have been discriminated
 * already.
 *
 * The algorithms allows for continuation of the procedure from a previously
 * saved computation state (txt log file).
 *
 * See more comments for `script_lattice_discr_fun`.
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

static void load_maj_discrfuns(const char *maj_name,
                               const char *maj_discrfuns_name,
                               fun **maj_discrfuns,
                               size_t *maj_discrfuns_sz) {
  printf("\n");
  printf("Loading functions discriminating majlattice'2013...\n");

  printf("reading \"%s\"...", maj_name); fflush(stdout);
  majlattice *majlt = majlattice_read(maj_name);
  printf(" Ok.\n");

  printf("reading \"%s\"...", maj_discrfuns_name); fflush(stdout);
  FILE *fd = fopen(maj_discrfuns_name, "rb");
  assert(fd);
  majclass **majclasss;

  read_classes_with_one_subclass_discr_fun(fd, majlt, &majclasss, maj_discrfuns_sz, maj_discrfuns);
  fclose(fd);

  free(majclasss);
  printf(" Ok.\n");
}

static void load_previous(const char *discrfun_prev_name,
                          discrfun **prev_discrfuns,
                          size_t *prev_discrfuns_sz,
                          size_t *prev_discriminated) {
  printf("\n");
  printf("[Loading the result of previous computation]\n");
  printf("[We assume that the results are correct]\n");

  printf("reading \"%s\"...", discrfun_prev_name); fflush(stdout);
  lattice_discr_fun_txt_read(discrfun_prev_name, prev_discrfuns, prev_discrfuns_sz);
  printf(" Ok.\n");
  
  /* Count how many pairs of classes was separated previously. */
  *prev_discriminated = 0;
  for(discrfun *df = *prev_discrfuns; df < *prev_discrfuns + *prev_discrfuns_sz; ++df) {
    if(df->fun.arity >= 0) ++(*prev_discriminated);
  }
}

static void get_basic_lattice_stats(const lattice *lt, size_t *total_pairs, size_t *maj_pairs) {
  printf("Searching for classes with majority operation..."); fflush(stdout);
  *total_pairs = 0;
  *maj_pairs   = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++ cp) {
    class *c = *cp;
    *total_pairs += c->num_maxsubs;
    /* Probably, there is a more effective way to test whether a clone contains
     * a majority operation. */
    if(clone_contains_majority(&c->clone)) {
        *maj_pairs += c->num_maxsubs;
    }
  }
  assert(*maj_pairs == 11419017);
  printf(" Ok.\n");
}

static void print_preliminary_statistics(size_t total_pairs,
                                         size_t maj_pairs,
                                         size_t prev_discriminated,
                                         const hashtable *ht) {
  printf("\n");
  printf("Total number of pairs \"clone — maximal proper subclone\": %lu\n", total_pairs);
  printf("Pairs where the top class contains a majority operation: %lu\n", maj_pairs);
  printf("Pairs separated previously: %lu\n", prev_discriminated);
  printf("Pairs to separate: %lu\n", total_pairs - maj_pairs - prev_discriminated);

  /** Compute statistics about preloaded functions. */
  size_t num_ar[6] = {0}; /* number of functions of the given arity (0..5) */
  for(hashtable_iterator it = hashtable_iterator_begin(ht); !hashtable_iterator_end(&it); hashtable_iterator_next(&it)) {
    hash_elem *elem = hashtable_iterator_deref(&it);
    assert(((fun *)elem->key)->arity <= 5);
    ++num_ar[((fun *)elem->key)->arity];
  }
  
  printf("\n");
  printf("Number of unique functions loaded:\n");
  printf("  arity:                   0     1     2     3     4     5   | total\n");
  printf("  number of functions:");
  for(uint32_t ar = 0; ar <= 5; ++ar) {
    printf("%6lu", num_ar[ar]);
  }
  printf("   |%6lu\n", ht->size);
}

static void print_verbose_log(FILE *log, const class *c, const class *sub, const fun *discr_fun) {
  /* Print verbose log */
  char s1[80], s2[80];
  sprintf(s1, "class %-8u (%u:%u)", c->cidx, c->lidx, c->cpos);
  sprintf(s2, "subclass %-8u (%u:%u)", sub->cidx, sub->lidx, sub->cpos);
  fprintf(log, "%-40s%-40s", s1, s2);
  assert(discr_fun->arity >= -2 && discr_fun->arity <= 5);
  switch(discr_fun->arity) {
  case -1: fprintf(log, "unsat\n"); break;
  case -2: fprintf(log, "undef\n"); break;
  default: {
    char *s = fun_print(discr_fun);
    fprintf(log, "%s\n", s);
    free(s);
    break;
  }}
  fflush(log);
}

static void print_statistics(layer_idx lidx,
                             size_t pairs_discr_ar[6],
                             clock_t t0,
                             clock_t z3_time,
                             double progress,
                             size_t pairs_processed,
                             size_t pairs_discriminated) {
  double z3_mins_dbl    = z3_time / CLOCKS_PER_SEC;
  unsigned z3_mins      = z3_mins_dbl / 60.;
  unsigned z3_secs      = (z3_mins_dbl - 60.*z3_mins) + 0.5;
  double other_mins_dbl = (clock() - t0 - z3_time) / CLOCKS_PER_SEC;
  unsigned other_mins   = other_mins_dbl / 60.;
  unsigned other_secs   = (other_mins_dbl - 60.*other_mins) + 0.5;
  printf("%5.1f%%   %2u  | %1lu %5lu %5lu %5lu %5lu %5lu |  %3lu          %+6d:%02u %+3d:%02u\n",
         (progress < 1.) ? (100. * progress) : 100.,
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
 *
 * lt_name            [in]  name of file with lattice
 * maj_name           [in]  name of file with majlattice'2013
 * maj_discrfuns_name [in]  name of file with discriminating function for
 *                          classes of majlattice'2013
 * discrfun_prev_name [in]  name of txt log file of a previous computation;
 *                          we will continue the computation from this step.
 * log_name           [out] file name where to save txt log
 * ldf_name           [out] binary file name where to save the results to
 */
void script_lattice_discr_fun(const char *lt_name,
                              const char *maj_name,
                              const char *maj_discrfuns_name,
                              const char *discrfun_prev_name,
                              const char *log_name,
                              const char *ldf_name) {
  printf("\n");
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf(" Ok.\n");

  size_t total_pairs;   /* The total number of pairs "clone — maximal proper
                         * subclone" */
  size_t maj_pairs;     /* Number of pairs where the upper class contains a
                         * majority operation. */
  get_basic_lattice_stats(lt, &total_pairs, &maj_pairs);


  /* Read discriminating functions for lattice of clones containing a majority
   * operation and store unique functions to hash table. */
  fun *maj_discrfuns;
  size_t maj_discrfuns_sz;
  load_maj_discrfuns(maj_name, maj_discrfuns_name, &maj_discrfuns, &maj_discrfuns_sz);

  /** Restore the computation from a text file. */
  discrfun *prev_discrfuns;     /* discriminating functions taken from a txt file. */
  size_t prev_discrfuns_sz;
  size_t prev_discriminated;    /* number of pairs discriminated previously
                                 * (from txt file). */
  load_previous(discrfun_prev_name, &prev_discrfuns, &prev_discrfuns_sz, &prev_discriminated);


  /* A table to store functions discriminating classes with majority operation
   * and functions found by Z3 solver.
   *
   * On every step, we test these functions first. It is only if no suitable
   * function has been found, we invoke Z3 solver. */
  hashtable *ht = hashtable_alloc(4096, fun_hash, (int (*) (const void *, const void *))fun_eq);

  /* Insert functions to hash table for further look-up. */
  for(fun *f = maj_discrfuns; f < maj_discrfuns + maj_discrfuns_sz; ++f) {
    hashtable_insert(ht, f, f);
  }
  for(discrfun *df = prev_discrfuns; df < prev_discrfuns + prev_discrfuns_sz; ++df) {
    hashtable_insert(ht, &df->fun, &df->fun);
  }


  print_preliminary_statistics(total_pairs, maj_pairs, prev_discriminated, ht);
  
  printf("\n");
  printf("opening log file \"%s\"...", log_name); fflush(stdout);
  FILE *log = fopen(log_name, "w");
  assert(log);
  printf(" Ok.\n");


  size_t num_pairs           = total_pairs - maj_pairs;
  size_t pairs_processed     = 0;       /* Number of pairs having been processed
                                           so far. */
  size_t pairs_discriminated = 0;       /* Total number of pairs discriminated
                                           successfully. */
  double progress_step       = 0.001;
  double progress            = progress_step; /* When to print statistics next. */

  size_t pairs_discr_ar[6]   = {0};     /* Pairs_discr_ar[ar] is the number of
                                         * pairs discriminated by a function of
                                         * arity `ar` */
  clock_t z3_time            = 0.;      /* Total time spent by Z3 solver for
                                           current step. */
  clock_t t0                 = clock(); /* Time stamp to measure elapsed time. */

  discrfun *discrfuns        = malloc(num_pairs * sizeof(discrfun));
                               /* A list of discriminating functions found by
                                * the program. We will save these functions to a
                                * binary file at the end of computation. */
  size_t discrfuns_sz        = 0;

  printf("\n");
  printf("[Starting computation]\n");

  printf("\n");
  printf("================================================================================\n");
  printf("progress     | number of new functions found   | undiscriminated                \n");
  printf("       layer | by Z3 solver (for given arity)  | (num of pairs)   elapsed time  \n");
  printf("       index | 0     1     2     3     4     5 |                (z3 time, other)\n");
  printf("================================================================================\n");

  /* We process classes from top layer to bottom. */
  for(layer_idx lidx = 0; lidx < lt->num_layers; ++lidx) {
    layer *lr = lattice_get_layer(lt, lidx);
    for(class_idx *cidx = lr->classes; cidx < lr->classes + lr->num_classes; ++cidx) {
      class *c = lattice_get_class(lt, *cidx);

      /* First, test if the clone contains a majority operation.
       * If the clone contains a majority operation, we conclude that it is
       * different from all its maximal proper subclones. */
      if(clone_contains_majority(&c->clone)) continue;
      
      for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
        class *sub = lattice_get_class(lt, *sub_idx);
        assert(sub->cidx != c->cidx);

        fun discr_fun;  /* A discriminating function for the current pair of classes. */

        int flag = 0;   /* If we have already found a discriminating function
                         * for the current pair of classes, or proved that it
                         * does not exist. */

        /** Test whether this pair was separated previously (i.e. if a
         * separating function for this pair was loaded from a txt log file). */
        for(discrfun *df = prev_discrfuns; df < prev_discrfuns + prev_discrfuns_sz; ++df) {
          if(df->parent == c->cidx && df->child == sub->cidx) {
            discr_fun = df->fun;
            flag = 1;
            if(df->fun.arity >= 0) {
              /* if the function is valid, not `f_unsat`, nor `f_undef` */
              ++pairs_discriminated;
            } else {
              /* otherwise, we assume that no separating function for this pair
               * exists, so we do nothing. */
            }
            break;
          }
        }

        /* If the result is unknown from previous computation, compute it. */
        if(!flag) {
          /* We want to find a discriminating function of the smallest arity,
           * that's why we iterate over arity from 0 to 5. */
          for(int arity = 0; arity <= 5; ++arity) {
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
          }
        }

        
        /* Save the discriminating function for a given pair of clones 
         * (or an indicator that the function has not been found). */
        discrfuns[discrfuns_sz].parent = *cidx;
        discrfuns[discrfuns_sz].child  = *sub_idx;
        discrfuns[discrfuns_sz].fun    = discr_fun;
        ++discrfuns_sz;

        ++pairs_processed;
        
        print_verbose_log(log, c, sub, &discr_fun);
        
        /* Print statistics */
        if(pairs_processed == (size_t)(progress * num_pairs) || pairs_processed == num_pairs) {
          print_statistics(lidx, pairs_discr_ar, t0, z3_time, progress, pairs_processed, pairs_discriminated);
          t0      = clock();
          z3_time = 0;
          progress += progress_step;
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
  printf(" Ok.\n");

  free(discrfuns);
  hashtable_free(ht);
  free(maj_discrfuns);
  free(prev_discrfuns);
  lattice_free(lt);
  fclose(log);
}


void verify(const char *lt_name, const char *ldf_name) {
  printf("\n");
  printf("[Verification of the result]\n");
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf(" Ok.\n");
  
  discrfun *discrfuns;
  size_t discrfuns_sz;
  printf("reading \"%s\"...", ldf_name); fflush(stdout);
  lattice_discr_fun_read(ldf_name, &discrfuns, &discrfuns_sz);
  printf(" Ok.\n");

  clock_t t0 = clock();
  size_t no_discrfuns = 0; /* number of pairs with no discriminating function. */
  printf("verification"); fflush(stdout);
  size_t pair_idx = 0;
  for(discrfun *df = discrfuns; df < discrfuns + discrfuns_sz; ++df) {
    class *parent = lattice_get_class(lt, df->parent);
    class *child  = lattice_get_class(lt, df->child);
    if(df->fun.arity >= 0) {
      assert(fun_preserves_clone(&df->fun, &parent->generator) && !fun_preserves_clone(&df->fun, &child->clone));
    } else {
      ++no_discrfuns;
    }

    /* print progress */
    ++pair_idx;
    if(pair_idx % (discrfuns_sz/40) == 0) {
      printf("."); fflush(stdout);
    }
  }
  printf(" %.2lf min. Ok.\n", (double)(clock() - t0) / CLOCKS_PER_SEC / 60.);

  printf("Number of pairs with no discriminating function: %lu\n", no_discrfuns);
  if(no_discrfuns > 0) {
    printf("List of pairs with no discriminating function:\n");
    printf("================================================================\n");
    for(discrfun *df = discrfuns; df < discrfuns + discrfuns_sz; ++df) {
      class *parent = lattice_get_class(lt, df->parent);
      class *child  = lattice_get_class(lt, df->child);
      if(df->fun.arity < 0) {
        print_verbose_log(stdout, parent, child, &df->fun);
      }
    }
    printf("================================================================\n");
  }  
  lattice_free(lt);
}

int main() {
  script_lattice_discr_fun("data/lattice.2016",
                           "data/all-maj.2016",
                           "data/maj-classes-with-one-subclass-discr-fun.2016",
                           "data/lattice-discr-fun.txt",
                           "output/lattice-discr-fun.log",
                           "output/lattice-discr-fun.2016");
  printf("Thank you.\n");

  verify("data/lattice.2016", "output/lattice-discr-fun.2016");
}

