/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes some properties of the sublattices of R3(2),
 * containing 0, 1, 2, min, max.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "utils.h"
#include "closure/closure-straightforward.h"
#include "pred-essential.h"
#include "lattice.h"
#include "binary/bin-lattice.h"


void test_predicates() {
  printf("list of all predicates in P3, preserving 0, 1, 2, min, max:\n");

  fun f_0, f_1, f_2;
  fun_scan("fun3_0_0", &f_0);
  fun_scan("fun3_0_1", &f_1);
  fun_scan("fun3_0_2", &f_2);
  fun f_min, f_max;
  fun_scan("fun3_2_210110000", &f_min);
  fun_scan("fun3_2_222211210", &f_max);

  for(uint64_t arity = 0; arity <= 2; ++arity) {
    printf("\n");
    printf("====== predicates of arity %lu ====================================\n", arity);

    printf("\\begin{flalign*}\n");
    uint64_t count = 0;
    for(uint64_t data = 0; data < int_pow2(int_pow(3, arity)); ++data) {
      pred p = { .arity = arity, .data = data };

      if(//pred_is_essential(&p) &&
         fun_preserves_pred(&f_0, &p) &&
         fun_preserves_pred(&f_1, &p) &&
         fun_preserves_pred(&f_2, &p) &&
         fun_preserves_pred(&f_min, &p) &&
         fun_preserves_pred(&f_max, &p)) {
        
        fprintf(stdout, "p_{%lu} \t &= %-40s & \\text{(%s)} \\\\\n",
                p.data,
                pred_print_extensional_ex(&p),
                pred_name(&p));
        ++count;
      }
    }
    
    printf("\\end{flalign*}\n");
    printf("total number of predicates: %lu\n", count);
  }
}

lattice *get_sublattice(const lattice *lt) {
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
        
/*         printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos); */
/*         clone_print_verbosely(stdout, &c->clone); */

        class *sublt_c = class_alloc(&c->clone);
        lattice_add_class(sublt, sublt_c);
        /* NB. Copy class indices from the main lattice. */
        sublt_c->cidx = c->cidx;
        sublt_c->lidx = c->lidx;
        sublt_c->cpos = c->cpos;
      }
    }
  }

  return sublt;
}


/** This function
 *
 * 1. Computes all predicates of arity 2 that preserve 0, 1, 2, min, max.
 *
 * 2. For all 13 predicates that we do not use in the description of
 *    the sublattice lattice, this function find the smallest class
 *    containing this predicate ("smallest" means here that the class
 *    contains the smallest number of predicates).
 */
void test_irrelevant_preds(const lattice *sublt) {
  pred irrpreds[] = {
    { .arity = 2, .data = 281 },
    { .arity = 2, .data = 307 },
    { .arity = 2, .data = 315 },
    { .arity = 2, .data = 401 },
    { .arity = 2, .data = 403 },
    { .arity = 2, .data = 409 },
    { .arity = 2, .data = 411 },
    { .arity = 2, .data = 435 },
    { .arity = 2, .data = 441 },
    { .arity = 2, .data = 473 },
    { .arity = 2, .data = 475 },
    { .arity = 2, .data = 505 },
    { .arity = 2, .data = 507 },
  };

  size_t num_irrpreds = sizeof(irrpreds) / sizeof(struct pred);
  assert(num_irrpreds == 13);

  clone cl_uniq;
  closure_uniq_ess_preds(2 /* max arity */, &cl_uniq);
    
  for(pred *p = irrpreds; p < irrpreds + num_irrpreds; ++p) {
    printf("\n");
    printf("====== predicate p_{%lu} = %s  (%s) ====================================\n",
           p->data,
           pred_print_extensional_ex(p),
           pred_name(p));
    
    if(!pred_is_essential(p)) {
      printf(":: the predicate is not essential\n");
      continue;
    }

    if(!clone_test_pred(&cl_uniq, p)) {
      printf(":: the predicate is not closure-unique\n");

      /* Find an essential predicate `p_uniq` that is a member of
         `cl_uniq` and is closure-equivalent to `p`. */
      int found = 0;
      pred p_uniq;
      
      closure_operator *clop = clop_alloc_straightforward();
      
      clone p_closure;
      closure_one_pred(clop, p, &p_closure);

      for(clone_iterator it = clone_iterator_begin(&cl_uniq); !clone_iterator_end(&cl_uniq, &it); clone_iterator_next(&it)) {
        pred p0 = clone_iterator_deref(&it);
        
        clone p0_closure;
        closure_one_pred(clop, &p0, &p0_closure);

        if(clone_eq(&p_closure, &p0_closure)) {
          p_uniq = p0;
          found = 1;
          break;
        }
      }

      if(!found) {
        printf(":: an equivalent predicates that is a member of the standard list of closure-unique predicates has /not/ been found\n");
        printf(":: most likely, this is a BUG.\n");
        
      } else {
        printf(":: this predicates is closure-equivalent to the following predicate:\n");
        fprintf(stdout, "p_{%lu} = %s \t (%s)\n",
                p_uniq.data,
                pred_print_extensional_ex(&p_uniq),
                pred_name(&p_uniq));
      }

      clop_free(clop);

      continue;
    }

    
    printf(":: the predicate is a member of the following smallest class:\n");
    clone *smallest_cl = NULL;
    
    for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) {
      class *c = *cp;
      if(clone_test_pred(&c->clone, p)) {
        if(smallest_cl == NULL) {
          smallest_cl = &c->clone;
          continue;
        }

        if(clone_subset(&c->clone, smallest_cl)) {
          smallest_cl = &c->clone;
        }
      }
    }
    
    assert(smallest_cl != NULL);

    clone_print_verbosely(stdout, smallest_cl);
  }
}



/* void test_lattice_0_1_2_min_max(const lattice *lt) { */
/*   printf("\ncomputing the list of maximal proper subclasses for every class...\n"); */
/*   lattice_construct_maximal_subclones(sublt); */
/*   for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) { */
/*     class *c = *cp; */
/*     printf("====== class %u (%u:%u) ======\n", c->cidx, c->lidx, c->cpos); */
/*     for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) { */
/*       class *sub = lattice_get_class(lt, *sub_idx); */
/*       printf("%u (%u:%u)\n", sub->cidx, sub->lidx, sub->cpos); */
/*     } */
/*     printf("\n"); */
/*   } */
/*  */
/*   printf("================\n"); */
/*   printf("sublattice size: %lu\n", sublt->num_classes); */
/* } */


int main() {
  test_predicates();

  const char *lt_name = "data/lattice.2016";
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  time_t t0 = time(NULL);
  lattice *lt = lattice_read(lt_name);
  printf("\t%.1f sec. Ok.\n", difftime(time(NULL), t0));

  lattice *sublt = get_sublattice(lt);
  test_irrelevant_preds(sublt);
  
  lattice_free(sublt);
  lattice_free(lt);

/*   printf("\n"); */
/*   printf("computing the sublattice containing the functions 0, 1, 2, min(x,y), max(x,y)...\n"); */
/*   time_t t3 = time(NULL); */
/*   test_lattice_0_1_2_min_max(lt); */
/*   printf("%.2f min. Ok.\n", difftime(time(NULL), t3) / 60.); */

/*   lattice_free(lt); */
}
