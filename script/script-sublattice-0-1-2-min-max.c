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
#include "closure/closure2-trace.h"
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


/** For all 13 predicates that we do not use in the description of the
 * sublattice lattice, this function find the smallest class of our
 * lattice containing this predicate ("smallest" means here that the
 * class contains the smallest number of predicates).
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


static const pred p_false = { .arity = 2,
                              .data  = 0x000 };
static const pred p_true  = { .arity = 2,
                              .data  = 0x1FF };
static const pred p_eq    = { .arity = 2,
                              .data  = 0x111 };

static inline const pred *PRED(uint64_t data) {
  static pred p;
  p.arity = 2;
  p.data  = data;
  return &p;
}

static const char *pred_naming_fn(pred p) {
  assert(p.arity == 2);
  
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  if(p.data == 0) {
    asprintf(&str, "false^{(2)}");
  } else if(p.data == 0x1FF) {
    asprintf(&str, "true^{(2)}");
  } else if(p.data == 0x111) {
    asprintf(&str, "eq^{(2)}");
  } else {
    asprintf(&str, "p_{%lu}", p.data);
  }
  return str;
}


static inline void strappend(char **str1, const char *str2) {
  char *str;
  asprintf(&str, "%s%s", *str1, str2);
  free(*str1);
  *str1 = str;
}

static const char *clone_naming_fn(const struct clone *clone) {
  static char *str = NULL;
  if(str != NULL) {
    free(str);
  }

  if(clone_is_empty(clone)) {
    asprintf(&str, "\\varnothing");
    return str;
  }
  
  asprintf(&str, "\\{");

  unsigned nprinted = 0;

  if(clone_test_pred(clone, &p_false)) {
    strappend(&str, pred_naming_fn(p_false));
    ++nprinted;
  }
  if(clone_test_pred(clone, &p_true)) {
    if(nprinted > 0) {
      strappend(&str, ", ");
    }
    strappend(&str, pred_naming_fn(p_true));
    ++nprinted;
  }
  if(clone_test_pred(clone, &p_eq)) {
    if(nprinted > 0) {
      strappend(&str, ", ");
    }
    strappend(&str, pred_naming_fn(p_eq));
    ++nprinted;
  }

  unsigned card = clone_cardinality(clone);
  
  for(clone_iterator it = clone_iterator_begin(clone); !clone_iterator_end(clone, &it); clone_iterator_next(&it)) {
    pred p = clone_iterator_deref(&it);

    if(pred_eq(&p, &p_false) || pred_eq(&p, &p_true) || pred_eq(&p, &p_eq)) {
      continue;
    }

    if(nprinted > 0) {
      strappend(&str, ", \\, ");
    }

    if(nprinted >= 2 && nprinted <= card - 2) {
      strappend(&str, "\\allowbreak ");
    }

    strappend(&str, pred_naming_fn(p));
        
    ++nprinted;
  }

  strappend(&str, "\\}");

  return str;
}


static void construct_formulas(const struct clone *clone, const pred *p) {
  closure_trace_t *trace = closure2_clone_traced(clone, NULL);
  trace_entry_t *entry;
  for(entry = trace->entries; entry < trace->entries + trace->num_entries; ++entry) {
    if(pred_eq(&entry->pred, p)) {
      /* Test correctness of `closure2_trace()`. */
      pred p_ = formula_eval(&entry->formula);
      assert(pred_eq(p, &p_) && "The formula does not define the predicate that it is expected to define. "
                                "Most likely, this is a bug in the closure2_trace() function.");
      
      char *phi = print_formula_func_form(&entry->formula, pred_naming_fn);
      printf("p_{%lu} = %s\n", p->data, phi);
      free(phi);
      break;
    }
  }

  if(entry == trace->entries + trace->num_entries) {
    printf("ERROR: predicate p_{%lu} has not been found in the trace.\n", p->data);
  }
  
  closure_trace_free(trace);
}


void find_formula_307() {
  printf("\n======================================================================\n");
  struct clone clone;
  
  clone_copy(top_clone2(), &clone);
  clone_insert_pred(&clone, PRED(311));
  clone_insert_pred(&clone, PRED(447));
  construct_formulas(&clone, PRED(307));

  clone_copy(top_clone2(), &clone);
  clone_insert_pred(&clone, PRED(307));
  construct_formulas(&clone, PRED(311));
  construct_formulas(&clone, PRED(447));
}


void find_formula_315() {
  printf("\n======================================================================\n");
  struct clone clone;
  
  clone_copy(top_clone2(), &clone);
  clone_insert_pred(&clone, PRED(319));
  clone_insert_pred(&clone, PRED(447));
  construct_formulas(&clone, PRED(315));

  clone_copy(top_clone2(), &clone);
  clone_insert_pred(&clone, PRED(315));
  construct_formulas(&clone, PRED(319));
  construct_formulas(&clone, PRED(447));
}


void find_formula_435() {
  printf("\n======================================================================\n");

  struct clone clone;
  
  clone_copy(top_clone2(), &clone);
  clone_insert_pred(&clone, PRED(319));
  clone_insert_pred(&clone, PRED(439));
  clone_insert_pred(&clone, PRED(447));
  construct_formulas(&clone, PRED(435));

  clone_copy(top_clone2(), &clone);
  clone_insert_pred(&clone, PRED(435));
  construct_formulas(&clone, PRED(439));
  construct_formulas(&clone, PRED(447));
}


void script_build_sublattice_with_latex_formualas() {
  closure_operator *clop2 = clop2_alloc_straightforward();
  ccplt *ccplt = ccplt_alloc();

  /* define a universe of predicates */
  pred preds[] = {
    /* false, true, eq */
/*     { .arity = 2, .data = 0   }, */
/*     { .arity = 2, .data = 511 }, */
/*     { .arity = 2, .data = 273 }, */
    /* left part */
    { .arity = 2, .data = 283 },
    { .arity = 2, .data = 275 },
    { .arity = 2, .data = 319 },
    /* central part */
    { .arity = 2, .data = 443 },
    { .arity = 2, .data = 311 },
    { .arity = 2, .data = 313 },
    { .arity = 2, .data = 447 },
    /* right part */    
    { .arity = 2, .data = 433 },
    { .arity = 2, .data = 305 },
    { .arity = 2, .data = 439 },
  };
  size_t num_preds = sizeof(preds) / sizeof(preds[0]);

  /* Collect all predicates in a "base set". */
  struct clone base;
  //clone_copy(top_clone2(), &base);
  clone_init(&base);
  for(pred *p = preds; p < preds + num_preds; ++p) {
    clone_insert_pred(&base, p);
  }

  ccplt->pred_num = predicate_numerator_alloc(preds, num_preds);

  /* start from a ccplt containing just one clone */
  ccpnode *top = ccpnode_alloc(ccplt);
  top->clone = *top_clone2();
  ccplt_insert_node(ccplt, top, 0 /*pidx_begin*/);
  
  /* iteratively construct new ccpnodes */
  for(pred_idx_t pidx = 0; pidx < ccplt->pred_num->uniq_sz; ++pidx) {
    ccplt_construct_step(clop2, ccplt, pidx);
  }

  //  printf("Total nodes: %lu\n", ccplt->num_nodes);


  for(pred_idx_t pidx = 0; pidx < ccplt->pred_num->uniq_sz; ++pidx) {
    pred p = *idx_pred(ccplt->pred_num, pidx);
    printf("\n%%%%====== +%s ====================================================\n", pred_naming_fn(p));
    printf("\\subsubsection{Добавление предиката $%s$}\n", pred_naming_fn(p));
    printf("\n");
    printf("\\begin{enumerate}\n");

    
    for(ccpnode **nodep = ccplt->nodes; nodep < ccplt->nodes + ccplt->num_nodes; ++nodep) {
      ccpnode *parent_node = *nodep;

      if(parent_node->pidx_begin > pidx) continue;
      
      clone parent;
      clone_intersection(&parent_node->clone, &base, &parent);

      /* child_node = <{p} ∪ parent_node> */
      pred p = *idx_pred(ccplt->pred_num, pidx);
      if(clone_test_pred(&parent, &p)) continue;
      
      ccpnode *child_node = ccplt_get_node(ccplt, parent_node->children[pidx - parent_node->pidx_begin]);
      clone child;
      clone_intersection(&child_node->clone, &base, &child);

      clone diff;
      clone_diff(&child, &parent, &diff);

      size_t diff_cardinality = clone_cardinality(&diff);
      printf("\\item $[C_{%u} \\cup \\{%s\\}] = [[%s] \\cup \\{%s\\}]",
             parent_node->cidx, pred_naming_fn(p),
             clone_naming_fn(&parent), pred_naming_fn(p));

      /* We use a user-defined LaTeX command that, when used in math
       * formulas, allows a line break before the symbol defined in
       * instruction's argument and, in case a line break happens, the
       * symbol is dubbed.
       *
       * The instruction should be defined as follows:
       *
       * \newcommand*{\dubonbreak}[1]{#1\nobreak\discretionary{}{\hbox{$\mathsurround=0pt #1$}}{}}
       */
      printf(" \\dubonbreak= [%s] = C_{%u}$", clone_naming_fn(&child), child_node->cidx);

      if(diff_cardinality == 1) {
        printf(".\n");
        
      } else {
        /* If the difference contains more than the predicate `p`,
         * then we will need to construct some proofs.
         * Thus, we print the child fully. */
        printf(", так как\n");
        
        /* For every predicate `q \in (child_node \ parent_node)`, construct a
         * formula that builds `q` from `{p} ∪ parent_node`. */
        clone generator;
        clone_copy(&parent, &generator);
        clone_insert_pred(&generator, &p);

        closure_trace_t *trace = closure2_clone_traced(&generator, NULL);
        
        printf("  \\begin{align*}\n");

        unsigned num_facts = 0;
        for(clone_iterator it = clone_iterator_begin(&diff); !clone_iterator_end(&diff, &it); clone_iterator_next(&it)) {
          pred q = clone_iterator_deref(&it);
          if(pred_eq(&q, &p)) continue;

          trace_entry_t *entry;
          for(entry = trace->entries; entry < trace->entries + trace->num_entries; ++entry) {
            if(pred_eq(&entry->pred, &q)) {
              /* Test correctness of `closure2_trace()`. */
              pred q_ = formula_eval(&entry->formula);
              assert(pred_eq(&q, &q_) && "The formula does not define the predicate that it is expected to define. "
                                         "Most likely, this is a bug in the closure2_trace() function.");
      
              char *phi = print_formula_func_form(&entry->formula, pred_naming_fn);

              ++num_facts;
              if(num_facts < diff_cardinality - 1) {
                printf("  %s &= %s;    \\\\\n", pred_naming_fn(q), phi);
              } else {
                printf("  %s &= %s.\n", pred_naming_fn(q), phi);
              }
              
              free(phi);
              break;
            }
          }
          
          if(entry == trace->entries + trace->num_entries) {
            fprintf(stderr, "ERROR: predicate %s has not been found in the trace.\n", pred_naming_fn(q));
          }
        }
        
        printf("  \\end{align*}\n");
      }
    }
    printf("\\end{enumerate}\n");
  }
  
  //ccplt_free(ccplt);
  clop_free(clop2);
}


int main() {
/*   test_predicates(); */


/*   const char *lt_name = "data/lattice.2016"; */
/*   printf("reading \"%s\"...", lt_name); fflush(stdout); */
/*   time_t t0 = time(NULL); */
/*   lattice *lt = lattice_read(lt_name); */
/*   printf("\t%.1f sec. Ok.\n", difftime(time(NULL), t0)); */
/*  */
/*   lattice *sublt = get_sublattice(lt); */
/*   test_irrelevant_preds(sublt); */
/*  */
/*   lattice_free(sublt); */
/*   lattice_free(lt); */


/*   find_formula_307(); */
/*   find_formula_315(); */
/*   find_formula_435(); */

  script_build_sublattice_with_latex_formualas();
}
