/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes some properties of the sublattices of R3(2),
 * containing 0, 1, 2, min, max.
 *
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "utils.h"
#include "colors.h"
#include "closure/closure-straightforward.h"
#include "closure/closure2-trace.h"
#include "pred-essential.h"
#include "lattice.h"
#include "sublattice-0-1-2-min-max/sublattice33.h"


/********************************************************************/
/** This function prints the list of all predicates in P3, preserving
 *  0, 1, 2, min, max.
 */
void script_filter_predicates() {
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


void script_print_sublattice33(const char *lt_name) {
  printf("computing the sublattice containing the functions 0, 1, 2, min(x,y), max(x,y)...\n");
  lattice *sublt = get_sublattice33(lt_name);

  for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) {
    class *c = *cp;

    printf("\n" COLOR_BOLD "====== class %u (%u:%u) ====================================" COLOR_RESET "\n", c->cidx, c->lidx, c->cpos);
    clone_print_verbosely(stdout, &c->clone);
  }

/*   printf("\ncomputing the list of maximal proper subclasses for every class...\n"); */
/*   lattice_construct_maximal_subclones(sublt); */
/*   for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) { */
/*     class *c = *cp; */
/*     printf("====== class %u (%u:%u) ======\n", c->cidx, c->lidx, c->cpos); */
/*     for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) { */
/*       class *sub = lattice_get_class(blt, *sub_idx); */
/*       printf("%u (%u:%u)\n", sub->cidx, sub->lidx, sub->cpos); */
/*     } */
/*     printf("\n"); */
/*   } */

  printf("\n================\n");
  printf("sublattice size: %lu\n", sublt->num_classes);

  lattice_free(sublt);
}


/********************************************************************/
/** For all 13 predicates that we do not use in the description of the
 * sublattice lattice, this function find the smallest class of our
 * lattice containing this predicate ("smallest" means here that the
 * class contains the smallest number of predicates).
 */
void script_irrelevant_predicates(const char *lt_name) {
  lattice *sublt = get_sublattice33(lt_name);

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

  lattice_free(sublt);
}


/********************************************************************/
static inline const pred *PRED(uint64_t data) {
  static pred p;
  p.arity = 2;
  p.data  = data;
  return &p;
}


static void construct_formulas(const struct clone *clone, const pred *p) {
  closure_trace_t *trace = closure2_clone_traced(clone, NULL);
  trace_entry_t *entry;
  for(entry = trace->entries; entry < trace->entries + trace->num_entries; ++entry) {
    if(pred_eq(&entry->pred, p)) {
      /* Test correctness of `closure2_trace()`. */
      pred p_ = term_eval(&entry->term);
      assert(pred_eq(p, &p_) && "The term does not define the predicate that it is expected to define. "
                                "Most likely, this is a bug in the closure2_trace() function.");

      formula_t *phi = term_to_formula(&entry->term);
      char *phi_str = formula_print_latex(phi, sublattice33_pred_naming_fn_latex, var_naming_fn_latex);
      char *var1 = strdup(var_naming_fn_latex(1));
      char *var2 = strdup(var_naming_fn_latex(2));
      printf("%s(%s, %s) = %s\n", sublattice33_pred_naming_fn_latex(*p), var1, var2, phi_str);
      free(var1);
      free(var2);

      free(phi);
      free(phi_str);
      break;
    }
  }

  if(entry == trace->entries + trace->num_entries) {
    printf(COLOR_RED "ERROR: predicate p_{%lu} has not been found in the trace." COLOR_RESET "\n", p->data);
  }

  closure_trace_free(trace);
}


void script_formulas_for_pred_307() {
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


void script_formulas_for_pred_315() {
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


void script_formulas_for_pred_435() {
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



/********************************************************************/
void script_print_generating_sets() {
  ccplt *ccplt = get_ccplt33();

  struct clone base;
  clone_init(&base);
  for(const pred *p = basic_preds; p < basic_preds + num_basic_preds; ++p) {
    clone_insert_pred(&base, p);
  }

  printf("\\begin{align*}\n");
  for(ccpnode **nodep = ccplt->nodes; nodep < ccplt->nodes + ccplt->num_nodes; ++nodep) {
    ccpnode *node = *nodep;

    clone clone_;
    clone_intersection(&node->clone, &base, &clone_);

    if(nodep < ccplt->nodes + ccplt->num_nodes - 1) {
      printf("  \\pi(v_{%u}) &= %s; \t\\\\\n", node->cidx+1, clone_naming_fn_latex(&clone_, sublattice33_pred_naming_fn_latex));
    } else {
      printf("  \\pi(v_{%u}) &= %s.\n", node->cidx+1, clone_naming_fn_latex(&clone_, sublattice33_pred_naming_fn_latex));
    }
  }
  printf("\\end{align*}\n");

  ccplt_free(ccplt);
}


/********************************************************************/
void script_build_sublattice_with_latex_formulas() {
  ccplt *ccplt = get_ccplt33();

  /* Collect all predicates in a "base set". */
  struct clone base;
  //clone_copy(top_clone2(), &base);
  clone_init(&base);
  for(const pred *p = basic_preds; p < basic_preds + num_basic_preds; ++p) {
    clone_insert_pred(&base, p);
  }

  for(pred_idx_t pidx = 0; pidx < ccplt->pred_num->uniq_sz; ++pidx) {
    pred p = *idx_pred(ccplt->pred_num, pidx);
    printf("\n\n%%%%====== +%s ==============================================================\n", sublattice33_pred_naming_fn_latex(p));
    printf("\\subsection{Добавление предиката $%s$}\n", sublattice33_pred_naming_fn_latex(p));
    printf("\n");
    printf("\\begin{enumerate} %%[wide, labelindent=0pt, label=\\textbf{\\arabic*}.]");

    for(ccpnode **nodep = ccplt->nodes; nodep < ccplt->nodes + ccplt->num_nodes; ++nodep) {
      ccpnode *parent_node = *nodep;

      if(parent_node->pidx_begin > pidx) continue;

      clone parent;
      clone_intersection(&parent_node->clone, &base, &parent);

      /* child_node = <{p} ∪ parent_node> */
      pred p = *idx_pred(ccplt->pred_num, pidx);

      /* Skip cases when <{p} ∪ parent_node> = <parent_node> */
      if(clone_test_pred(&parent, &p)) continue;


      ccpnode *child_node = ccplt_get_node(ccplt, parent_node->children[pidx - parent_node->pidx_begin]);
      clone child;
      clone_intersection(&child_node->clone, &base, &child);

      /* We use a user-defined LaTeX command that, when used in math
       * terms, allows a line break before the symbol defined in
       * instruction's argument and, in case a line break happens, the
       * symbol is duplicated
       *
       * The instruction should have been defined as follows:
       *
       * \newcommand*{\duponbreak}[1]{#1\nobreak\discretionary{}{\hbox{$\mathsurround=0pt #1$}}{}}
       */
      char *parent_name = strdup(clone_naming_fn_latex(&parent, sublattice33_pred_naming_fn_latex));
      char *child_name  = strdup(clone_naming_fn_latex(&child, sublattice33_pred_naming_fn_latex));
      printf("\n\\item $[C_{%u} \\cup \\{%s\\}]_{p.p.} = [[%s]_{p.p.} \\cup \\{%s\\}]_{p.p.} \\duponbreak= [%s]_{p.p.} \\duponbreak= C_{%u}$",
             parent_node->cidx+1, sublattice33_pred_naming_fn_latex(p),
             parent_name, sublattice33_pred_naming_fn_latex(p),
             child_name, child_node->cidx+1);
      free(parent_name);
      free(child_name);

      clone diff;
      clone_diff(&child, &parent, &diff);
      size_t diff_cardinality = clone_cardinality(&diff);

      if(diff_cardinality <= 1) {
        printf(".\n");

      } else {
        /* If the difference contains more than the predicate `p`,
         * then we will need to construct some proofs.
         * Thus, we print the child fully. */
        printf(", так как\n");

        /* For every predicate `q \in (child_node \ parent_node)`, construct a
         * term that builds `q` from `{p} ∪ parent_node`. */
        clone generator;
        clone_copy(&parent, &generator);
        clone_insert_pred(&generator, &p);

        closure_trace_t *trace = closure2_clone_traced(&generator, NULL);

        printf("  \\begin{flalign*}\n");

        unsigned num_facts = 0;
        for(clone_iterator it = clone_iterator_begin(&diff); !clone_iterator_end(&diff, &it); clone_iterator_next(&it)) {
          pred q = clone_iterator_deref(&it);
          if(pred_eq(&q, &p)) continue;

          trace_entry_t *entry;
          for(entry = trace->entries; entry < trace->entries + trace->num_entries; ++entry) {
            if(pred_eq(&entry->pred, &q)) {
              /* Test correctness of `closure2_trace()`. */
              pred q_ = term_eval(&entry->term);
              assert(pred_eq(&q, &q_) && "The term does not define the predicate that it is expected to define. "
                                         "Most likely, this is a bug in the closure2_trace() function.");

              ++num_facts;

              formula_t *phi = term_to_formula(&entry->term);

              /* Test correctness of `term_to_formula`. */
              pred q__ = formula_eval(phi);
              if(!pred_eq(&q_, &q__)) {
                fprintf(stderr, COLOR_RED);
                fprintf(stderr, "ERROR: The formula defines a predicate different from the predicated defined by the term.\n");
                fprintf(stderr, "       Most likely, this is a bug in the term_to_formula() function.\n");
                fprintf(stderr, COLOR_RED "Term:   " COLOR_YELLOW "  %s\n", term_print(&entry->term, sublattice33_pred_naming_fn_latex));
                fprintf(stderr, "\t\t==> %s\n", pred_print_extensional_ex(&q_));
                fprintf(stderr, COLOR_RED "Formula:" COLOR_YELLOW "  %s\n", formula_print_latex(phi, sublattice33_pred_naming_fn_latex, var_naming_fn_latex));
                fprintf(stderr, "\t\t==> %s\n", pred_print_extensional_ex(&q__));
                fprintf(stderr, COLOR_RESET);
                assert(pred_eq(&q_, &q__));
              }

              char *phi_str  = formula_print_latex(phi, sublattice33_pred_naming_fn_latex, var_naming_fn_latex);
              char *var1     = strdup(var_naming_fn_latex(1));
              char *var2     = strdup(var_naming_fn_latex(2));
              static const char *indent_str = "\\hspace{1cm}";
              if(num_facts < diff_cardinality - 1) {
                printf("  %s %s(%s,%s) &= %s; & \t\\\\\n", indent_str, sublattice33_pred_naming_fn_latex(q), var1, var2, phi_str);
              } else {
                printf("  %s %s(%s,%s) &= %s. &\n", indent_str, sublattice33_pred_naming_fn_latex(q), var1, var2, phi_str);
              }
              free(var1);
              free(var2);
              free(phi_str);
              free(phi);
              break;
            }
          }

          if(entry == trace->entries + trace->num_entries) {
            fprintf(stderr, COLOR_RED "ERROR: predicate %s has not been found in the trace." COLOR_RESET "\n", sublattice33_pred_naming_fn_latex(q));
          }
        }

        printf("  \\end{flalign*}\n");
      }
    }

    printf("\\end{enumerate}\n");

    printf("Таким образом,\n");
    printf("$ Classes(%u) = \\{", pidx+1);

    /* Count the number of classes that contain the predicate `p`
     * (i.e. the classes constructed at the previous steps + the
     * classes constructed on this step). */
    unsigned num_classes = 0;
    for(ccpnode **nodep = ccplt->nodes; nodep < ccplt->nodes + ccplt->num_nodes; ++nodep) {
      ccpnode *node = *nodep;
      if(node->pidx_begin <= pidx + 1) {
        ++num_classes;
      }
    }
    assert(num_classes >= 1);

    /** Because we print the list of classes in the form "C_1, C_2, ..., C_n",
     * we need to check that the list is really continuous
     * (to justify the usage of ellipsis) */
    for(ccpnode **nodep = ccplt->nodes; nodep < ccplt->nodes + ccplt->num_nodes; ++nodep) {
      ccpnode *node = *nodep;
      if(node->pidx_begin <= pidx + 1) {
        assert(node->cidx < num_classes);
      }
    }

    switch(num_classes) {
    case 1: printf("C_1"); break;
    case 2: printf("C_1, C_2"); break;
    case 3: printf("C_1, C_2, C_3"); break;
    default: printf("C_1, C_2, \\ldots, C_{%u}", num_classes); break;
    }
    printf("\\}. $\n");
  }

  ccplt_free(ccplt);
}

#include "binary/bin-lattice.h"


void script_print_sublattice33_dot() {
  ccplt *ccplt = get_ccplt33();
  lattice *lt = lattice_alloc();
  lattice_load_classes_from_ccplt(lt, ccplt);
  lattice_construct_layers_ccplt(lt, ccplt);
  lattice_construct_maximal_subclones(lt);



  printf("graph lattice33 {\n");
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    printf("  C%u [shape=point, label=\"\"]\n", c->cidx+1);
  }
  printf("\n");
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
      class *sub = lattice_get_class(lt, *sub_idx);

      printf("  C%u -- C%u;\n", c->cidx+1, sub->cidx+1);
    }
  }

  printf("}\n");

  ccplt_free(ccplt);
  lattice_free(lt);
}


int main() {
  //  script_print_sublattice33("data/lattice.2016");

  //  script_filter_predicates();

  //  script_irrelevant_predicates("data/lattice.2016");

  //   script_formulas_for_pred_307();
  //   script_formulas_for_pred_315();
  //   script_formulas_for_pred_435();


  //    script_print_generating_sets();

  //script_build_sublattice_with_latex_formulas();

  script_print_sublattice33_dot();

}
