/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This script tests some properties of the sublattice of all classes containing
 * the ternary discriminator
 *
 *      p(x, y, z) = (if x=y then z else x).
 *
 * The classes containing the ternary discriminator were studied by
 * S. S. Marchenkov in 1997 (see [3]) where he proved that
 *
 *   При любом k >= 2 функтор Pol устанавливает взаимно однозначное соответствие
 *   между 2-замкнутыми множествами предикатов из R(k), все двуместные предикаты
 *   которых имеют вид
 *      (x ∈ E) ∧ (π(x) = y),
 *   где E⊆Ek и π — перестановка на Ек, либо представимы в виде конъюнкции
 *   одноместных предикатов, и дискриминаторными классами функций из Рк.
 *
 * In 2003 Marchenkov made a description of (almost) all classes containing a
 * ternary discriminator (see [1]). Marchenkov constructed 144 classes
 * containing the ternary discriminator; however, he missed 6 classes.
 *
 * This script tests that there exactly 150 classes containing the ternary
 * discriminator.
 *
 * Relevant papers:
 *
 * [1] Марченков С. С. Дискриминаторные классы трёхзначной логики //
 *     Математические вопросы кибернетики. Вып. 12. М.: Физматлит, 2003.
 *     С. 15–26.
 *     http://publ.lib.ru/ARCHIVES/M/''Matematicheskie_voprosy_kibernetiki''/_''MVK''.html#012
 *
 * [2] С. С. Марченков. Дискриминаторные позитивно замкнутые классы трёхзначной
 *     логики // Дискретн. анализ и исслед. опер., сер. 1, 14:3 (2007), 53–66.
 *
 * [3] Марченков С. С. Клоновая классификация дуально дискриминаторных алгебр с
 *     конечным носителем // Математич. заметки. — 1997. — Т. 61, No 3. —
 *     С. 359-366.
 *
 * [4] С. С. Марченков, Позитивно замкнутые классы трёхзначной логики, Дискретн.
 *     анализ и исслед. опер., 2014, том 21, номер 1, 67–83.
 *     http://mi.mathnet.ru/da761
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "lattice.h"
#include "binary/bin-lattice.h"
#include "z3/z3-search.h"

size_t sublattice_size(const lattice *lt, const fun *f, const pred *p) {
  size_t size = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(fun_preserves_clone(f, &c->generator)) {
      if(clone_test_pred(&c->clone, p)) {
        ++size;
      }
    }
  }
  return size;
}

size_t sublattice_size_ex(const lattice *lt, const fun *f, const pred *p, const pred not[], size_t not_size) {
  size_t size = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(fun_preserves_clone(f, &c->generator)) {
      if(clone_test_pred(&c->clone, p)) {
        int flag = 0;
        for(const pred *notp = not; notp < not + not_size; ++notp) {
          if(clone_test_pred(&c->clone, notp)) {
            flag = 1;
            break;
          }
        }
        if(flag) continue;
        
        ++size;
      }
    }
  }
  return size;
}

void print_sublattice(const lattice *lt, const fun *f, const pred *p, int verbosity) {
  lattice *sublt = lattice_alloc();

  size_t size = 0;
  for(class **cp = lt->classes; cp < lt->classes + lt->num_classes; ++cp) {
    class *c = *cp;
    if(fun_preserves_clone(f, &c->generator)) {
      if(clone_test_pred(&c->clone, p)) {
        printf("====== class %u (%u:%u) ====================================\n", c->cidx, c->lidx, c->cpos);
        if(verbosity == 1) clone_print_verbosely(stdout, &c->clone);

        class *sublt_c = class_alloc(&c->clone, &c->generator);
        lattice_add_class(sublt, sublt_c);
        /* NB. Copy class indices from the main lattice. */
        sublt_c->cidx = c->cidx;
        sublt_c->lidx = c->lidx;
        sublt_c->cpos = c->cpos;

        ++size;
      }
    }
  }

  if(verbosity == 2) {
    printf("\ncomputing the list of maximal proper subclasses for every class...\n");
    lattice_construct_maximal_subclones(sublt);
    for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) {
      class *c = *cp;
      printf("====== class %u (%u:%u) ======\n", c->cidx, c->lidx, c->cpos);
      for(class_idx *sub_idx = c->maxsubs; sub_idx < c->maxsubs + c->num_maxsubs; ++sub_idx) {
        class *sub = lattice_get_class(lt, *sub_idx);
        printf("%u (%u:%u)\n", sub->cidx, sub->lidx, sub->cpos);
        clone diff;
        clone_diff(&sub->clone, &c->clone, &diff);
        clone_print_verbosely(stdout, &diff);
      }
      printf("\n");
    }
  }
  
  printf("================\n");
  printf("sublattice size: %lu\n", size);

  lattice_free(sublt);
}

void script(const char *lt_name) {
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf(" Ok.\n");

  fun f_discr; /* ternary discriminator */
  fun_init(&f_discr, 3);
  for(int x = 0; x < 3; ++x)
    for(int y = 0; y < 3; ++y)
      for(int z = 0; z < 3; ++z) {
        uint32_t digits[3]= { x, y, z };
        uint64_t tuple = get_K_tuple(digits, 3);
        uint64_t val;
        if(x == y) {
          val = z;
        } else {
          val = x;
        }
        fun_set_val(&f_discr, tuple, val);
      }
  pred p_false = pred_scan_ex(0, "{}");
  print_sublattice(lt, &f_discr, &p_false, 0);  

  pred p_sigma   = pred_scan_ex(2, "{01, 12, 20}");
  pred p_sigma_0 = pred_scan_ex(2, "{00, 12, 21}");
  pred p_sigma_1 = pred_scan_ex(2, "{02, 11, 20}");
  pred p_sigma_2 = pred_scan_ex(2, "{01, 10, 22}");

  printf(" 6 =?= %lu\n", sublattice_size(lt, &f_discr, &p_sigma));
  
  pred not_sigma[] = { p_sigma };
  printf("10 =?= %lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_0, not_sigma, 1));
  //printf("%lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_1, not_sigma, 1));
  //printf("%lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_2, not_sigma, 1));

  pred p_sigma_01    = pred_scan_ex(2, "{01, 12}");
  pred p_sigma_02    = pred_scan_ex(2, "{10, 02}");
  pred p_sigma_12    = pred_scan_ex(2, "{12, 20}");
  pred not2[] = { p_sigma,
                  p_sigma_0, p_sigma_1, p_sigma_2 };
  printf(" 9 =?= %lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_01, not2, 4));
  //printf("%lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_02, not2, 4));
  //printf("%lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_12, not2, 4));

  pred p_sigma_01_0     = pred_scan_ex(2, "{00, 12}");
  pred p_sigma_02_0     = pred_scan_ex(2, "{00, 21}");
  pred p_sigma_12_0     = pred_scan_ex(2, "{12, 21}");
  pred not3[] = { p_sigma,
                  p_sigma_0, p_sigma_1, p_sigma_2,
                  p_sigma_01, p_sigma_02, p_sigma_12 };
  printf(" 4 =?= %lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_01_0, not3, 7));

  pred p_sigma_01_1     = pred_scan_ex(2, "{02, 11}");
  pred p_sigma_02_1     = pred_scan_ex(2, "{02, 20}");
  pred p_sigma_12_1     = pred_scan_ex(2, "{11, 02}");

  pred p_sigma_01_2     = pred_scan_ex(2, "{01, 10}");
  pred p_sigma_02_2     = pred_scan_ex(2, "{01, 22}");
  pred p_sigma_12_2     = pred_scan_ex(2, "{10, 22}");
  pred not4[] = { p_sigma,
                  p_sigma_0, p_sigma_1, p_sigma_2,
                  p_sigma_01, p_sigma_02, p_sigma_12,
                  p_sigma_01_0, p_sigma_01_1, p_sigma_02_2};
  printf("12 =?= %lu\n", sublattice_size_ex(lt, &f_discr, &p_sigma_12_0, not4, 10));


  pred not5[] = { p_sigma,
                  p_sigma_0,    p_sigma_1,    p_sigma_2,
                  p_sigma_01,   p_sigma_02,   p_sigma_12,
                  p_sigma_01_0, p_sigma_02_0, p_sigma_12_0,
                  p_sigma_01_1, p_sigma_02_1, p_sigma_12_1,
                  p_sigma_01_2, p_sigma_02_2, p_sigma_12_2 };
  printf("45 =?= %lu\n", sublattice_size_ex(lt, &f_discr, &p_false, not5, 16));
  
  lattice_free(lt);
}


/*
 * M ====== class 31366 (4:96) ====================================
 * pred3_1_2: 	set {1}                         {1}
 * pred3_1_4: 	set {2}                         {2}
 * pred3_1_6: 	set {1, 2}                      {2, 1}
 * pred3_2_a0: 	?                               {21, 12}
 * 
 * M0 ====== class 31367 (5:188) ====================================
 * pred3_1_1: 	set {0}                         {0}
 *
 * M01 ====== class 31369 (6:329) ====================================
 * pred3_1_1: 	set {0}                         {0}
 * pred3_1_3: 	set {0, 1}                      {1, 0}
 * 
 * M02 ====== class 31371 (6:330) ====================================
 * pred3_1_1: 	set {0}                         {0}
 * pred3_1_5: 	set {0, 2}                      {2, 0}
 *
 * M1 ====== class 31368 (5:189) ====================================
 * pred3_1_3: 	set {0, 1}                      {1, 0}
 * 
 * M2 ====== class 31370 (5:190) ====================================
 * pred3_1_5: 	set {0, 2}                      {2, 0}
 *
 * Marchenkov in [1] has M, M0, M01, M02, but does not has M1, M2.
 */
void falsify_marchenkov(const char *lt_name) {
  printf("reading \"%s\"...", lt_name); fflush(stdout);
  lattice *lt = lattice_read(lt_name);
  printf(" Ok.\n");

  class *m   = lattice_get_class(lt, 31366);
  //class *m0  = lattice_get_class(lt, 31367);
  class *m01 = lattice_get_class(lt, 31369);
  class *m02 = lattice_get_class(lt, 31371);
  class *m1  = lattice_get_class(lt, 31368);
  class *m2  = lattice_get_class(lt, 31370);

  fun f_m_m1;
  fun f_m_m2;
  fun f_m1_m01;
  fun f_m2_m02;
  assert(z3_find_discr_function(&m->generator, &m->clone, &m1->clone, 5, &f_m_m1) == Z3_L_TRUE);
  printf("%s\n", fun_print(&f_m_m1));
  assert(z3_find_discr_function(&m->generator, &m->clone, &m2->clone, 5, &f_m_m2) == Z3_L_TRUE);
  printf("%s\n", fun_print(&f_m_m2));
  assert(z3_find_discr_function(&m1->generator, &m1->clone, &m01->clone, 5, &f_m1_m01) == Z3_L_TRUE);
  printf("%s\n", fun_print(&f_m1_m01));
  assert(z3_find_discr_function(&m2->generator, &m2->clone, &m02->clone, 5, &f_m2_m02) == Z3_L_TRUE);
  printf("%s\n", fun_print(&f_m2_m02));

  lattice_free(lt);
}


int main() {
  script("data/lattice.2016");
  falsify_marchenkov("data/lattice.2016");
  printf("Thank you.\n");
}

