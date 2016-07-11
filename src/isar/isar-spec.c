/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "globals.h"
#include "utils.h"
#include "isar/isar-spec.h"
#include "closure/closure-straightforward.h"
#include "closure/closure2-straightforward.h"
#include "binary/bin-closure-clone-pred.h"


static const char *isar_pred_name(const pred *p) {
  static char s[128];
  sprintf(s, "P%03lu", p->data);
  return s;
}

static void isar_pred(FILE *fd, const pred *p) {
  assert(K == 3);
  assert(p->arity == 2);
  assert(p->data < (1 << K*K));

  const char *name = isar_pred_name(p);
  
  fprintf(fd, "(* %s = %s",
          name,
          pred_print_extensional_ex(p));
  const char *human_name = pred_name(p);
  if(human_name != NULL) {
    fprintf(fd, "    -- %s", human_name);
  }
  fprintf(fd, " *)\n");

    
  fprintf(fd, "fun %s :: \"pred2\" where\n", name);
  for(int x1 = 0; x1 < 3; ++x1) {
    for(int x0 = 0; x0 < 3; ++x0) {
      uint32_t digits[3] = { x1, x0 };
      uint64_t tuple = get_K_tuple(digits, p->arity);
      
      const char *res;
      if(pred_compute(p, tuple)) {
        res = "True";
      } else {
        res = "False";
      }
       
      if(x1 == 0 && x0 == 0) {
        fprintf(fd, "  \"%s V%u V%u = %s\"\n", name, x1, x0, res);
      } else {
        fprintf(fd, "| \"%s V%u V%u = %s\"\n", name, x1, x0, res);
      }
    }
  }
}

void isar_preds(FILE *fd, const char *theory_name) {
  assert(K == 3);
  
  fprintf(fd, "theory %s\n", theory_name);
  fprintf(fd, "imports common\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");

  pred p = { .arity = 2 };
  for(p.data = 0; p.data < (1 << K*K); ++p.data) {
    isar_pred(fd, &p);
    fprintf(fd, "\n");
  }

  fprintf(fd, "end\n");
}


/******************************************************************************/
static void isar_op1_proof(FILE *fd, const char *op_name, const pred *p, const pred *resp) {
  static char name[128];
  strcpy(name, isar_pred_name(p));
  static char resp_name[128];
  strcpy(resp_name, isar_pred_name(resp));
  
  fprintf(fd, "lemma op_perm_%s: \"%s %s = %s\"\n", name, op_name, name, resp_name);
  fprintf(fd, "proof (simp add: fun_eq_iff; intro allI)\n");
  fprintf(fd, "  show \"\\<And>x1 x2. (%s %s) x1 x2 = %s x1 x2\"\n", op_name, name, resp_name);
  fprintf(fd, "  by (induct_tac x1 rule: dom3.induct;\n");
  fprintf(fd, "      induct_tac x2 rule: dom3.induct;\n");
  fprintf(fd, "      simp add: %s_def)\n", op_name);
  fprintf(fd, "qed\n");
}

static void isar_op2_proof(FILE *fd, const char *op_name, const pred *p1, const pred *p2, const pred *resp) {
  static char name1[128];
  strcpy(name1, isar_pred_name(p1));
  static char name2[128];
  strcpy(name2, isar_pred_name(p2));
  static char resp_name[128];
  strcpy(resp_name, isar_pred_name(resp));
  
  fprintf(fd, "lemma %s_%s_%s: \"%s %s %s = %s\"\n", op_name, name1, name2, op_name, name1, name2, resp_name);
  fprintf(fd, "proof (simp add: fun_eq_iff; intro allI)\n");
  fprintf(fd, "  show \"\\<And>x1 x2. (%s %s %s) x1 x2 = %s x1 x2\"\n", op_name, name1, name2, resp_name);
  fprintf(fd, "  by (induct_tac x1 rule: dom3.induct;\n");
  fprintf(fd, "      induct_tac x2 rule: dom3.induct;\n");
  fprintf(fd, "      simp add: %s_def)\n", op_name);
  fprintf(fd, "qed\n");
}

void isar_pred_ops_perm(FILE *fd, const char *theory_name) {
  assert(K == 3);
  
  fprintf(fd, "theory %s\n", theory_name);
  fprintf(fd, "imports common preds\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");

  pred p = { .arity = 2 };
  for(p.data = 0; p.data < (1 << K*K); ++p.data) {
    pred resp = op_perm2(&p);
    isar_op1_proof(fd, "op_perm", &p, &resp);
    fprintf(fd, "\n");
  }

  fprintf(fd, "end\n");
}


void isar_pred_ops_conj(FILE *fd, const char *theory_name) {
  assert(K == 3);
  
  fprintf(fd, "theory %s\n", theory_name);
  fprintf(fd, "imports common preds\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");

  pred p1 = { .arity = 2 };
  pred p2 = { .arity = 2 };
  for(p1.data = 0; p1.data < (1 << K*K); ++p1.data) {
    for(p2.data = 0; p2.data < (1 << K*K); ++p2.data) {
      pred resp = op_conj2(&p1, &p2);
      isar_op2_proof(fd, "op_conj", &p1, &p2, &resp);
      fprintf(fd, "\n");
    }
  }

  fprintf(fd, "end\n");
}

void isar_pred_ops_conj2(FILE *fd, const char *theory_name) {
  assert(K == 3);
  
  fprintf(fd, "theory %s\n", theory_name);
  fprintf(fd, "imports common preds\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");

  const char *op_name = "op_conj";
  
  pred p1 = { .arity = 2 };
  pred p2 = { .arity = 2 };
  for(p1.data = 0; p1.data < (1 << K*K); ++p1.data) {
    for(p2.data = 0; p2.data < (1 << K*K); ++p2.data) {
      pred resp = op_conj2(&p1, &p2);
        
      static char name1[128];
      strcpy(name1, isar_pred_name(&p1));
      static char name2[128];
      strcpy(name2, isar_pred_name(&p2));
      static char resp_name[128];
      strcpy(resp_name, isar_pred_name(&resp));

      const char *pre  = (p1.data == 0 && p2.data == 0  ? "lemma \"" : "       ");
      const char *post = (p1.data == (1 << K*K) - 1 && p2.data == (1 << K*K) - 1  ? "\"" : " \\<and>");
      fprintf(fd, "%s%s %-4s %-4s = %-4s%s\n", pre, op_name, name1, name2, resp_name, post);
    }
  }
    
  fprintf(fd, "by (intro conjI;\n");
  fprintf(fd, "    simp add: fun_eq_iff; intro allI; rename_tac x1 x2;\n");
  fprintf(fd, "    induct_tac x1 rule: dom3.induct;\n");
  fprintf(fd, "    induct_tac x2 rule: dom3.induct;\n");
  fprintf(fd, "    simp add: %s_def)\n", op_name);
  fprintf(fd, "\n");

  fprintf(fd, "end\n");
}


void isar_pred_ops_comp(FILE *fd, const char *theory_name) {
  assert(K == 3);
  
  fprintf(fd, "theory %s\n", theory_name);
  fprintf(fd, "imports common preds\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");

  pred p1 = { .arity = 2 };
  pred p2 = { .arity = 2 };
  fprintf(fd, "\n");
  for(p1.data = 0; p1.data < (1 << K*K); ++p1.data) {
    for(p2.data = 0; p2.data < (1 << K*K); ++p2.data) {
      pred resp = op_comp2(&p1, &p2);
      isar_op2_proof(fd, "op_comp", &p1, &p2, &resp);
      fprintf(fd, "\n");
    }
  }

  fprintf(fd, "end\n");
}



static const char *isar_clone_name(class_idx cidx) {
  static char s[128];
  sprintf(s, "C%07u", cidx);
  return s;
}

void isar_clones(const char *ccplt_fname, FILE *fd, const char *theory_name) {
  assert(K == 3);
  
  fprintf(fd, "theory %s\n", theory_name);
  fprintf(fd, "imports common preds\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");

  printf("reading \"%s\"...", ccplt_fname); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccplt_fname);
  printf("\tOk.\n");

  printf("writing specs for clones...");  fflush(stdout);
  for(ccpnode **ndp = ccplt->nodes; ndp < ccplt->nodes + ccplt->num_nodes; ++ndp) {
    ccpnode  *nd = *ndp;
    clone *cl    = &nd->clone;

    const char *name = isar_clone_name(nd->cidx);
    fprintf(fd, "definition \"%s \\<equiv> {", name);
    int flag = 1;
    for(clone_iterator it = clone_iterator_begin(cl); !clone_iterator_end(cl, &it); clone_iterator_next(&it)) {
      pred p = clone_iterator_deref(&it);
      assert(p.arity == 2);
      if(flag) {
        fprintf(fd, "%s", isar_pred_name(&p));
        flag = 0;
      } else {
        fprintf(fd, ", %s", isar_pred_name(&p));
      }
    }
    fprintf(fd, "}\"\n");
  }
  
  fprintf(fd, "end\n");
  printf("\tOk.\n");
}
