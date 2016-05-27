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


static const char *isar_pred_name(const pred *p) {
  static char s[128];
  sprintf(s, "p%lu", p->data);
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

void isar_preds(FILE *fd) {
  assert(K == 3);
  
  fprintf(fd, "theory preds\n");
  fprintf(fd, "imports Main\n");
  fprintf(fd, "begin\n");
  fprintf(fd, "\n");
  fprintf(fd, "datatype dom3 = V0 | V1 | V2\n");
  fprintf(fd, "type_synonym pred2 = \"dom3 \\<Rightarrow> dom3 \\<Rightarrow> bool\"\n");

  pred p = { .arity = 2 };
  for(p.data = 0; p.data < (1 << K*K); ++p.data) {
    fprintf(fd, "\n");
    isar_pred(fd, &p);
  }

  fprintf(fd, "\nend\n");
}

