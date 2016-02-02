/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/common.h"
#include "algorithms/alg-closure.h"

void construct_closure_two_preds(const char *fout_name) {
  pred p_eq;
  assert(pred_construct(2, "100010001", &p_eq));
  
  clone closure;
  clone_closure_two_preds(&p_eq, &p_eq, &closure);
}

int main() {
  printf("construct-closure-two-preds: "); fflush(stdout);
  construct_closure_two_preds("output/closure-two-preds.2016");
  printf("Ok.\n");
}
