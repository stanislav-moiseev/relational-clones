/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "pred-essential.h"
#include "closure/closure-clone-pred.h"
#include "algorithm/alg-closure-clone-pred.h"
#include "binary/bin-closure-clone-pred.h"

struct clop_clone_pred_internals {
  ccplt *ccplt;
  clone cl_uniq;
};
typedef struct clop_clone_pred_internals clop_clone_pred_internals;

void clop_clone_pred_closure_clone_ex(void *_internals, const clone *base, const clone *suppl, clone *closure) {
  clop_clone_pred_internals *internals = (clop_clone_pred_internals *)_internals;
  clone cl;
  clone_union(base, suppl, &cl);
  assert(clone_subset(&cl, &internals->cl_uniq) && "clop_clone_pred is defined for closure-unique essential predicates only");
  
  ccpnode *closure_nd = ccplt_closure_clone(internals->ccplt, &cl);
  clone_copy(&closure_nd->clone, closure);
}

static void clop_clone_pred_internals_free(void *internals) {
  ccplt_free(((clop_clone_pred_internals *)internals)->ccplt);
  free(internals);
}

closure_operator *clop_clone_pred_read(const char *fname) {
  closure_operator *clop = malloc(sizeof(closure_operator));
  
  ccplt *ccplt = ccplt_read(fname);

  clop->ops.closure_clone_ex = clop_clone_pred_closure_clone_ex;
  clop->ops.internals_free   = clop_clone_pred_internals_free;
  clop->internals            = malloc(sizeof(clop_clone_pred_internals));
  ((clop_clone_pred_internals *)clop->internals)->ccplt = ccplt;
  closure_uniq_ess_preds(2, &((clop_clone_pred_internals *)clop->internals)->cl_uniq);

  return clop;
}

closure_operator *clop_clone_pred_alloc(ccplt *ccplt) {
  closure_operator *clop = malloc(sizeof(closure_operator));
 
  clop->ops.closure_clone_ex = clop_clone_pred_closure_clone_ex;
  clop->ops.internals_free   = clop_clone_pred_internals_free;
  clop->internals            = malloc(sizeof(clop_clone_pred_internals));
  ((clop_clone_pred_internals *)clop->internals)->ccplt = ccplt;
  closure_uniq_ess_preds(2, &((clop_clone_pred_internals *)clop->internals)->cl_uniq);

  return clop;
} 

