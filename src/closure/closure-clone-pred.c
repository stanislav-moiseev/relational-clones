/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure/closure-clone-pred.h"
#include "algorithm/alg-closure-clone-pred.h"
#include "binary/bin-closure-clone-pred.h"

void clop_clone_pred_closure_clone_ex(void *internals, const clone *base, const clone *suppl, clone *closure) {
  const ccplt *ccplt = (const struct ccplt *)internals;
  clone cl;
  clone_union(base, suppl, &cl);
  ccpnode *closure_nd = ccplt_closure_clone(ccplt, &cl);
  clone_copy(&closure_nd->clone, closure);
}

static void clop_clone_pred_internals_free(void *internals) {
  ccplt_free((ccplt *)internals);
}

closure_operator *clop_clone_pred_read(const char *fname) {
  closure_operator *clop = malloc(sizeof(closure_operator));
  
  ccplt *ccplt = ccplt_read(fname);

  clop->internals            = (void *)ccplt;
  clop->ops.closure_clone_ex = clop_clone_pred_closure_clone_ex;
  clop->ops.internals_free   = clop_clone_pred_internals_free;

  return clop;
}

closure_operator *clop_clone_pred_alloc(const ccplt *ccplt) {
  closure_operator *clop = malloc(sizeof(closure_operator));
 
  clop->internals            = (void *)ccplt;
  clop->ops.closure_clone_ex = clop_clone_pred_closure_clone_ex;
  clop->ops.internals_free   = clop_clone_pred_internals_free;

  return clop;
} 

