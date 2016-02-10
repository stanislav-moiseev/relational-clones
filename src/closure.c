/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "closure.h"
#include "closure/closure-straightforward.h"
#include "closure/closure-two-preds.h"

void clop_free(closure_operator *clop) {
  clop->ops.internals_free(clop->internals);
  free(clop);
}

/******************************************************************************/
void clone_insert_dummy_preds(clone *cl) {
  pred p_false, p_true, p_eq;
  pred_construct(0, "0", &p_false);
  pred_construct(0, "1", &p_true);
  pred_construct(2, "100010001", &p_eq);

  clone_insert_pred(cl, &p_false);
  clone_insert_pred(cl, &p_true);
  clone_insert_pred(cl, &p_eq);
}

void closure_dummy_clone(const closure_operator *clop, clone *closure) {
  clone_init(closure);
  
  clone cl;
  clone_init(&cl);
  
  clone_insert_dummy_preds(&cl);

  closure_clone(clop, &cl, closure);
}

void closure_one_pred(const closure_operator *clop, const pred *p, clone *closure) {
  clone_init(closure);

  clone cl;
  clone_init(&cl);
  
  clone_insert_dummy_preds(&cl);
  clone_insert_pred(&cl, p);

  closure_clone(clop, &cl, closure);
}

