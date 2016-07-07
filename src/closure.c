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


/******************************************************************************/
const clone *top_clone() {
  static int flag = 0;
  static clone cl;
  if(!flag) {
    flag = 1;
    clone_init(&cl);
    clone_insert_pred(&cl, pred_get("false(0)"));
    clone_insert_pred(&cl, pred_get("true(0)"));
    clone_insert_pred(&cl, pred_get("equality"));
  }
  return &cl;
}

void closure_clone(const closure_operator *clop, const clone *clone, struct clone *closure) {
  clone_init(closure);
  
  struct clone empty;
  clone_init(&empty);
  clop->ops.closure_clone_ex(clop->internals, &empty, clone, closure);
}
