/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef SCRIPT_VERIFY_MAJ
#define SCRIPT_VERIFY_MAJ

#include "closure/closure-straightforward.h"

/** The function prepares the clone for comparison with clones from maj'2013
 * lattice. */
void clone_prepare_for_maj2013(const clone *cl, clone *cl2013) {
  closure_operator *clop = clop_alloc_straightforward();
  
  /* In current implementation we store only closure-unique predicates,
   * so we have to expand the clone to all essential predicates */
  clone cl2;
  clone_copy(cl, &cl2);
  clone_union(top_clone(), &cl2, &cl2);
  clone full_closure;
  closure_clone(clop, &cl2, &full_closure);
    
  /* In the previous lattice (maj'2013) we did not store predicates false(0)
   * and true(0), that's why we remove them. */
  clone_copy(&full_closure, cl2013);
  pred p_false, p_true;
  pred_construct(0, "0", &p_false);
  pred_construct(0, "1", &p_true);
  clone_remove_pred(cl2013, &p_false);
  clone_remove_pred(cl2013, &p_true);

  clop_free(clop);
}

#endif
