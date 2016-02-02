/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "binary/binary-2016.h"
#include "closure.h"

void test_pred_is_essential() {
  pred p_false, p_true, p_eq0, p_eq1, p_eq2, p_eq, p_neq;
  assert(pred_construct(0, "0", &p_false));
  assert(pred_construct(0, "1", &p_true));
  assert(pred_construct(1, "001", &p_eq0));
  assert(pred_construct(1, "010", &p_eq1));
  assert(pred_construct(1, "100", &p_eq2));
  assert(pred_construct(2, "100010001", &p_eq));
  assert(pred_construct(2, "011101110", &p_neq));

  assert(pred_is_essential(&p_false));
  assert(pred_is_essential(&p_true));
  assert(pred_is_essential(&p_eq));
  assert(pred_is_essential(&p_neq));
  assert(pred_is_essential(&p_eq0));
  assert(pred_is_essential(&p_eq1));
  assert(pred_is_essential(&p_eq2));
  
  pred p_12;
  assert(pred_construct(1, "110", &p_12));
  assert(pred_is_essential(&p_12));
}

void test_clone_closure() {
  pred p_false, p_true, p_eq0, p_eq1, p_eq2, p_eq, p_neq;
  assert(pred_construct(0, "0", &p_false));
  assert(pred_construct(0, "1", &p_true));
  assert(pred_construct(1, "001", &p_eq0));
  assert(pred_construct(1, "010", &p_eq1));
  assert(pred_construct(1, "100", &p_eq2));
  assert(pred_construct(2, "100010001", &p_eq));
  assert(pred_construct(2, "011101110", &p_neq));

  struct clone clone;
  clone_init(&clone);
  clone_insert_pred(&clone, &p_false);
  clone_insert_pred(&clone, &p_true);
  clone_insert_pred(&clone, &p_eq);
  clone_insert_pred(&clone, &p_eq0);
  clone_insert_pred(&clone, &p_eq1);
  clone_insert_pred(&clone, &p_eq2);

  struct clone closure;
  clone_closure(&clone, &closure);
  assert(clone_eq(&clone, &closure));

  clone_insert_pred(&clone, &p_neq);
  clone_closure(&clone, &closure);
  for(clone_iterator it = clone_iterator_begin(&closure); !clone_iterator_end(&closure, &it); clone_iterator_next(&it)) {
    pred pred = clone_iterator_deref(&it);
    assert(pred_is_essential(&pred));
  }
}

int main() {
  printf("test-pred-is-essential:\t"); fflush(stdout);
  test_pred_is_essential();
  printf("Ok.\n");
  
  printf("test-clone-closure:\t"); fflush(stdout);
  test_clone_closure();
  printf("Ok.\n");
}
