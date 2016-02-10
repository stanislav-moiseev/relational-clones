/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "fun-majority.h"

void min_majorities(fun **majs, size_t *size) {
  assert(K == 3);
  
  *size = 7;
  *majs = malloc(*size * sizeof(fun));
  assert(majs);
  
  /* лфМаж1 a   = лфМаж (\ [x,y,z] -> a) */
  const char maj1_0[]  = "fun3_3_222210200210111010200010000";
  const char maj1_1[]  = "fun3_3_222211210211111110210110000";
  const char maj1_2[]  = "fun3_3_222212220212111210220210000";
  
  /* лфМаж2     = лфМаж (\ [x,y,z] -> x) */
  const char maj2[]    = "fun3_3_222212220211111110200010000";
  
  /* лфМаж3 a b = лфМаж (\ xs -> case xs of
   *                               [0,1,2] -> a
   *                               [1,2,0] -> a
   *                               [2,0,1] -> a
   *                               [0,2,1] -> b
   *                               [2,1,0] -> b
   *                               [1,0,2] -> b) */
  const char maj3_01[] = "fun3_3_222211200210111110210010000";
  const char maj3_12[] = "fun3_3_222212210211111210220110000";
  const char maj3_20[] = "fun3_3_222210220212111010200210000";

  /* минМаж = [лфМаж1 0, лфМаж1 1, лфМаж1 2, лфМаж2, лфМаж3 0 1, лфМаж3 1 2, лфМаж3 2 0] */
  fun_scan(maj1_0,  *majs + 0);
  fun_scan(maj1_1,  *majs + 1);
  fun_scan(maj1_2,  *majs + 2);
  fun_scan(maj2,    *majs + 3);
  fun_scan(maj3_01, *majs + 4);
  fun_scan(maj3_12, *majs + 5);
  fun_scan(maj3_20, *majs + 6);
}

int clone_contains_majority(const clone *cl) {
  fun *majs;
  size_t num;
  min_majorities(&majs, &num);

  for(fun *f = majs; f < majs + num; ++f) {
    int flag = 1;
    for(clone_iterator it = clone_iterator_begin(cl); !clone_iterator_end(cl, &it); clone_iterator_next(&it)) {
      pred p = clone_iterator_deref(&it);
      if(!fun_preserves_pred(f, &p)) { flag = 0; break; }
    }
    if(flag) { free(majs); return 1; }
  }

  free(majs);
  return 0;
}

int pred_preserves_majority(const pred *p) {
  fun *majs;
  size_t num_majs;
  min_majorities(&majs, &num_majs);

  int flag = 0;
  for(fun *f = majs; f < majs + num_majs; ++f) {
    if(fun_preserves_pred(f, p)) { flag = 1; break; }
  }
  free(majs);
  return flag;
}
