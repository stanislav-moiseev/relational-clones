/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef TEST_RANDOM_H
#define TEST_RANDOM_H

#include "fun.h"
#include "pred.h"
#include "utils.h"

/** Construct a random string representing predicate's extensional. */
void random_pred_extensional(uint64_t arity, char *str) {
  srand(clock());
  
  int shift = int_pow(K, arity);
  /* char str[shift+1]; */
  for(int i = 0; i < shift; ++i) {
    if((float)rand()/RAND_MAX > 0.5) {
      str[i] = '1';
    } else {
      str[i] = '0';
    }
  }
  str[shift] = 0;
}

void random_pred(pred *p) {
  uint32_t ar = rand() % 3;
  char str[pred_print_extensional_size()];
  random_pred_extensional(ar, str);
  pred_construct(ar, str, p);
}

void random_clone(clone *cl) {
  clone_init(cl);
  int num = rand() % (int_pow2(int_pow(K, 2)));
  for(int i = 0; i < num; ++i) {
    pred p;
    random_pred(&p);
    clone_insert_pred(cl, &p);
  }
}

#endif
