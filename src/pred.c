/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "utils.h"
#include "pred.h"

int pred_construct(uint32_t arity, const char *str, pred *pred) {
  pred->arity      = arity;
  pred->data       = 0;

  for(int pos = int_pow(K, arity) - 1; pos >= 0; --pos) {
    pred->data <<= 1;
    switch(*str) {
    case 0:     return 0;
    case '0':   break;
    case '1':   pred->data |= 1; break;
    default:    return 0;
    }
    ++str;
  }

  /* if the string have not finished yet */
  if(*str) return 0;
  return 1;
}

int pred_consistent(const pred *pred) {
  uint64_t shift = int_pow(K, pred->arity);
  /* check that the `struct pred` has enough bits to store the predicate's
   * content */
  if(shift > 64) return 0;

  /* check that all unnecessary bits in pred->data are set to zero */
  if(pred->data >= (uint64_t)1 << shift) return 0;
  
  return 1;
}

#define PRED_FINGERPRINT_SIZE                    \
  (7             /* for "pred__" string */       \
   + 2           /* for K */                     \
   + 3           /* for pred->arity */           \
   + 16          /* for pred->data */            \
   + 1)          /* for terminating null byte */ \

const char *pred_print_fingerprint(const pred *pred) {
  assert(K < 100);
  assert(pred->arity < 1000);
  static char str[PRED_FINGERPRINT_SIZE];
  sprintf(str, "pred%u_%lu_%lx", K, pred->arity, pred->data);
  return str;
}

size_t pred_print_extensional_size() {
  return 65;            /* 64 bytes + terminating null byte */
}

void pred_print_extensional(char *str, const pred *pred) {
  for(int64_t shift = int_pow(K, pred->arity) - 1; shift >= 0; --shift) {
    if(pred_compute(pred, shift)) {
      str += sprintf(str, "1");
    } else {
      str += sprintf(str, "0");
    }
  }
}

const char *pred_print_extensional_ex(const pred *p) {
  assert(K <= 9 && "Only one-digit Ek elems are suppored");
  assert(p->arity <= 2);
  static char _str[64];
  char *str = _str;
  
  /* treat predicates of zero arity specially */
  if(p->arity == 0) {
    if(p->data != 0) sprintf(str, "{<>}");
    else sprintf(str, "{}");
    return str;
  }

  str += sprintf(str, "{");
  int flag = 0; /* if we've written at least one tuple. */
  for(int64_t shift = int_pow(K, p->arity) - 1; shift >= 0; --shift) {
    if(pred_compute(p, shift)) {
      if(flag) str += sprintf(str, ", ");
      uint32_t digits[p->arity];
      get_K_digits(digits, p->arity, shift);
      for(size_t i = 0; i < p->arity; ++i) {
        str += sprintf(str, "%u", digits[i]);
      }
      flag = 1;
    }
  }
  str += sprintf(str, "}");
  
  return _str;
}

pred pred_scan_ex(uint32_t arity, const char *str) {
  assert(K <= 9 && "Only one-digit Ek elems are suppored");
  assert(arity <= 2);

  if(arity == 0) {
    pred p_false, p_true;
    pred_construct(0, "0", &p_false);
    pred_construct(0, "1", &p_true);
    if(strcmp(str, "{}") == 0)   return p_false;
    if(strcmp(str, "{<>}") == 0) return p_true;
    assert(0 && "invalid string for predicate extensional");
  }
  
  pred p;
  pred_init(&p, arity);
  
  assert(str[0] == '{');
  ++str;

  while(str[0] != '}') {
    uint32_t digits[arity];
    for(uint32_t i = 0; i < arity; ++i) {
      char c = str[0];
      assert(c >= '0' && c <= '0' + K);
      digits[i] = c - '0';
      ++str;
    }
    uint64_t tuple = get_K_tuple(digits, arity);
    pred_set(&p, tuple);
    if(str[0] == ',') ++str;
    while(str[0] == ' ') ++str;
  }

  return p;
}

/******************************************************************************/
/** basic operations */

void pred_extensional(const pred *pred, uint32_t **ext, size_t *size) {
  *ext = malloc(int_pow(K, pred->arity) * sizeof(uint32_t));
  assert(*ext != NULL);
  size_t _size = 0;
  for(int64_t shift = int_pow(K, pred->arity) - 1; shift >= 0; --shift) {
    if(pred_compute(pred, shift)) {
      (*ext)[_size] = shift;
      ++_size;
    }
  }
  *size = _size;
}

int64_t pred_cardinality(const pred *pred) {
  return popcount64(pred->data);
}



/******************************************************************************/
/* Database of known predicates (with mathematical names) */

struct named_pred {
  pred pred;
  const char *name;
};
typedef struct named_pred named_pred;

static named_pred *named_preds = NULL;
static size_t num_named_preds  = 0;

struct named_pred_info {
  uint32_t arity;
  const char *ext;
  const char *name;
};
typedef struct named_pred_info named_pred_info;

static named_pred_info named_pred_infos[] = {
  /* Predicates of arity 0 */
  { .arity = 0, .ext = "{}",     .name = "false" },
  { .arity = 0, .ext = "{<>}",   .name = "true" },

  /* Predicates of arity 1 */
  /* central of arity 1 */
  { .arity = 1, .ext = "{0}",    .name = "set {0}" },
  { .arity = 1, .ext = "{1}",    .name = "set {1}" },
  { .arity = 1, .ext = "{2}",    .name = "set {2}" },
  { .arity = 1, .ext = "{0, 1}", .name = "set {0, 1}" },
  { .arity = 1, .ext = "{0, 2}", .name = "set {0, 2}" },
  { .arity = 1, .ext = "{1, 2}", .name = "set {1, 2}" },

    
  /* Predicates of arity 2 */
  /* equality */
  { .arity = 2, .ext = "{00, 11, 22}",                     .name = "equality" },
    
  /* partial orders */
  { .arity = 2, .ext = "{22, 11, 00, 01}",                 .name = "partial order 0 < 1" },
  { .arity = 2, .ext = "{22, 11, 00, 02}",                 .name = "partial order 0 < 2" },
  { .arity = 2, .ext = "{22, 11, 00, 10}",                 .name = "partial order 1 < 0" },
  { .arity = 2, .ext = "{22, 11, 00, 12}",                 .name = "partial order 1 < 2" },
  { .arity = 2, .ext = "{22, 11, 00, 20}",                 .name = "partial order 2 < 0" },
  { .arity = 2, .ext = "{22, 11, 00, 21}",                 .name = "partial order 2 < 1" },

  { .arity = 2, .ext = "{22, 11, 00, 01, 02}",             .name = "partial order 0 < 1, 0 < 2" },
  { .arity = 2, .ext = "{22, 11, 00, 10, 12}",             .name = "partial order 1 < 0, 1 < 2" },
  { .arity = 2, .ext = "{22, 11, 00, 20, 21}",             .name = "partial order 2 < 0, 2 < 1" },
  { .arity = 2, .ext = "{22, 11, 00, 02, 12}",             .name = "partial order 0 < 2, 1 < 2" },
  { .arity = 2, .ext = "{22, 11, 00, 10, 20}",             .name = "partial order 1 < 0, 2 < 0" },
  { .arity = 2, .ext = "{22, 11, 00, 01, 21}",             .name = "partial order 0 < 1, 2 < 1" },

  /* linearity order */
  { .arity = 2, .ext = "{00, 11, 22, 01, 02, 12}",         .name = "linear order (0 < 1 < 2)" },
  { .arity = 2, .ext = "{00, 11, 22, 02, 01, 21}",         .name = "linear order (0 < 2 < 1)" },
  { .arity = 2, .ext = "{00, 11, 22, 10, 12, 02}",         .name = "linear order (1 < 0 < 2)" },
  { .arity = 2, .ext = "{00, 11, 22, 12, 10, 20}",         .name = "linear order (1 < 2 < 0)" },
  { .arity = 2, .ext = "{00, 11, 22, 20, 21, 01}",         .name = "linear order (2 < 0 < 1)" },
  { .arity = 2, .ext = "{00, 11, 22, 21, 20, 10}",         .name = "linear order (2 < 1 < 0)" },

  /* preorders */
  { .arity = 2, .ext = "{00, 11, 22, 01, 10, 02, 12}",     .name = "preorder (0 ~ 1) < 2" },
  { .arity = 2, .ext = "{00, 11, 22, 02, 20, 01, 21}",     .name = "preorder (0 ~ 2) < 1" },
  { .arity = 2, .ext = "{00, 11, 22, 12, 21, 10, 20}",     .name = "preorder (1 ~ 2) < 0" },
  { .arity = 2, .ext = "{00, 11, 22, 01, 02, 12, 21}",     .name = "preorder 0 < (1 ~ 2)" },
  { .arity = 2, .ext = "{00, 11, 22, 10, 12, 02, 20}",     .name = "preorder 1 < (0 ~ 2)" },
  { .arity = 2, .ext = "{00, 11, 22, 20, 21, 01, 10}",     .name = "preorder 2 < (0 ~ 1)" },

  /* autodual with respect to a permutation */
  { .arity = 2, .ext = "{01, 12, 20}",                     .name = "permutation (0, 1, 2)" },
  { .arity = 2, .ext = "{02, 21, 10}",                     .name = "permutation (0, 2, 1)" },
  { .arity = 2, .ext = "{10, 02, 21}",                     .name = "permutation (1, 0, 2)" },
  { .arity = 2, .ext = "{12, 20, 01}",                     .name = "permutation (1, 2, 0)" },
  { .arity = 2, .ext = "{20, 01, 12}",                     .name = "permutation (2, 0, 1)" },
  { .arity = 2, .ext = "{21, 10, 02}",                     .name = "permutation (2, 1, 0)" },

  /* equivalence relation */
  { .arity = 2, .ext = "{00, 11, 22, 01, 10}",             .name = "equivalence (0 ~ 1)" },
  { .arity = 2, .ext = "{00, 11, 22, 02, 20}",             .name = "equivalence (0 ~ 2)" },
  { .arity = 2, .ext = "{00, 11, 22, 12, 21}",             .name = "equivalence (1 ~ 2)" },

  /* central */
  { .arity = 2, .ext = "{00, 11, 22, 01, 10, 02, 20}",     .name = "central {0}" },
  { .arity = 2, .ext = "{00, 11, 22, 10, 01, 12, 21}",     .name = "central {1}" },
  { .arity = 2, .ext = "{00, 11, 22, 20, 02, 21, 12}",     .name = "central {2}" },

  /* all except one */
  { .arity = 2, .ext = "{21, 20, 12, 11, 10, 02, 01, 00}", .name = "all except 22" },
  { .arity = 2, .ext = "{22, 20, 12, 11, 10, 02, 01, 00}", .name = "all except 21" },
  { .arity = 2, .ext = "{22, 21, 12, 11, 10, 02, 01, 00}", .name = "all except 20" },
  { .arity = 2, .ext = "{22, 21, 20, 11, 10, 02, 01, 00}", .name = "all except 12" },
  { .arity = 2, .ext = "{22, 21, 20, 12, 10, 02, 01, 00}", .name = "all except 11" },
  { .arity = 2, .ext = "{22, 21, 20, 12, 11, 02, 01, 00}", .name = "all except 10" },
  { .arity = 2, .ext = "{22, 21, 20, 12, 11, 10, 01, 00}", .name = "all except 02" },
  { .arity = 2, .ext = "{22, 21, 20, 12, 11, 10, 02, 00}", .name = "all except 02" },
  { .arity = 2, .ext = "{22, 21, 20, 12, 11, 10, 02, 01}", .name = "all except 00" },

  /* x + y == c */
  { .arity = 2, .ext = "{00, 12, 21}",                     .name = "x + y == 0" },
  { .arity = 2, .ext = "{01, 10, 22}",                     .name = "x + y == 1" },
  { .arity = 2, .ext = "{02, 20, 11}",                     .name = "x + y == 2" },
  
  /* other */
  { .arity = 2, .ext = "{21, 20, 12, 10, 02, 01}",         .name = "inequality" },
};


static void named_preds_init() {
  num_named_preds = sizeof(named_pred_infos) / sizeof(named_pred_info);
  named_preds     = malloc(num_named_preds * sizeof(named_pred));
  for(size_t i = 0; i < num_named_preds; ++i) {
    named_pred_info *info = named_pred_infos + i;
    named_preds[i].pred = pred_scan_ex(info->arity, info->ext);
    named_preds[i].name = info->name;
  }
}

const char *pred_name(const pred *p) {
  if(named_preds == NULL) named_preds_init();
  
  for(named_pred *np = named_preds; np < named_preds + num_named_preds; ++np) {
    if(pred_eq(&np->pred, p)) return np->name;
  }
  return NULL;
}

const pred *pred_get(const char *name) {
  if(named_preds == NULL) named_preds_init();

  for(named_pred *np = named_preds; np < named_preds + num_named_preds; ++np) {
    if(strcmp(np->name, name) ==  0) return &np->pred;
  }
  assert(0 && "unknown predicate name");
  return NULL;
}
