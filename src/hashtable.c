/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "utils.h"
#include "hashtable.h"

hash_table *hash_table_alloc(size_t capacity,
                             uint32_t (*hash) (const void *),
                             int (*eq) (const void *, const void *)) {
  hash_table *ht = malloc(sizeof(hash_table));
  assert(ht);
  /* capacity must be power of 2 */
  ht->capacity = int_pow2(int_log(2, 16*capacity));
  ht->table    = malloc(ht->capacity * sizeof(hash_elem *));
  assert(ht->table);
  memset(ht->table, 0, ht->capacity * sizeof(hash_elem *));
  ht->hash     = hash;
  ht->eq       = eq;
  return ht;
}

void hash_table_free(hash_table *ht) {
  for(hash_elem **elemp = ht->table; elemp < ht->table + ht->capacity; ++elemp) {
    hash_elem *elem = *elemp;
    while(elem != NULL) {
      hash_elem *next = elem->next;
      free(elem);
      elem = next;
    }
  }
  free(ht->table);
  free(ht);
}

void hash_table_insert(hash_table *ht, const void *key, const void *value) {
  uint32_t hash = ht->hash(key);
  hash_elem *prev = ht->table[hash & (ht->capacity - 1)];
  hash_elem *elem = malloc(sizeof(hash_elem));
  assert(elem);
  elem->key   = (void *)key;
  elem->value = (void *)value;
  elem->next  = prev;
  ht->table[hash & (ht->capacity - 1)] = elem;
}

void *hash_table_lookup(const hash_table *ht, const void *key) {
  uint32_t hash = ht->hash(key);
  hash_elem *elem = ht->table[hash & (ht->capacity - 1)];
  while(elem != NULL) {
    if(ht->eq(elem->key, key)) return elem->value;
    elem = elem->next;
  }
  return NULL;
}

int hash_table_max_chain(const hash_table *ht) {
  int max = 0;
  for(hash_elem **elemp = ht->table; elemp < ht->table + ht->capacity; ++elemp) {
    int m = 0;
    hash_elem *elem = *elemp;
    while(elem != NULL) {
      ++m;
      elem = elem->next;
    }
    if(m > max) max = m;
  }
  return max;
}

