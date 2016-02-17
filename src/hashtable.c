/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "utils.h"
#include "hashtable.h"

hashtable *hashtable_alloc(size_t capacity,
                           uint32_t (*hash) (const void *),
                           int (*eq) (const void *, const void *)) {
  hashtable *ht = malloc(sizeof(hashtable));
  assert(ht);
  /* capacity must be power of 2 */
  ht->size     = 0;
  ht->capacity = int_pow2(int_log(2, 2*capacity));
  ht->table    = malloc(ht->capacity * sizeof(hash_elem *));
  assert(ht->table);
  memset(ht->table, 0, ht->capacity * sizeof(hash_elem *));
  ht->hash     = hash;
  ht->eq       = eq;
  return ht;
}

void hashtable_free(hashtable *ht) {
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

void hashtable_insert(hashtable *ht, const void *key, const void *value) {
  /* search for the element with the given key */
  uint32_t hash = ht->hash(key);
  hash_elem *elem = ht->table[hash & (ht->capacity - 1)];
  while(elem != NULL) {
    /* if found, update the value */
    if(ht->eq(elem->key, key)) {
      elem->value = (void *)value;
      return;
    }
    elem = elem->next;
  }

  /* if not found, create a new hash_elem */
  elem = malloc(sizeof(hash_elem));
  assert(elem);
  elem->key   = (void *)key;
  elem->value = (void *)value;
  elem->next  = ht->table[hash & (ht->capacity - 1)];
  ht->table[hash & (ht->capacity - 1)] = elem;
  ++ht->size;
}

void hashtable_remove(hashtable *ht, const void *key) {
  uint32_t hash         = ht->hash(key);
  hash_elem **prev_next = &ht->table[hash & (ht->capacity - 1)];
  hash_elem *elem       = ht->table[hash & (ht->capacity - 1)];
  while(elem != NULL) {
    if(ht->eq(elem->key, key)) {
      *prev_next = elem->next;
      free(elem);
      --ht->size;
      return;
    }
    prev_next = &elem->next;
    elem = elem->next;
  }
}

void *hashtable_lookup(const hashtable *ht, const void *key) {
  uint32_t hash = ht->hash(key);
  hash_elem *elem = ht->table[hash & (ht->capacity - 1)];
  while(elem != NULL) {
    if(ht->eq(elem->key, key)) return elem->value;
    elem = elem->next;
  }
  return NULL;
}

unsigned hashtable_max_chain(const hashtable *ht) {
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


/******************************************************************************/
/** Hash table iterators */

hashtable_iterator hashtable_iterator_begin(const hashtable *ht) {
  hashtable_iterator it = { .ht    = ht,
                            .elem  = NULL,
                            .elemp = ht->table - 1 };
  hashtable_iterator_next(&it);
  return it;
}

int hashtable_iterator_end(hashtable_iterator *it) {
  return (it->elemp == it->ht->table + it->ht->capacity);
}

void hashtable_iterator_next(hashtable_iterator *it) {
  /* if `it != hashtable_iterator_begin`, proceed to the next element */
  if(it->elem != NULL) { it->elem = it->elem->next; }

  /* if `it == hashtable_iterator_begin` or the next element is NULL. */
  if(it->elem == NULL) {
    do {
      ++it->elemp;
    } while(it->elemp < it->ht->table + it->ht->capacity && *it->elemp == NULL);
    if(it->elemp < it->ht->table + it->ht->capacity) {
      it->elem = *it->elemp;
    }
  }
}

hash_elem *hashtable_iterator_deref(const hashtable_iterator *it) {
  return it->elem;
}
