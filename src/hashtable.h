/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Simple chaining hash table with fixed capacity.
 ******************************************************************************/

#ifndef HASHTABLE_H
#define HASHTABLE_H

#include <stdint.h>

/** Linked list.
*/
struct hash_elem {
  void *key;
  void *value;
  struct hash_elem *next;
};
typedef struct hash_elem hash_elem;

struct hashtable {
  /* the capacity is determined at hash table creation and cannot be increased */
  size_t capacity;

  /* key hashing function */
  uint32_t (*hash) (const void *key);

  /* key comparison function */
  int (*eq) (const void *key1, const void *key2);

  /* an array of pointers to hash_elem */
  hash_elem **table;
};
typedef struct hashtable hashtable;

hashtable *hashtable_alloc(size_t capacity,
                             uint32_t (*hash) (const void *),
                           int (*eq) (const void *, const void *));

void hashtable_free(hashtable *ht);

/** `hash_table_insert` inserts an element to the hash table. If the element is
 * already in the hash table, this function will insert its copy. */
void hashtable_insert(hashtable *ht, const void *key, const void *value);

void *hashtable_lookup(const hashtable *ht, const void *key);

unsigned hashtable_max_chain(const hashtable *ht);


/******************************************************************************/
/** Hash table iterators */

struct hashtable_iterator {
  const hashtable *ht;
  hash_elem *elem;
  hash_elem **elemp;
};
typedef struct hashtable_iterator hashtable_iterator;

hashtable_iterator hashtable_iterator_begin(const hashtable *ht);

int hashtable_iterator_end(hashtable_iterator *it);

void hashtable_iterator_next(hashtable_iterator *it);

hash_elem *hashtable_iterator_deref(const hashtable_iterator *it);

#endif
