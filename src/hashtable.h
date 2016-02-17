/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * Simple chaining hash table with fixed capacity.
 ******************************************************************************/

#ifndef HASHTABLE_H
#define HASHTABLE_H

#include <stdint.h>

/** Hash table element as a linked list. */
struct hash_elem {
  void *key;
  void *value;
  struct hash_elem *next;
};
typedef struct hash_elem hash_elem;

struct hashtable {
  /* number of elements in the hash table */
  size_t size;
  
  /* The capacity of the hash table. The capacity is chosen at hash table
   * creation and cannot be increased in future. */
  size_t capacity;

  /* key hashing function */
  uint32_t (*hash) (const void *key);

  /* key comparison function */
  int (*eq) (const void *key1, const void *key2);

  /* an array of pointers to hash_elem */
  hash_elem **table;
};
typedef struct hashtable hashtable;

/** `hashtable_alloc` creates a hash table with the given capacity. */
hashtable *hashtable_alloc(size_t capacity,
                           uint32_t (*hash) (const void *),
                           int (*eq) (const void *, const void *));

void hashtable_free(hashtable *ht);

/** `hash_table_insert` inserts an element to the hash table.
 *
 * If the element with the given key is already in the hash table, this function
 * will update the element's value. */
void hashtable_insert(hashtable *ht, const void *key, const void *value);

/** `hashtable_remove` removes the element with the given key from the hash
 * table if it was present in the table; otherwise the function does nothing.
 */
void hashtable_remove(hashtable *ht, const void *key);

/** `hashtable_lookup` searches for the element with the given key.
 *
 * If it's been found, the functions returns the element's value;
 * otherwise it returns NULL.
 */
void *hashtable_lookup(const hashtable *ht, const void *key);

/** `hashtable_max_chain` returns the length of the longest chain of elements
 * with identical key hashes.
 */
unsigned hashtable_max_chain(const hashtable *ht);


/******************************************************************************/
/** Hash table iterators */

/** `hashtable_iterator` iterates the elements of the hash table in an
 * unspecified order. */
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
