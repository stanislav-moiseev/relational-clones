/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
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

/** Simple chaining hash table with fixed capacity.
 */
struct hash_table {
  size_t capacity;

  /* key hashing function */
  uint32_t (*hash) (const void *);

  /* key comparison function */
  int (*eq) (const void *, const void *);

  /* an array of pointers to hash_elem */
  hash_elem **table;
};
typedef struct hash_table hash_table;

hash_table *hash_table_alloc(size_t capacity,
                             uint32_t (*hash) (const void *),
                             int (*eq) (const void *, const void *));

void hash_table_free(hash_table *ht);

void hash_table_insert(hash_table *ht, const void *key, const void *value);

void *hash_table_lookup(const hash_table *ht, const void *key);

int hash_table_max_chain(const hash_table *ht);

#endif
