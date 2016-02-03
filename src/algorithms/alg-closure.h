/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef ALGORITHMS_ALG_MAJ_H
#define ALGORITHMS_ALG_MAJ_H

#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "closure.h"

struct closure_two_preds_table {
  clone *data[3][3];
};

typedef struct closure_two_preds_table closure_two_preds_table;

void closure_two_preds_table_free(closure_two_preds_table *table);

/** `clone_closure_two_preds_construct_table` computes the closure of
 *      { false(0), true(0), eq(2), p1, p2 }
 * for all pairs of essential predicates (p1, p2)
 * and writes the result to the table.
 *
 * If either p1 or p2 is not essential, the functions writes the empty clone.
 *
 * The function allocates memory to store the table.
 * Memory should be freed by calling closure_two_preds_table_free.
 */
void clone_closure_two_preds_construct_table(closure_two_preds_table *table);


#endif
