/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_CLOSURE_TWO_PREDS
#define BINARY_CLOSURE_TWO_PREDS

#include "closure.h"


void closure_two_preds_write(FILE *fd, const closure_table_two_preds *table);

/**
 * The function allocates memory to store the table.
 * Memory should be freed by calling closure_table_two_preds_free.
 */
void closure_two_preds_read(FILE *fd, closure_table_two_preds *table);

#endif
