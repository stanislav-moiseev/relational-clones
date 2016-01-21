/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_H
#define BINARY_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"


/** `pred_read` read one predicate from binary file.
 */
void pred_read(FILE *fd, pred *pred);

/** `clone_read` reads the binary clone data starting from current file
 * position.
 * If `pred_list != NULL`, the function allocates an array and writes the
 * predicate basis to `pred_list`.
 * The pointer should be free'd to release the storage.
 */
int clone_read(FILE *fd, clone *clone, pred **pred_list, uint64_t *size);

/** `clone_aread_layer` reads from binary file a layer of clones.
 * It allocates an array to store all clone.
 * The pointer should be free'd to release the storage.
 */
int clone_aread_layer(FILE *fd, clone **clones, size_t *size);


#endif
