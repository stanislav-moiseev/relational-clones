/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_H
#define BINARY_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"
#include "class.h"


/** `pred_read` read one predicate from binary file.
 */
void pred_read(FILE *fd, pred *pred);

/** `class_read` reads the binary class data starting from current file
 * position.
 */
int class_read(FILE *fd, class *class);

/** `class_aread_layer` reads from binary file a layer of classes.
 * It allocates an array to store all classes.
 * The pointer should be free'd to release the storage.
 */
int class_aread_layer(FILE *fd, class **classes, size_t *size);


#endif
