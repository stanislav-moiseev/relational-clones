/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_H
#define BINARY_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"
#include "class.h"
#include "lattice.h"

/** `pred_read` read one predicate from binary file.
 */
void pred_read(FILE *fd, pred *pred);

/** `class_read` reads the binary class data starting from current file
 * position.
 */
int class_read(FILE *fd, class *class);

/** `layer_aread_classes` reads from binary file a layer of classes.
 * It allocates an array to store all classes.
 * The pointer should be free'd to release the storage.
 */
void layer_aread_classes(FILE *fd, layer *layer);

void layer_aread_connections(FILE *fd, layer *layer);

/**
 * `dir_clones` - directory where to look for binary files with clones
 * `dir_connectoins` - directory where to look for binary files with connections
 * between clones (clones' subclasses)
 * The function allocates memory to store `lattice`.
 */
void lattice_read(int num_layers, const char *dir_clones, const char *dir_connections, lattice *lattice);

#endif
