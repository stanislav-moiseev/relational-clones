/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_2013_H
#define BINARY_2013_H

#include <stdint.h>

#include "pred.h"
#include "clone.h"
#include "maj-lattice.h"

/** `pred_read` read one predicate from binary file.
 */
void pred_read_2013(FILE *fd, pred *pred);

/** `class_read` reads the binary class data starting from current file
 * position.
 */
int maj_class_read_2013(FILE *fd, majclass *class);

/** `layer_aread_classes` reads from binary file a layer of classes.
 * It allocates an array to store all classes.
 * The pointer should be free'd to release the storage.
 */
void majlayer_aread_classes_2013(FILE *fd, majlayer *layer);

/** `layer_aread_connections` reads the list of subclasses from file.
 */
void majlayer_aread_connections_2013(FILE *fd, majlayer *layer);

/**
 * `dir_clones` - directory where to look for binary files with clones
 * `dir_connectoins` - directory where to look for binary files with connections
 * between clones (clones' subclasses)
 * The function allocates memory to store `lattice`.
 */
void majlattice_read_2013(int num_layers, const char *dir_clones, const char *dir_connections, majlattice *lattice);

#endif
