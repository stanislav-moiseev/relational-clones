/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_BIN_MAJ_LATTICE_H
#define BINARY_BIN_MAJ_LATTICE_H

#include "maj-lattice.h"

void maj_class_id_write(FILE *fd, const maj_class_id *id);

/** `maj_lattice_write` writes the lattice to binary file.
 */
void maj_lattice_write(FILE *fd, const maj_lattice *lattice);

void maj_class_id_read(FILE *fd, maj_class_id *id);

/** `maj_lattice_read` reads the lattice from binary file.
 */
maj_lattice *maj_lattice_read(const char *fname);

#endif

