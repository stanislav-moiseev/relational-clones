/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_BIN_MAJ_LATTICE_H
#define BINARY_BIN_MAJ_LATTICE_H

#include "maj-lattice.h"

void majclass_id_write(FILE *fd, const majclass_id *id);

/** `majlattice_write` writes the lattice to binary file.
 */
void majlattice_write(FILE *fd, const majlattice *lattice);

void majclass_id_read(FILE *fd, majclass_id *id);

/** `majlattice_read` reads the lattice from binary file.
 */
majlattice *majlattice_read(const char *fname);

#endif

