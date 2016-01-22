/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_2016_H
#define BINARY_2016_H

#include <stdint.h>

#include "utils.h"
#include "pred.h"
#include "clone.h"
#include "class.h"
#include "lattice.h"

/** `lattic_read` reads the lattice from binary file.
 */
void lattice_read(FILE *fd, lattice *lattice);

/** `lattic_write` writes the lattice to binary file.
 */
void lattice_write(FILE *fd, const lattice *lattice);

#endif
