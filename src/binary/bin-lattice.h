/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_LATTICE_H
#define BINARY_LATTICE_H

#include "lattice.h"

void lattice_write(const char *fname, const lattice *lt);

lattice *lattice_read(const char *fname);

#endif
