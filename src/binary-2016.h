/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_2016_H
#define BINARY_2016_H

#include <stdint.h>

#include "utils.h"
#include "fun.h"
#include "pred.h"
#include "clone.h"
#include "class.h"
#include "lattice.h"

/******************************************************************************/
/** WRITE part*/

void fun_write(FILE *fd, const fun *fun);

void pred_write(FILE *fd, const pred *pred);

void clone_write(FILE *fd, const clone *clone);

void class_write(FILE *fd, const class *class);

void layer_write(FILE *fd, const layer *layer);

/** `lattic_write` writes the lattice to binary file.
 */
void lattice_write(FILE *fd, const lattice *lattice);


/******************************************************************************/
/** READ part*/

void fun_read(FILE *fd, fun *fun);

void pred_read(FILE *fd, pred *pred);

void clone_read(FILE *fd, clone *clone);

void class_read(FILE *fd, class *class);

void layer_read(FILE *fd, layer *layer);

/** `lattic_read` reads the lattice from binary file.
 */
void lattice_read(FILE *fd, lattice *lattice);

#endif
