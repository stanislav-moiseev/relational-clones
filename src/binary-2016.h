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
/** Common part */

void uint32_write(FILE *fd, uint32_t x);

void uint64_write(FILE *fd, uint64_t x);

uint32_t uint32_read(FILE *fd);

uint64_t uint64_read(FILE *fd);


/******************************************************************************/
/** WRITE part */

void fun_write(FILE *fd, const fun *fun);

void pred_write(FILE *fd, const pred *pred);

void clone_write(FILE *fd, const clone *clone);

void class_id_write(FILE *fd, const class_id *id);

void class_write(FILE *fd, const class *class);

void layer_write(FILE *fd, const layer *layer);

/** `lattic_write` writes the lattice to binary file.
 */
void lattice_write(FILE *fd, const lattice *lattice);


/******************************************************************************/
/** READ part */

void fun_read(FILE *fd, fun *fun);

void pred_read(FILE *fd, pred *pred);

void clone_read(FILE *fd, clone *clone);

void class_id_read(FILE *fd, class_id *id);

void class_read(FILE *fd, class *class);

void layer_read(FILE *fd, layer *layer);

/** `lattic_read` reads the lattice from binary file.
 */
void lattice_read(FILE *fd, lattice *lattice);

#endif
