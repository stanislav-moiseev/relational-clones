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
#include "binary/maj-lattice.h"

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

void maj_class_id_write(FILE *fd, const maj_class_id *id);

void maj_class_write(FILE *fd, const maj_class *class);

void maj_layer_write(FILE *fd, const maj_layer *layer);

/** `maj_lattice_write` writes the lattice to binary file.
 */
void maj_lattice_write(FILE *fd, const maj_lattice *lattice);


/******************************************************************************/
/** READ part */

void fun_read(FILE *fd, fun *fun);

void pred_read(FILE *fd, pred *pred);

void clone_read(FILE *fd, clone *clone);

void maj_class_id_read(FILE *fd, maj_class_id *id);

void maj_class_read(FILE *fd, maj_class *class);

void maj_layer_read(FILE *fd, maj_layer *layer);

/** `maj_lattice_read` reads the lattice from binary file.
 */
void maj_lattice_read(FILE *fd, maj_lattice *lattice);

#endif
