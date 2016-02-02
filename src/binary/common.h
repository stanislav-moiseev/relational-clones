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

/******************************************************************************/
/** READ part */

void fun_read(FILE *fd, fun *fun);

void pred_read(FILE *fd, pred *pred);

void clone_read(FILE *fd, clone *clone);

#endif
