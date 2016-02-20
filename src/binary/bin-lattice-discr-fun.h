/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_LDF_H
#define BINARY_LDF_H

#include "lattice.h"
#include "fun.h"

struct discrfun {
  class_idx parent;
  class_idx child;
  fun fun;
};
typedef struct discrfun discrfun;

/** `lattice_discr_fun_write` writes a list of functions discriminating
 *  all pairs "class — maximal proper subclass".
 */
void lattice_discr_fun_write(const char *fout, const discrfun *dfs, size_t size);

/** `lattice_discr_fun_read` reads a list of discriminating functions from a
 * file, and writes it to `dfs`.
 *
 * The procedure allocates memory to store the discriminating function. Memory
 * should be freed to release the storage.
 */
void lattice_discr_fun_read(const char *fin, discrfun **dfs, size_t *size);

#endif
