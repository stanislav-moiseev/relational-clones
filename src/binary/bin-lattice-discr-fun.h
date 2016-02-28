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

/** `lattice_discr_fun_log_read` load functions from a text log file.
 *
 * The file should have the following format:
 *
 * class 7696     (29:128)                 subclass 486261   (30:9695)             fun3_2_210111010
 * class 7696     (29:128)                 subclass 7699     (36:17)               fun3_3_210111210111210111210111210
 * class 12330    (29:163)                 subclass 13673    (30:126)              fun3_4_220220000222220000000000000220220200220210000200000200000000000202000000000000000
 */
void lattice_discr_fun_txt_read(const char *fin, fun **funs, size_t *size);

#endif
