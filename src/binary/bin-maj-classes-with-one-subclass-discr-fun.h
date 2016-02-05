/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef MAJ_CWOSDF_H
#define MAJ_CWOSDF_H

#include "fun.h"
#include "maj-lattice.h"

void write_classes_with_one_subclass_discr_fun(FILE *fd, const maj_lattice *lattice, maj_class * const *classes, size_t num_classes, const fun *fun);

void read_classes_with_one_subclass_discr_fun(FILE *fd, const maj_lattice *lattice, maj_class ***classes, size_t *num_classes, fun **funs);


#endif