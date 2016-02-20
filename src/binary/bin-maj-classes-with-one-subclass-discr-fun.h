/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef MAJ_CWOSDF_H
#define MAJ_CWOSDF_H

#include "fun.h"
#include "maj-lattice.h"

/**
 * classes      - a list of classes with one subclass (parents of the pair)
 *                which the discriminating functions are given for.
 * fun          - a list of discriminating functions.
 */
void write_classes_with_one_subclass_discr_fun(FILE *fd, const majlattice *lattice, majclass * const *classes, size_t num_classes, const fun *fun);

void read_classes_with_one_subclass_discr_fun(FILE *fd, const majlattice *lattice, majclass ***classes, size_t *num_classes, fun **funs);


#endif
