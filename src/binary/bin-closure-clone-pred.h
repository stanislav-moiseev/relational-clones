/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#ifndef BINARY_BIN_CCPLT_H
#define BINARY_BIN_CCPLT_H

#include "algorithm/alg-closure-clone-pred.h"

void ccplt_write(const char *fname, const ccplt *lt);

ccplt *ccplt_read(const char *fname);

#endif

