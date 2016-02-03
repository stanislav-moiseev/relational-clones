/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "algorithms/alg-lattice.h"

void construct_lattice() {
  lattice lt;
  latice_construct(&lt);
}

int main() {
  printf("script-construct-lattice:\n"); fflush(stdout);
  construct_lattice();
  printf("Ok.\n");
}
