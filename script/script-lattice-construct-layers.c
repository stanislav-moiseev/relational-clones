/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include "lattice.h"
#include "binary/bin-closure-clone-pred.h"

void script_lattice_construct_layers(const char *ccp_name) {
  printf("reading \"%s\"...", ccp_name); fflush(stdout);
  ccplt *ccplt = ccplt_read(ccp_name);
  printf("\tOk.\n");

  lattice *lt = lattice_alloc();
  lattice_construct_layers(lt, ccplt);
  
  lattice_free(lt);
  ccplt_free(ccplt);
  return;
}

int main() {
  time_t t0 = time(NULL);
  printf("script-lattice-construct-layers:\n");
  script_lattice_construct_layers("data/closure-clone-pred.2016");
  printf("Ok.\n");
  printf("%.2f min\n", difftime(time(NULL), t0) / 60.);
}
