/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes some properties of the sublattices of R3(2),
 * containing 0, 1, 2, min, max.
 *
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "sublattice33.h"

typedef struct {
  layer_idx lidx;
  class_pos cpos;

  int x;
  int y;
} class_positions_t;

static const class_positions_t class_positions[] = {
  { .lidx = 0, .cpos = 0,    .x = 0,  .y = 0    },
  { .lidx = 1, .cpos = 8,    .x = -6, .y = -2   },
  { .lidx = 1, .cpos = 16,   .x = 2,  .y = -2   },
  { .lidx = 1, .cpos = 15,   .x = 6,  .y = -2   },
  { .lidx = 1, .cpos = 9,    .x = 0,  .y = -2   },
  { .lidx = 2, .cpos = 71,   .x = 1,  .y = -4   },
  { .lidx = 2, .cpos = 53,   .x = -8, .y = -5   },
  { .lidx = 2, .cpos = 36,   .x = -6, .y = -5   },
  { .lidx = 3, .cpos = 199,  .x = -4, .y = -5   },
  { .lidx = 3, .cpos = 201,  .x = 4,  .y = -5   },
  { .lidx = 2, .cpos = 46,   .x = 6,  .y = -5   },
  { .lidx = 2, .cpos = 68,   .x = 8,  .y = -5   },
  { .lidx = 3, .cpos = 114,  .x = 0,  .y = -7   },
  { .lidx = 2, .cpos = 50,   .x = 1,  .y = -7   },
  { .lidx = 3, .cpos = 129,  .x = -8, .y = -8   },
  { .lidx = 3, .cpos = 192,  .x = 8,  .y = -8   },
  { .lidx = 3, .cpos = 203,  .x = 0,  .y = -9.3 },
  { .lidx = 4, .cpos = 258,  .x = -8, .y = -11  },
  { .lidx = 4, .cpos = 405,  .x = 0,  .y = -11  },
  { .lidx = 4, .cpos = 260,  .x = 8,  .y = -11  },
  { .lidx = 4, .cpos = 267,  .x = -6, .y = -8   },
  { .lidx = 4, .cpos = 457,  .x = -4, .y = -8   },
  { .lidx = 4, .cpos = 461,  .x = 4,  .y = -8   },
  { .lidx = 4, .cpos = 424,  .x = 6,  .y = -8   },
  { .lidx = 5, .cpos = 534,  .x = -6, .y = -11  },
  { .lidx = 5, .cpos = 872,  .x = 6,  .y = -11  },
  { .lidx = 6, .cpos = 958,  .x = -6, .y = -14  },
  { .lidx = 6, .cpos = 1034, .x = -4, .y = -14  },
  { .lidx = 5, .cpos = 497,  .x = -1, .y = -15  },
  { .lidx = 5, .cpos = 825,  .x = 1,  .y = -15  },
  { .lidx = 6, .cpos = 1036, .x = 4,  .y = -14  },
  { .lidx = 6, .cpos = 959,  .x = 6,  .y = -14  },
  { .lidx = 7, .cpos = 1601, .x = 0,  .y = -17  },
};
static const size_t num_class_positions = sizeof(class_positions) / sizeof(class_positions[0]);


static void get_class_positions(layer_idx lidx, class_pos cpos, int *x, int *y) {
  for(const class_positions_t *cp = class_positions; cp < class_positions + num_class_positions; ++cp) {
    if(cp->lidx == lidx && cp->cpos == cpos) {
      *x = cp->x;
      *y = cp->y;
      return;
    }
  }
  fprintf(stderr, "ERROR: get_class_positions: unknown class (lidx = %u, cpos = %u).\n", lidx, cpos);
}


void generate_graph_class_positions() {
  const char *lt_name = "data/lattice.2016";
  lattice *sublt = get_sublattice33(lt_name);

  printf("static const graph_class_descr_t graph_class_descrs[] = {\n");
  for(class **cp = sublt->classes; cp < sublt->classes + sublt->num_classes; ++cp) {
    class *c = *cp;
    
    int x = 0;
    int y = 0;
    get_class_positions(c->lidx, c->cpos, &x, &y);
    
    printf("  {\n");
    printf("    .cidx  = %u,\n", c->cidx);
    printf("    .lidx  = %u,\n", c->lidx);
    printf("    .cpos  = %u,\n", c->cpos);
    printf("    .clone = {\n");
    printf("      .data0 = 0x%0x,\n", c->clone.data0);
    printf("      .data1 = 0x%x,\n", c->clone.data1);
    printf("      .data2 = {");
    printf("0x%lx", c->clone.data2[0]);
    for(unsigned k = 1; k < CLONE_DATA2_SIZE; ++k) {
      printf(", 0x%lx", c->clone.data2[k]);
    }
    printf(" }\n");
    printf("    .x     = %d,\n", x);
    printf("    .y     = %d,\n", y);
    printf("    },\n");
    printf("  },\n");
  }

  printf("}\n");
  
  lattice_free(sublt);
}


int main() {
  generate_graph_class_positions();
}
