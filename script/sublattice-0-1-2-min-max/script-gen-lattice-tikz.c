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

#include "lattice.h"

typedef struct {
  struct clone clone;

  class_idx cidx;
  layer_idx lidx;
  class_pos cpos;

  int x;
  int y;
} graph_class_descr_t;

/* Include generated files. */
#include "graph-class-positions.h.generated"

static void get_clone_positions(const struct clone *cl, int *x, int *y) {
  for(graph_class_descr_t *descr = graph_class_descrs; descr < graph_class_descrs + num_graph_class_descrs; ++descr) {
    if(clone_eq(cl, &descr->clone)) {
      *x = descr->x;
      *y = descr->y;
    }
  }
  fprintf(stderr, "ERROR: get_clone_positions: unknown clone:\n");
  clone_print_verbosely(stderr, cl);
}


/*
  \node[] (1-8)   at (-6, -2) {};
  \node[fill=blue] (4-260)  at (8, -11)   {};

  \draw[edge]      (0-0) -- (1-8);
*/

/* void gen_lattice_in_latex() { */
/*   printf("\begin{tikzpicture}[scale=0.57]\n"); */
/*   printf("  \n"); */
/*      */
/*   printf("  \draw[opacity = 0, use as bounding box] (-12.5, 1) rectangle (12.5, -17.5);\n"); */
/*   printf("  \n"); */
/*    */
/*   printf("  \tikzstyle{every node} = [circle, draw=black, fill=gray, inner sep=2pt]\n"); */
/*   printf("  \n"); */
/*    */
/*   printf("  \tikzstyle{edge}      = [draw, thick, post, black]\n"); */
/*   printf("  \tikzstyle{blue edge} = [draw, thick, post, blue]\n"); */
/*   printf("  \tikzstyle{red edge}  = [draw, thick, post, red]\n"); */
/*   printf("  \n"); */
/*    */
/*   printf("\end{tikzpicture}\n"); */
/* } */

