/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 *
 * This test computes some properties of the sublattices of R3(2),
 * containing 0, 1, 2, min, max.
 *
 ******************************************************************************/

#include "lattice.h"

/* A universe of predicates defining the sublattice of R3(2),
 * containing 0, 1, 2, min, max. */
static pred basic_preds[] = {
  /* false, true, eq */
/*   { .arity = 2, .data = 0   }, */
/*   { .arity = 2, .data = 511 }, */
/*   { .arity = 2, .data = 273 }, */
  
  /* left part */
  { .arity = 2, .data = 283 },
  { .arity = 2, .data = 275 },
  { .arity = 2, .data = 319 },
  
  /* central part */
  { .arity = 2, .data = 443 },
  { .arity = 2, .data = 311 },
  { .arity = 2, .data = 313 },
  { .arity = 2, .data = 447 },
  
  /* right part */    
  { .arity = 2, .data = 433 },
  { .arity = 2, .data = 305 },
  { .arity = 2, .data = 439 },
};
static const size_t num_basic_preds = sizeof(basic_preds) / sizeof(basic_preds[0]);


/** This functions reads from file the full lattice of clones in P3,
 * defined by predicates of arity <= 2, and filters it, selecting the
 * clones, that preserve the functions 0, 1, 2, min, max. The function
 * returns the resulting sublattice.
 */
lattice *get_sublattice33(const char *lt_name);


/** `get_ccplt33` constructs the lattice of all relational clone
 * in P3, preserving the functions 0, 1, 2, min, max.
 *
 * The function `get_ccplt33` differs from `get_sublattice33`, which
 * reads a previously constructed full lattice from file and then
 * selects classes, preserving the functions 0, 1, 2, min, max.
 */
ccplt *get_ccplt33();
