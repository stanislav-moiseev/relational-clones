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
static const pred basic_preds[] = {
  /* false, true, eq */
/*   { .arity = 2, .data = 0   }, */
/*   { .arity = 2, .data = 511 }, */
/*   { .arity = 2, .data = 273 }, */

  { .arity = 2, .data = 275 },  /* q1 */
  { .arity = 2, .data = 283 },  /* q2 */
  { .arity = 2, .data = 305 },  /* q3 */
  
  { .arity = 2, .data = 311 },  /* q4 */
  { .arity = 2, .data = 313 },  /* q5 */
  { .arity = 2, .data = 319 },  /* q6 */
  
  { .arity = 2, .data = 433 },  /* q7 */
  { .arity = 2, .data = 439 },  /* q8 */
  { .arity = 2, .data = 443 },  /* q9 */
  { .arity = 2, .data = 447 },  /* q10 */
  
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

/** A naming function for predicates that works with
 * `sublattice33_basic_preds` only.
 * Every predicate is printed as "q_{j}", where j is the number
 * of the predicate in the `sublattice33_basic_preds` list.
 */
const char *sublattice33_pred_naming_fn_latex(pred p);

