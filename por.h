/***************************************************************************************
 *                   The Patterns of Resemblance Arithmetic Library                    *
 *                                                                                     *
 *                              (By Samuel Alexander)                                  *
 *                           (Department of Mathematics)                               *
 *                           (The Ohio State University)                               *
 ***************************************************************************************
 *         As seen in the Online Patterns of Resemblance Ordinal Calculator            *
 *            For documentation, see http://www.semitrivial.com/patterns               *
 ***************************************************************************************
 * This library implements basic arithmetic for Timothy J. Carlson's Patterns of       *
 * Resemblance ordinal notation system.  Patterns of resemblance are a combinatorial   *
 * way of notating very large ordinals (up to the ordinal of Pi^1_1-CA_0, to be        *
 * precise).  The PORAL (Patterns of Resemblance Arithmetic Library) is a patterns     *
 * implementation in C.                                                                *
 ***************************************************************************************
 * por.h                                                                               *
 ***************************************************************************************
 * Header file for por.c (miscellaneous pattern manipulations that don't go elsewhere) *
 **************************************************************************************/

#ifndef POR_H_INCLUDED
#define POR_H_INCLUDED

/*
 * The PATTERNS_DATABASE symbol should remain undefined by users of the library
 * other than the Patterns of Resemblance Calculator at http://www.xamuel.com/patterns
 * (The exception would be if you write a custom save_pattern function, in which
 *  case the symbol saves you from having to figure out the best places to call
 *  that function)
 */
//#define PATTERNS_DATABASE

#include "macro.h"
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

/*
 * Nonmagical numbers
 */
#define MAX_NODES_PER_PATTERN_UPPER 250
#define EXPLOGIND_LIMIT 20

/*
 * Typedefs
 */
typedef struct AMAL amal;
typedef struct AO_RECORD ao_record;
typedef struct AO_DETAIL ao_detail;

/*
 * Data structure for an amalgamation p of two patterns p1 and p2.
 * Also contains pointers pi_in_p (i=1,2) which indicate where, in p,
 * the designated points of p1 and p2 embed.
 */
struct AMAL
{
  amal *next;
  amal *prev;
  pattern *p;
  pattern *p1;
  pattern *p2;
  node *p1_in_p;
  node *p2_in_p;
};

typedef enum
{
  PATTERN_PURE=0, PATTERN_ADD=1
} pattern_types;

/*
 * Data structure to hold details about a step in the amalgamation
 * algorithm (to support the amalgamation algorithm's ability to
 * show its work).
 */
struct AO_RECORD
{
  ao_record *next;
  ao_record *prev;
  char *txt;
  ao_detail *details;
};

/*
 * Specific details about a step in the amalgamation algorithm
 * (to support the algorithm's ability to show its work).
 */
struct AO_DETAIL
{
  ao_detail *next;
  ao_detail *prev;
  pattern *p1;
  pattern *p2;
  int p1_is_true;
  int p2_is_true;
  int over_n_nodes;
  int id;
};

#define PATTERN_ADDITIVE PATTERN_ADD

/*
 * Function prototypes
 */

/* patterns.c */
pattern *copy_pattern( pattern *p );

/* por.c */
char *get_new_pattern_id(void);
char *assign_node_id( node *n, pattern *p );
pattern *eliminate_duplicate_pattern(pattern *p);
void kill_pattern(pattern *p);
void kill_node( node *n );
int same_pattern( pattern *p, pattern *q );
pattern *get_pattern_by_id( char *id );
node *get_node_by_id( pattern *p, char *id );
int decomposition_length( node **decomposition );
node *get_node_by_position( pattern *p, int pos );
char *can_insert_node_before( node *n );
node *insert_node_before( node *n, pattern *p );
int lex_leq( node **x, node **y );
char *decomposition_inconsistent_with_addition_tree( node **d, node *n, pattern *p );
int is_prev_decomposition( node **prev, node **next );
char *decomposition_to_text( node **d );
int init_zero_patterns(void);
void fix_node_names(pattern *p);
int transitively_close_less1( pattern *p );
node **get_decomposition_of_sum( node *n, node *m );
int same_decompositions( node **d1, node **d2 );
char *next_node_id( char *prev );
pattern *adstend_pattern( pattern *p, node **d );
node *adstend_pattern_recurse( pattern *q, node **d, int dlen );
node **copy_decomposition_adstend( node **d, pattern *r, int dlen );
pattern *add_patterns_scratch( pattern *p, pattern *q );

/* core.c */
amal *amalgamate( pattern *P1, pattern *P2 );
node *isom( node *n, pattern *p );
int is_initial_segment( node *n, pattern *p );
void clean_scratch_workspace(void);
ao_detail *create_details( pattern *P1, pattern *P2, node *Q );
void setup_scratch_workspace(void);
void unsetup_scratch_workspace(void);

/* arith.c */
int is_epsilon( node *n );
node **get_reach( node *n );
node *get_node_by_decomposition( pattern *p, node **d );
int init_additive_one( void );
int init_additive_omega( void );
pattern *mult( node *x, node *y );
pattern *logomega( node *n );
int compare_decompositions( node **x, node **y );
node *next_with_minreach_destructive( node *start, node **after );
node **get_minreach( node *n );
pattern *node_mult( node *x, node **y );
node **translate_minreach( node **reach, node **map );
pattern *mult_patterns_assuming_scratch_workspace( pattern *p, pattern *q );
pattern *omexp( pattern *p );
pattern *omlog( pattern *p );
pattern *omind( pattern *p );
pattern *omexp_decomp( node **d );

/* simp.c */
pattern *simplify( pattern *p );
int same_point( pattern *p, pattern *q );

#ifdef PATTERNS_DATABASE
/* db.c */
void save_pattern(pattern *p);
#endif

/*
 * Some functions also defined in core.h
 */


/*
 * Global variables
 */
extern pattern *pure_zero;
extern pattern *additive_zero;
extern pattern pattern_too_large_struct;
extern pattern *first_pattern;
extern pattern *last_pattern;
extern ao_record *first_ao_record;
extern ao_record *last_ao_record;
extern ao_detail *first_detail;
extern ao_detail *last_detail;
extern pattern *additive_one;
extern pattern *additive_omega;
extern char *global_pattern_name_overwrite;
extern int global_showwork;



#endif  // closes the #ifdef POR_H_INCLUDED
