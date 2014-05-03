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
 * core.h                                                                              *
 ***************************************************************************************
 * Header file for the implementation of the amalgamation algorithm in Lemma 7.12 of:  *
 * T.J. Carlson, 2001, "Elementary patterns of resemblance", Ann. Pure Appl. Logic     *
 **************************************************************************************/

#ifndef CORE_H_INCLUDED
#define CORE_H_INCLUDED

/*
 * Typedefs
 */
typedef struct AMAL_OVER amal_over;
typedef struct MAPPING mapping;
typedef struct DECOMP_SHELL decomp_shell;

/*
 * Data structure for an amalgamation P of two patterns P1,P2 over pattern Q.
 * (Q is represented as the interval from 0 to node *over in either P1 or P2.)
 * Besides including the amalgamation pattern itself, the data structure also
 * includes maps embedding P1 and P2 into that amalgamation pattern.
 *
 * Also includes some unimportant paperwork fields for storing data about how
 * the amalgamation was computed.
 */
struct AMAL_OVER
{
  amal_over *next;
  amal_over *prev;
  node *over;
  pattern *p;
  pattern *p1;
  pattern *p2;
  node **map1;
  node **map2;
  char *created;
  int swaps;
  int killed;
};

/*
 * Wrapper data structure intended to surround an embedding of a pattern
 * P into a pattern Ptilde.
 */
struct MAPPING
{
  mapping *next;
  mapping *prev;
  pattern *P;
  pattern *Ptilde;
  node **map;
};

/*
 * Wrapper data structure intended to surround a NULL-terminated string
 * of node *'s (for example, a "decomposition" of a decomposable ordinal
 * into a sum of indecomposable ordinals).
 */
struct DECOMP_SHELL
{
  decomp_shell *next;
  decomp_shell *prev;
  node **d;
};

/*
 * Global variables
 */
extern decomp_shell *first_decomp_shell;
extern decomp_shell *last_decomp_shell;

/*
 * Function prototypes for functions in core.c
 */
amal_over *amalgamate_over_Q( pattern *P1, pattern *P2, node *Q, int depth );
pattern *copy_initial_segment( pattern *P, node *b );
node *copy_interval( pattern *dest, node *start, node *end, node **tailptr );
node **compose_maps( pattern *start, pattern *mid, pattern *end, node **map1, node **map2 );
mapping *lemma711( pattern *P, pattern *Q, node **bintoQ );
mapping *lemma711_wrapper( pattern *P, pattern *Q, node **bintoQ );
node **copy_map( node **map );
node **identity_map( pattern *p );
node **isom_map( pattern *p, pattern *q );
node **isom_change_last_point( pattern *p, pattern *q, node *newlast );
node **isom_avoid_one_point( pattern *p, pattern *q, node *avoid );
node **ignore_new_interval( node **oldmap, pattern *newptn, node *left, node *right );
pattern *additively_extend_specialcase( pattern *p, node **decomp, node **newnode );
pattern *reflect_specialcase( pattern *p, node *start, node *end, node *below, node ***map );
void kill_mapping( mapping *m );
void kill_amal( amal *a );
void kill_amal_over( amal_over *ao );
void kill_ao_record( ao_record *rec );

/*
 * Function prototypes for functions in arith.c
 */
decomp_shell *dshell_one_node( node *n );
decomp_shell *copy_decomp_to_shell( node **d );

#define SHOW_WORK_BUF_SIZE 256

#endif // End of #ifdef CORE_H_INCLUDED
