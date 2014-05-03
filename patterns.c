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
 * patterns.c                                                                          *
 ***************************************************************************************
 * Basic commands for manipulating patterns and accessing the main algorithms of the   *
 * library.                                                                            *
 *                                                                                     *
 * If the user so chooses, she may treat all other files in the library as black boxes *
 * and only use interact with them via these functions.                                *
 *                                                                                     *
 * Note: The functions in this file amount to a very bare-bones UI for the library.    *
 * The actual Patterns of Resemblance Calculator uses much more sophisticated,         *
 * web-ready versions of these functions, not published here.                          *
 **************************************************************************************/

#include "patterns.h"
#include "por.h"
#include "core.h"

char global_pattern_error[PATTERN_ERROR_BUFSIZE];

/*
 * Create a pattern with specified number of nodes.
 * The nodes are initially indecomposable and there
 * are no circles (that is, the less1 relation is
 * trivial).
 *
 * Starting with this blank pattern, more interesting
 * patterns can be created by directly altering the
 * fields in the pattern structure.  See example.c
 * for examples.  Note that if a pattern structure is
 * altered to not actually satisfy the axioms of a
 * pattern of resemblance, then most functions which
 * expect a pattern as input may exhibit undefined
 * behavior.
 */
pattern *new_pattern( int nodes )
{
  pattern *p;
  int i;

  if ( !nodes )
    PTN_ERROR( "A pattern must have at least one node." );

  if ( nodes < 0 )
    PTN_ERROR( "A pattern cannot have a negative number of nodes." );

  p = copy_pattern( additive_zero );

  for ( i = 1; i < nodes; i++ )
    insert_node_before( NULL, p );

  p->nodes = nodes;

  p = eliminate_duplicate_pattern(p);

  if ( p == pattern_too_large )
    PTN_ERRORF( "Pattern size is limited to %d nodes.", MAX_NODES_PER_PATTERN_UPPER );

  return p;
}

/*
 * If p denotes ordinal alpha and q denotes ordinal beta,
 * calculate a pattern that denotes ordinal alpha+beta.
 */
pattern *pattern_sum( pattern *p, pattern *q )
{
  pattern *result;

  /*
   * If either pattern notates 0, then the sum is the
   * other pattern.
   */
  if ( p->point == p->first_node )
    return q;
  if ( q->point == q->first_node )
    return p;

  /*
   * Otherwise, the calculation will be a bit more involved.
   * We'll need to do a bunch of computations, so we'll
   * work on scratchpaper.  (To simplify garbage collection)
   */
  setup_scratch_workspace();
  result = add_patterns_scratch(copy_pattern(p),copy_pattern(q));
  unsetup_scratch_workspace();

  /*
   * Result is still in scratch space.  Clean it up and
   * store it in non-scratch space.
   */
  result = copy_pattern( result );
  fix_node_names(result);

  clean_scratch_workspace();

  return eliminate_duplicate_pattern(result);
}

/*
 * If pattern p notates ordinal alpha, and pattern q
 * notates ordinal beta, calculate a pattern that
 * notates the product alpha*beta.
 */
pattern *pattern_product( pattern *p, pattern *q )
{
  pattern *result;

  /*
   * If either pattern notates zero, then the
   * answer is zero.
   */
  if ( p->point == p->first_node
  ||   q->point == q->first_node )
    return additive_zero;

  /*
   * Otherwise, do the complicated calculations on
   * disposable scratch paper.
   */
  setup_scratch_workspace();
  result = mult_patterns_assuming_scratch_workspace( p, q );
  unsetup_scratch_workspace();

  /*
   * Copy the result from the scratch paper, and
   * clean it up.
   */
  result = copy_pattern(result);
  fix_node_names(result);

  clean_scratch_workspace();

  return eliminate_duplicate_pattern(result);
}

/*
 * If pattern p notates ordinal alpha, compute
 * a pattern that notates ordinal omega^alpha.
 */
pattern *pattern_exponential( pattern *p )
{
  pattern *result;

  /*
   * The computation may be complicated,
   * so we do it on scratchpaper.
   */
  setup_scratch_workspace();
  result = omexp( copy_pattern(p) );
  unsetup_scratch_workspace();

  /*
   * Copy the result from scratch, clean it up.
   */
  result = copy_pattern(result);
  fix_node_names(result);

  clean_scratch_workspace();

  return eliminate_duplicate_pattern(result);
}

/*
 * If pattern p notates ordinal omega^alpha,
 * compute a pattern that notates alpha.
 * Otherwise, output NULL.
 */
pattern *pattern_logarithm( pattern *p )
{
  pattern *result;

  if ( !p->point->position )
    PTN_ERROR( "The logarithm of 0 is not defined." );

  if ( p->point->decomposition )
    PTN_ERROR( "The logarithm of a decomposable ordinal is not defined." );

  /*
   * Do the calculations on scratch paper.
   */
  setup_scratch_workspace();
  result = omlog( copy_pattern(p) );
  unsetup_scratch_workspace();

  /*
   * Copy the result from scratch and clean it up.
   */
  result = copy_pattern(result);
  fix_node_names(result);

  clean_scratch_workspace();

  return eliminate_duplicate_pattern(result);
}

/*
 * Compare patterns p and q.
 * Returns 1 if p denotes a bigger ordinal than q.
 * Returns 0 if p and q denote the same ordinal.
 * Returns -1 if p denotes a smaller ordinal than q.
 */
int pattern_compare( pattern *p, pattern *q )
{
  amal *a;
  int result;

  /*
   * Strategy: Amalgamate the patterns into one single pattern,
   *  compare their designated points in the amalgamation.
   *
   * Amalgamation is complicated so we do it on scratchpaper.
   */
  setup_scratch_workspace();
  a = amalgamate( copy_pattern(p), copy_pattern(q) );
  unsetup_scratch_workspace();

  /*
   * Compare the designated points of p and q within the amalgamation.
   * We have to do this before calling "clean_scratch_workspace();" because
   * the amalgamation lives in scratch workspace.
   */
  if ( a->p1_in_p->position > a->p2_in_p->position )
    result = 1;
  else if ( a->p1_in_p->position == a->p2_in_p->position )
    result = 0;
  else
    result = -1;

  clean_scratch_workspace();

  return result;
}

/*
 * If pattern p notates ordinal alpha, compute
 * the simplest pattern that notates alpha.
 */
pattern *pattern_simplify( pattern *p )
{
  pattern *result;

  /*
   * Do the work on scratchpaper.
   */
  setup_scratch_workspace();
  result = simplify( copy_pattern(p) );
  unsetup_scratch_workspace();

  /*
   * Copy the result from scratch and clean it up.
   */
  result = copy_pattern(result);
  fix_node_names(result);

  clean_scratch_workspace();

  return eliminate_duplicate_pattern(result);
}

/*
 * Compute the amalgamation of patterns p and q
 * (Lemma 7.12 from Carlson2001).
 */
pattern *pattern_amalgamate( pattern *p, pattern *q )
{
  amal *a;
  pattern *result;

  /*
   * Do the work on scratchpaper
   */
  setup_scratch_workspace();
  a = amalgamate( copy_pattern(p), copy_pattern(q) );
  unsetup_scratch_workspace();

  /*
   * Copy the result from the scratchpaper, clean it up
   */
  result = copy_pattern( a->p );
  fix_node_names( result );

  clean_scratch_workspace();

  return eliminate_duplicate_pattern( result );
}


/*
 * Create a duplicate of a pattern.
 * (Usually for the sake of altering the duplicate
 *  without altering the original.)
 *
 * Note: If p was generated in scratch space, and
 * we have now unsetup'd scratch space, and we have
 * not yet called clean_scratch_workspace();, then
 * the copy created by copy_pattern will live in normal
 * space.  Similarly, if copy_pattern is called on a
 * normal-space pattern while working in scratch workspace,
 * the copy will live in scratch workspace.
 */
pattern *copy_pattern( pattern *p )
{
  pattern *q;
  node *m, *n, **dm, **dn;

  CREATE( q, pattern, 1 );
  q->first_node = NULL;
  q->last_node = NULL;
  q->nodes = p->nodes;
  q->type = p->type;
  q->id = get_new_pattern_id();
  LINK( q, first_pattern, last_pattern, next, prev );

  for ( n = p->first_node; n; n = n->next )
  {
    CREATE( m, node, 1 );
    m->p = q;
    if ( n->id )
    {
      /*
       * Node IDs come from a central table, so no need
       * to duplicate the memory for them.
       */
      m->id = n->id;
    }
    else
      m->id = NULL;
    m->position = n->position;
    m->isnatural = n->isnatural;
    m->natural = n->natural;
    if ( n->decomposition )
    {
      CREATE( m->decomposition, node *, decomposition_length( n->decomposition ) + 1 );
      for ( dm = m->decomposition, dn = n->decomposition; *dn; dn++ )
        *dm++ = get_node_by_position( q, (*dn)->position );
      *dm = NULL;
    }
    LINK( m, q->first_node, q->last_node, next, prev );
  }
  for ( n = p->first_node, m=q->first_node; n; n=n->next, m=m->next )
  {
    if ( n->less1 == n )
      m->less1 = m;
    else
      m->less1 = get_node_by_position( q, n->less1->position );
  }

  q->point = get_node_by_position( q, p->point->position );

  return q;
}

/*
 * Initialize the basic patterns (0, 1, and omega)
 */
void patterns_initialize( void )
{
  init_zero_patterns();
  init_additive_one();
  init_additive_omega();

  global_pattern_error[0] = '\0';
}
