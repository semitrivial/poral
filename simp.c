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
 * simp.c                                                                              *
 ***************************************************************************************
 * Implementation of an algorithm to simplify a pattern.                               *
 *                                                                                     *
 * Simplifies a pointed pattern into its normal form, as defined in:                   *
 *  Carlson & Wilken, 2013, "Normal forms for elementary patterns", J. Symb. Logic     *
 *                                                                                     *
 * Programmed mainly May 2--3, 2013.                                                   *
 **************************************************************************************/

#include "patterns.h"
#include "por.h"

/*
 * Local function prototypes
 */
static pattern *simplify_recurse( pattern *p, node *start );
static pattern *remove_end_clumps( pattern *p );
static int mark_for_removal( pattern *p, node *x, node *start );
static pattern *execute_removal(pattern *p);

/*
 * Local definitions
 */

typedef enum
{
  SIMPL_UNCHECKED=0, SIMPL_MARKED=1
} simple_data_types;

/*
 * The simplify function itself is just a wrapper function
 * to do some minor preparation and launch a recursive simplify
 * function that takes an additional argument
 */
pattern *simplify( pattern *p )
{
  if ( !p->first_node->next )
    return p;

  p = remove_end_clumps(p);

  if ( !p->first_node->next )
    return p;

  return simplify_recurse( p, p->first_node->next );
}

/*
 * We simplify the pattern recursively, using node "start" as a
 * "zipper" to zip the pattern up ("start" moves from left to
 * right as the recursion proceeds, and the recusion ends when
 * "start" reaches the end of the pattern).
 *
 * Overall strategy: We "check" whether we can remove "start" without
 * changing what ordinal the pointed pattern notates.  But if we remove
 * "start", we have to remove anything connected to it (via less1,
 * or via decompositions), so we have to ask the same question about
 * all those nodes as well, which in turn requires asking the same
 * question about any node THEY'RE connected to, and so on.
 */
static pattern *simplify_recurse( pattern *p, node *start )
{
  node *n;
  pattern *q;

  /*
   * Mark all nodes in the pattern as being unchecked during this iteration
   */
  for ( n = p->first_node; n; n = n->next )
    n->simplify_data = SIMPL_UNCHECKED;

  /*
   * Under no circumstances would we remove the pattern's designated point
   */
  if ( start == p->point )
  {
    start = start->next;
    if ( !start )
      return p;
  }

  /*
   * Attempt to mark "start" for removal.
   * If the attempt fails (because it would
   * require removing p->point) then move on
   * to the next start.
   */
  if ( ! mark_for_removal(p,start,start) )
  {
    if ( !start->next )
      return p;
    return simplify_recurse( p, start->next );
  }

  /*
   * If "start" was successfully marked for
   * removal, then remove it, along with anything
   * else that was marked as collateral damage.
   * Actually, do all this in a copy q of p.
   */
  q = execute_removal(p);

  /*
   * Check whether the copy q, with "start" removed,
   * still notates the same ordinal that p does.
   * If so, continue trying to further simplify q.
   * If not, revert back to p and increment "start".
   */
  if ( same_point(q,p) )
  {
    start = isom(start,q);

    if ( start )
      return simplify_recurse( q, start );
    else
      return q;
  }
  else
  {
    if ( start->next )
      return simplify_recurse( p, start->next );
    else
      return p;
  }
}

/*
 * Attempt to mark a node x for removal, along with (recursively)
 * all nodes that would also have to be removed if that node were.
 * Returns 0 if the pattern's designated point would have to be
 * removed.  The node *start input keeps track of which node we
 * were originally wanting to remove (before getting lost in the
 * mazes of recursion).
 */
static int mark_for_removal( pattern *p, node *x, node *start )
{
  node *n, **d, *L;

  if ( x == p->point )
    return 0;

  /*
   * Black-magic shortcut:
   *  if the point we're recursively trying to mark is further left
   *  than the original point we care about marking, then marking
   *  x would force us to mark p->point.  Why?  Because if we could
   *  have marked x, then we would have done so already, in simplify_recurse,
   *  before even considering "start".
   */
  if ( x->position < start->position )
    return 0;

  /*
   * If x is the left endpoint of a circle and p->point lies within that
   * circle, then we cannot mark x for removal without marking p->point
   */
  if ( x->position <= p->point->position
  &&   p->point->position <= x->less1->position )
    return 0;

  /*
   * If we've already marked x for removal, there's nothing left to do.
   */
  if ( x->simplify_data == SIMPL_MARKED )
    return 1;

  /*
   * Mark x for removal.
   */
  x->simplify_data = SIMPL_MARKED;

  /*
   * Now recursively mark for removal all things which would have to
   * be removed if we remove x.
   */
  for ( n = x->next; n; n = n->next )
  {
    /*
     * Anything which is a decomposition involving doomed nodes, is doomed.
     */
    if ( n->decomposition )
    {
      for ( d = n->decomposition; *d; d++ )
      {
        if ( (*d)->simplify_data == SIMPL_MARKED )
          break;
      }
      if ( *d )
      {
        if ( !mark_for_removal( p, n, start ) )
          return 0;
      }
      else
      {
        /*
         * Suppose n=x_1+...+x_n (a descending sum of indecomposables), and none
         * of the x_i have been marked for removal.  It will still be necessary
         * to mark n for removal if any of x_1+...+x_(n-i) are marked.
         */
        node *d_bak; // backup of *d
        node *acl; // "arithmetical closure"

        for ( d = n->decomposition; *d; d++ )
        {
          d_bak = *d;
          *d = NULL;
          acl = get_node_by_decomposition( p, n->decomposition );
          *d = d_bak;
          if ( acl == n )
            continue;
          if ( acl->simplify_data == SIMPL_MARKED )
            break;
        }
        if ( *d )
        {
          if ( !mark_for_removal( p, n, start ) )
            return 0;
        }
      }
    }
  }

  /*
   * If x is the left endpoint of a less1-circle, then to remove x,
   * we must remove everything within that circle.
   */
  if ( x->less1 != x )
  {
    for ( n = x->next; n->position <= x->less1->position; n = n->next )
    {
      if ( !mark_for_removal( p, n, start ) )
        return 0;
    }
  }
  else
  {
    /*
     * Otherwise, consider the case whether x is the right endpoint of
     * a less1-circle.  We search for the leftmost (if any) node L such
     * that L is the left-endpoint of a circle whose right endpoint is x.
     */
    for ( L = p->first_node; L; L = L->next )
    {
      if ( L == x )
        break;
      if ( L->less1 == x )
        break;
      if ( L->less1->position < x->position )
        L = L->less1;
    }

    /*
     * If we found a circle with left endpoint L and right endpoint x,
     * we are obliged to remove that circle and everything inside it.
     */
    if ( L && L != x )
    {
      for ( n = L; L->position < x->position; L++ )
      {
        if ( !mark_for_removal( p, n, start ) )
          return 0;
      }
    }
  }

  return 1;
}

/*
 * Having successfully marked some points for removal ("successfully" here
 * means that doing so did not force us to mark p->point), make a copy of
 * the pattern, and remove the marked points from it.
 */
static pattern *execute_removal(pattern *p)
{
  node *n, *m, *m_next;
  pattern *q;
  int i;

  q = copy_pattern(p);

  for ( i=0, n=p->first_node, m=q->first_node; n; n = n->next, m = m_next )
  {
    m_next = m->next;

    if ( n->simplify_data == SIMPL_MARKED )
    {
      UNLINK( m, q->first_node, q->last_node, next, prev );
      kill_node( m );
    }
    else
    {
      /*
       * Maintain a running count of how many nodes we DON'T remove,
       * so we can fix the nodecount after the dust settles.
       */
      i++;
    }
  }

  q->nodes = i;

  for ( i = 0, m = q->first_node; m; m = m->next )
    m->position = i++;

  return q;
}

/*
 * Remove less1-connected-components located to the right of
 * the less1-connected-component containing p->point.
 *
 * Undefined behavior if p is the pattern with only one node.
 */
static pattern *remove_end_clumps( pattern *p )
{
  node *n, *n_next;
  pattern *q;

  /*
   * Search for the first node (if any) that lies further right
   * than every circle containing p->point.
   */
  n = p->first_node->next;

  while ( n->position <= p->point->position )
  {
    n = n->less1->next;
    if ( !n )
      return p;
  }

  /*
   * Having found such a node, n, we make a copy of p,
   * and in the copy, kill everything from n onward.
   */
  q = copy_pattern(p);

  q->nodes = n->position;

  for ( n = isom(n,q); n; n = n_next )
  {
    n_next = n->next;
    UNLINK( n, q->first_node, q->last_node, next, prev );
    kill_node( n );
  }

  return q;
}

/*
 * Check whether pointed patterns p and q notate the same ordinal.
 * Assumes working in scratch-space (see core.c)
 */
int same_point( pattern *p, pattern *q )
{
  amal *a = amalgamate( copy_pattern(p), copy_pattern(q) );

  return ( a->p1_in_p->position == a->p2_in_p->position );
}
