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
 * patterns.h                                                                          *
 ***************************************************************************************
 * Miscellaneous pattern manipulations that don't go anywhere else.                    *
 **************************************************************************************/

#include "patterns.h"
#include "por.h"
#include "core.h"
#include <stdlib.h>

/*
 * Global variables
 */
pattern *first_pattern;
pattern *last_pattern;
pattern *pure_zero;
pattern *additive_zero;
ao_detail *first_detail;
ao_detail *last_detail;

pattern pattern_too_large_struct;
pattern *pattern_too_large = &pattern_too_large_struct;

char *global_pattern_name_overwrite;

/*
 * Functions
 */

/*
 * Get a new pattern id, to be assigned to a newly created pattern
 */
char *get_new_pattern_id(void)
{
  char *x, *y, *z, *p;
  int lastlen;

  /*
   * If this is the first pattern to ever be created, give it ID "aa"
   */
  if ( !last_pattern )
  {
    CREATE( x, char, 3 );
    sprintf( x, "aa" );

    return x;
  }

  /*
   * If this is not the first pattern, then look at the most recent pattern ID
   * and increment it appropriately (increment the rightmost char, rolling that
   * over from 'z' back to 'a' and incrementing the next rightmost char, etc.,
   * and increasing the length if the last ID was a string of z's)
   */
  lastlen = strlen(last_pattern->id);

  /*
   * Search for the rightmost non-'z' entry in the last ID
   */
  for ( y = &last_pattern->id[lastlen-1]; y >= last_pattern->id; y-- )
    if ( *y != 'z' )
      break;

  /*
   * If none was found, return a one-longer string of a's
   */
  if ( y < last_pattern->id )
  {
    CREATE( x, char, lastlen + 2 );
    y = &x[lastlen+1];
    *y-- = '\0';
    for ( ; y >= x; y-- )
      *y = 'a';
    return x;
  }

  /*
   * If a rightmost non-'z' was found, copy everything before it, followed
   * by it plus 1, followed by a bunch of a's
   */
  {
    CREATE( x, char, lastlen + 1 );
    for ( p=x, z=last_pattern->id; z < y; z++ )
      *p++ = *z;

    *p = *y + 1;

    {
      /*
       * Footnote: Avoid having "in" or "add" as IDs...
       */
      if ( p == &x[1] && *p == 'n' && *x == 'i' )
        *p = 'o';
      else if ( p == &x[2] && *p == 'd' && *x == 'a' && x[1] == 'd' )
        *p = 'e';
    }

    p++;

    while ( p < &x[lastlen] )
      *p++ = 'a';
  }

  *p = '\0';

  return x;
}

/*
 * Given a node id, "prev", generate the next node id.
 * This function will be used to generate a big table
 * of node IDs, so that node IDs don't have to be
 * recomputed every time a new pattern is created.
 */
char *next_node_id( char *prev )
{
  int len = strlen(prev);
  char *x;
  char *buf;
  int pos;

  /*
   * In the previous node ID, search for a rightmost non-'z' character.
   */
  for ( x = &prev[len-1], pos=len-1; x >= prev; x--, pos-- )
    if ( *x != 'z' )
      break;

  /*
   * If we found a rightmost non-'z' character in the previous ID,
   * copy the previous ID, increment the rightmost non-'z', and
   * replacing everything to the right with a's
   */
  if ( x >= prev )
  {
    CREATE( buf, char, len+1 );
    sprintf( buf, "%s", prev );
    buf[pos]++;
    for ( x = &buf[pos+1]; *x; x++ )
      *x = 'a';
    return buf;
  }

  /*
   * If the previous node was all z's, create a one-longer string of a's
   */
  CREATE( buf, char, len+2 );
  buf[len+1] = '\0';
  for ( x = &buf[len]; x >= buf; x-- )
    *x = 'a';
  return buf;
}

/*
 * Assign an ID to a node in a pattern.
 * Intended to be called on the pattern's nodes one-by-one,
 * from left to right, as the nodes are added to the
 * pattern.
 */
char *assign_node_id( node *n, pattern *p )
{
  static char **cache;

  /*
   * If this is the first time the function has been called,
   * generate a table of node IDs.
   */
  if ( !cache )
  {
    int i;

    CREATE( cache, char *, MAX_NODES_PER_PATTERN_UPPER );
    *cache = strdup( "a" );
    for ( i = 1; i < MAX_NODES_PER_PATTERN_UPPER; i++ )
      cache[i] = next_node_id( cache[i-1] );
  }

  /*
   * Read the ID from the table
   */
  return cache[p->nodes-1];
}

/*
 * After creating a pattern, check whether an identical
 * pattern already exists in our linked list of persistent
 * patterns.  If so, discard the new pattern and return a
 * link to the already existing copy.
 *
 * May also kill the input pattern and return the global
 * pointer "pattern_too_large" to indicate what the name says.
 *
 * This function is more important than it may at first seem.
 * As the unique gateway that all new patterns pass through,
 * it is a suitable place to maintain various paperwork.
 *  (Does not apply to temporary patterns created in scratch space,
 *   see core.c)
 * example, this is where the Patterns of Resemblance Calculator
 * at http://www.xamuel.com/patterns writes new patterns to its
 * database.
 */
pattern *eliminate_duplicate_pattern(pattern *p)
{
  pattern *q;

  /*
   * Prevent creation of patterns larger than a hardcoded limit
   */
  if ( p->nodes > MAX_NODES_PER_PATTERN_UPPER )
  {
    UNLINK( p, first_pattern, last_pattern, next, prev );
    kill_pattern(p);
    return pattern_too_large;
  }

  /*
   * Seek a copy of the input pattern, if found then kill the input
   * and return the copy.
   */
  for ( q = first_pattern; q; q = q->next )
  {
    if ( q == p )
      continue;

    if ( same_pattern(p,q) )
    {
       UNLINK( p, first_pattern, last_pattern, next, prev );
       kill_pattern(p);
       return q;
    }
  }

  /*
   * At this point, the patterns of resemblance calculator at http://www.xamuel.com/patterns/ saves the pattern
   * to its database.  The database is not a part of the open source library of pattern arithmetical functions,
   * hence the save_pattern call is commented out.
   */
#ifdef PATTERNS_DATABASE
  save_pattern(p);
#endif

  return p;
}

/*
 * De-allocate memory formerly allocated for a pattern
 */
void kill_pattern(pattern *p)
{
  node *n, *n_next;

  for ( n = p->first_node; n; n = n_next )
  {
    n_next = n->next;
    kill_node(n);
  }

  free(p->id);
  free( p );
}

/*
 * De-allocate memory formerly allocated for a node
 */
void kill_node( node *n )
{
  if ( n->decomposition )
    free( n->decomposition );

  /*
   * Note: n->id is statically allocated (in a table)
   *  and thus should not be freed
   */

  free( n );
}

/*
 * Check whether two patterns are the same
 */
int same_pattern( pattern *p, pattern *q )
{
  node *pn, *qn, **dp, **dq;

  if ( p->nodes != q->nodes )
    return 0;

  if ( p->point->position != q->point->position )
    return 0;

  if ( p->type != q->type )
    return 0;

  /*
   * Check whether the nodes are equal
   */
  for ( pn = p->first_node, qn = q->first_node; pn; pn = pn->next, qn = qn->next )
  {
    if ( (pn->id && !qn->id) || (!pn->id && qn->id) || (pn->id && strcmp(pn->id,qn->id)) )
      return 0;
    if ( pn->less1->position != qn->less1->position )
      return 0;
    if ( pn->natural != qn->natural )
      return 0;
    if ( (pn->decomposition && !qn->decomposition) || (qn->decomposition && !pn->decomposition) )
      return 0;
    if ( pn->decomposition )
    {
      /*
       * If a node and its counterpart are decomposable, search for a
       * difference in their decompositions.
       */
      dp = pn->decomposition;
      dq = qn->decomposition;
      while ( 1 )
      {
        if ( (*dp && !*dq) || (*dq && !*dp) )
          return 0;
        if ( !*dp )
          break;
        if ( (*dp)->position != (*dq)->position )
          return 0;
        dp++;
        dq++;
      }
    }
  }
  return 1;
}

/*
 * Search the linked list of patterns by id
 */
pattern *get_pattern_by_id( char *id )
{
  pattern *p;

  for ( p = first_pattern; p; p = p->next )
    if ( !strcmp( p->id, id ) )
      return p;

  return NULL;
}

/*
 * Within a given pattern, search the linked
 * list of nodes by id
 */
node *get_node_by_id( pattern *p, char *id )
{
  node *n;

  for ( n = p->first_node; n; n = n->next )
    if ( !strcmp( n->id, id ) )
      return n;

  return NULL;
}

int decomposition_length( node **decomposition )
{
  int n;
  node **ptr;

  for ( n = 0, ptr = decomposition; *ptr; ptr++ )
    n++;

  return n;
}

node *get_node_by_position( pattern *p, int pos )
{
  node *n;
  int i;

  for ( i=0, n = p->first_node; n; n = n->next )
  {
    if ( i == pos )
      return n;
    i++;
  }

  return NULL;
}

/*
 * Check whether it is legal to insert a new indecomposable node before node n.
 * Returns NULL if legal, otherwise returns a pointer to a string
 * indicating the reason (in English) why illegal.
 *
 * Supports NULL input, in which case it always reports the insertion
 * is legal (it is always legal to append a new indecomposable node at the end of
 * a pattern).
 */
char *can_insert_node_before( node *n )
{
  node *m;

  if ( n && n->decomposition )
  {
    static char buf[1024];
    sprintf( buf, "That would not be a pattern - node %s would have a decomposition which breaks the lexicographic ordering of nodes.", n->id );
    return buf;
  }

  for ( m = n; m; m = m->next )
  {
    if ( m->isnatural && m->position == m->natural )
    {
      static char buf[1024];
      sprintf( buf, "The required node cannot be inserted, because then node (%s), which is supposed to represent %ld, would have more than %ld nodes before it.", m->id, m->natural, m->natural );
      return buf;
    }
  }
  return NULL;
}

/*
 * Insert a new indecomposable node before node n in pattern p
 * (or append it at the end of p if n=NULL)
 */
node *insert_node_before( node *n, pattern *p )
{
  node *m;

  for ( m = n; m; m = m->next )
    m->position++;

  CREATE( m, node, 1 );

  m->less1 = m;

  m->p = p;

  if ( n )
  {
    if ( p->first_node == n )
      p->first_node = m;
    m->prev = n->prev;
    m->next = n;
    n->prev = m;
    if ( m->prev )
      m->prev->next = m;
    m->position = n->position - 1;
  }
  else
  {
    LINK( m, p->first_node, p->last_node, next, prev );
    m->position = p->nodes;
  }

  m->decomposition = NULL;
  m->isnatural = 0;
  m->natural = 0;
  p->nodes++;

  m->id = assign_node_id( m, p );

  return m;
}

/*
 * Check whether decomposing node n in pattern p into decomposition d, is legal
 * (whether the resulting structure would remain a bona fide pattern).
 * Returns NULL if legal.  Otherwise returns a string explaining (in HTML) why
 * the decomposition would be illegal.
 *
 * Rather technical, so instead of verbose commenting, for now we'll let said
 * error messages speak for themselves.
 */
char *decomposition_inconsistent_with_addition_tree( node **d, node *n, pattern *p )
{
  node *m;
  static char buf[2048];
  int fprev=0;
  int X,Y;

  for ( m = p->first_node; m; m = m->next )
  {
    if ( !m->decomposition )
    {
      if ( m==n )
        continue;
      if ( n->position <= m->position )
        X=1;
      else
        X=0;
      if ( (*d)->position < m->position )
        Y=1;
      else
        Y=0;
      if ( X != Y )
      {
        sprintf( buf, "That would be inconsistent with the decomposition of %s.", m->id );
        return buf;
      }
    }
    else
    {
      if ( n->position <= m->position && !lex_leq( d, m->decomposition ) )
      {
        sprintf( buf, "That would be inconsistent:<br/>Node %s is &gt;= node %s but has a decomposition which is lexicographically smaller than the one you suggested for node %s.", m->id, n->id, n->id );
        return buf;
      }
      if ( n->position > m->position && lex_leq( d, m->decomposition ) )
      {
        sprintf( buf, "That would be inconsistent:<br/>Node %s is &lt; node %s but has a decomposition which is lexicographically &gt;= the one you suggested for %s.", m->id, n->id, n->id );
        return buf;
      }
      if ( !fprev && is_prev_decomposition( m->decomposition, d ) )
        fprev = 1;
    }
  }

  if ( !fprev && d[0] && d[1] && d[2] )
  {
    sprintf( buf, "Before you define a decomposition, you must define the sums of its initial segments.<br/>Eg, before defining a+b+c, you must first define a+b." );
    return buf;
  }

  return NULL;
}

/*
 * Given two NULL-terminated strings of node *'s, check whether the first precedes
 * the second lexicographically (the individual entries being ordered according to
 * their positions in their patterns).
 */
int lex_leq( node **x, node **y )
{
  while(1)
  {
    if ( *x && !*y )
      return 0;
    if ( !*x )
      return 1;
    if ( (*x)->position < (*y)->position )
      return 1;
    if ( (*x)->position > (*y)->position )
      return 0;
    x++;
    y++;
  }
}

/*
 * Check whether "prev" and "next" are such that
 *  prev = x_1 ... x_n
 * and
 *  next = x_1 ... x_{n+1}
 * (In other words, check whether next consists of prev with one extra entry appended)
 */
int is_prev_decomposition( node **prev, node **next )
{
  node **x,**y;

  for ( x=prev, y=next; *x; x++ )
  {
    if ( !*y )
      return 0;

    if ( (*y)->position != (*x)->position )
    {
      return 0;
    }
    y++;
  }

  return *y && !y[1];
}

/*
 * Gloss a decomposition as a string (using the IDs of its nodes)
 */
char *decomposition_to_text( node **d )
{
  static char buf[MAX_NODES_PER_PATTERN_UPPER * 5]; // Would theoretically need resizing if MAX_NODES_PER_PATTERN_UPPER was made very large
  node **x;
  int blen;

  if ( !d )
  {
    *buf = '\0';
    return buf;
  }

  blen = 0;
  *buf ='\0';

  for ( x = d; *x; x++ )
  {
    if ( x[1] )
    {
      sprintf( buf + blen, "%s+", (*x)->id );
      blen += strlen((*x)->id) + 1;
    }
    else
      sprintf( buf + blen, "%s", (*x)->id );
  }
  return buf;
}

/*
 * Initialize patterns to notate the ordinal 0
 * (needed for base cases of various algorithms)
 */
int init_zero_patterns(void)
{
  node *n;
  pattern *p;

  /*
   * First, check to see whether the zero patterns already exist from loading a savefile
   */
  for ( p = first_pattern; p; p = p->next )
  {
    if ( p->nodes == 1 && p->type == PATTERN_ADD )
    {
      additive_zero = p;
      return 0;
    }
  }

  CREATE( additive_zero, pattern, 1 );

  additive_zero->nodes = 1;
  additive_zero->type = PATTERN_ADD;
  additive_zero->id = get_new_pattern_id();
  additive_zero->first_node = NULL;
  additive_zero->last_node = NULL;

  CREATE( n, node, 1 );
  n->p = additive_zero;
  n->decomposition = NULL;
  n->less1 = n;
  n->isnatural = 1;
  n->natural = 0;
  n->position = 0;
  LINK( n, additive_zero->first_node, additive_zero->last_node, next, prev );
  n->id = assign_node_id(n,additive_zero);

  additive_zero->point = n;

  LINK( additive_zero, first_pattern, last_pattern, next, prev );

  return 1;
}

/*
 * Re-assign IDs to the nodes in a pattern
 * (for example, if the nodes have been shuffled, etc)
 */
void fix_node_names(pattern *p)
{
  node *n;

  p->nodes = 0;

  for ( n = p->first_node; n; n = n->next )
  {
    p->nodes++;
    n->id = assign_node_id(n,p);
  }
}

/*
 * Sigma_1-elementary equivalence should be transitive.
 * If x->less1 = y and y->less1 = z, then x->less1 should be
 * equal to z.
 *
 * Returns 0 if p's less1 was already transitive.
 * Returns 1 otherwise.
 */
int transitively_close_less1( pattern *p )
{
  node *n, *m;
  int fmatch=0;

  for ( n = p->first_node; n; n = n->next )
  {
    if ( n->less1 != n )
    {
      for ( m = n->less1; m != n; m = m->prev )
      {
        if ( m->less1->position > n->less1->position )
        {
          fmatch=1;
          n->less1 = m->less1;
        }
      }
    }
  }
  if ( fmatch )
    transitively_close_less1(p);
  return fmatch;
}

/*
 * Add a node with a given decomposition to a given pattern.
 *
 * This is complicated by the following factor.
 * Say we want to add a node with decomposition x_1+x_2+x_3+x_4,
 * but suppose x_1+x_2+x_3 is not defined.  Then first we must
 * add a node x_1+x_2+x_3.  And to do that, we must ensure
 * x_1+x_2 is defined, as well.  We take the obvious recursive
 * approach to this problem.
 */
node *adstend_pattern_recurse( pattern *q, node **d, int dlen )
{
  node *prev_decomp, *bound, *newnode;

  /*
   * If the desired decomposition is longer than length 2, search
   * to see whether the previous (one-smaller) decomposition is
   * already present.
   */
  if ( dlen > 2 )
  {
    for ( prev_decomp = q->first_node; prev_decomp; prev_decomp = prev_decomp->next )
    {
      if ( prev_decomp->decomposition && is_prev_decomposition(prev_decomp->decomposition, d) )
        break;
    }
    /*
     * If the previous decomposition is absent, add it in, recursively.
     */
    if ( !prev_decomp )
    {
      node *tmp;

      tmp = d[dlen-1];
      d[dlen-1]=NULL;
      adstend_pattern_recurse( q, d, dlen-1 );
      d[dlen-1]=tmp;
    }
  }

  /*
   * Search for the correct place to insert the new node.
   * We want to insert it in the correct lexicographic order.
   * Search the pattern for the leftmost mode that comes
   * lexicographically after d.
   */
  for ( bound = q->first_node; bound; bound = bound->next )
  {
    if ( bound->decomposition )
    {
      if ( lex_leq( bound->decomposition, d ) )
        continue;
    }
    else
    {
      if ( bound->position <= (*d)->position )
        continue;
    }
    break;
  }

  /*
   * Insert a new indecomposable node just before bound.
   * (If bound=NULL, meaning d is lexicographically bigger
   *  than everything in the pattern, then insert_node_before
   *  will insert the node at the very end of the pattern.)
   */
  newnode = insert_node_before(bound,q);

  /*
   * Give the new node the desired decomposition
   */
  newnode->decomposition = copy_decomposition_adstend(d,q,dlen);

  return newnode;
}

/*
 * Given a pattern, and a decomposition,
 * create a copy of the pattern, and add a node
 * to the copy, having the given decomposition.
 *
 * Returns pattern_too_large if the resulting pattern
 * would exceed size MAX_NODES_PER_PATTERN_UPPER.
 */
pattern *adstend_pattern( pattern *p, node **d )
{
  pattern *q = copy_pattern(p);
  adstend_pattern_recurse( q, d, decomposition_length(d) );

  return eliminate_duplicate_pattern(q);

}

/*
 * Given a pattern r, and a decomposition d living in a copy of r,
 * form the counterpart of d in r itself.
 */
node **copy_decomposition_adstend( node **d, pattern *r, int dlen )
{
  node **dnew, **x, **dptr;

  CREATE( dnew, node *, dlen + 1 );

  for ( x=d, dptr=dnew; *x; x++ )
    *dptr++ = isom(*x,r);

  *dptr = NULL;

  return dnew;
}

/*
 * Given nodes n and m, form the decomposition of their ordinal sum n+m.
 *
 * For example:
 *  If n and m are indecomposable, the result will just n+m.
 *  If n=x_1+...+x_k, and m is a smaller indecomposable than x_k, the result will be x_1+...+x_k+m.
 *  If n=x_1+...+x_k, and m is a bigger indecomposable than x_k, the result will be m.
 *  If n=x_1+...+x_k, and m=y_1+...+y_s, the result will be x_1+...+x_t+y_1+...+y_s,
 *         where t is maximum such that x_t >= y_1.
 */
node **get_decomposition_of_sum( node *n, node *m )
{
  node **d, **dx, **dy;
  int i;

  if ( !n->decomposition && !m->decomposition )
  {
    CREATE( d, node *, 3 );
    d[0] = n;
    d[1] = m;
    d[2] = NULL;
    return d;
  }

  if ( !n->decomposition )
  {
    CREATE( d, node *, decomposition_length(m->decomposition) + 2 );
    *d = n;
    for ( dx=&d[1],dy=m->decomposition; *dy; dy++ )
      *dx++ = *dy;
    *dx = NULL;
    return d;
  }

  if ( !m->decomposition )
  {
    for ( i=0, dx = n->decomposition; *dx && (*dx)->position >= m->position; dx++ )
      i++;
    CREATE( d, node *, i+2 );
    for ( dx = n->decomposition, dy=d; *dx && (*dx)->position >= m->position; dx++ )
      *dy++ = *dx;
    *dy++ = m;
    *dy = NULL;
    return d;
  }

  for ( i = 0, dx = n->decomposition; *dx && (*dx)->position >= (*m->decomposition)->position; dx++ )
    i++;
  CREATE( d, node *, i + decomposition_length( m->decomposition ) + 1 );
  for ( dy=d,  dx = n->decomposition; *dx && (*dx)->position >= (*m->decomposition)->position; dx++ )
    *dy++ = *dx;
  for ( dx = m->decomposition; *dx; dx++ )
    *dy++ = *dx;
  *dy = NULL;
  return d;
}

/*
 * Check whether two decompositions are the same
 * (up to order isomorphism within their respective patterns)
 */
int same_decompositions( node **d1, node **d2 )
{
  node **dx1, **dx2;

  for ( dx1 = d1, dx2 = d2; *dx1; dx1++ )
  {
    if ( !*dx2 )
      return 0;
    if ( (*dx1)->position != (*dx2)->position )
      return 0;
    dx2++;
  }

  return !*dx2;
}

/*
 * If pattern p denotes ordinal alpha, and pattern q denotes ordinal beta,
 * calculate a pattern denoting alpha+beta.
 *
 * Strategy: amalgamate p and q together, reducing the problem to a simple
 *   problem of adding nodes instead of adding full patterns.
 *
 * Assumes we are working in scratch space (so should only be called
 * on temporary patterns).
 */
pattern *add_patterns_scratch( pattern *p, pattern *q )
{
  amal *a;
  node *n, *n1, *n2, **d, *x;
  pattern *r;

  /*
   * 0 is the additive identity
   */
  if ( !p->point->position )
    return q;
  if ( !q->point->position )
    return p;

  /*
   * Amalgamate p and q into a single pattern.
   * The point of p embeds as a->p1_in p.
   * The point of q embeds as a->p2_in_p.
   */
  a = amalgamate( p, q );

  /*
   * In ordinal addition, if A<B, and if there is an indecomposable
   * ordinal between A and B, then A+B=B.
   */
  if ( a->p1_in_p->position < a->p2_in_p->position )
  {
    for ( n = a->p1_in_p->next; n; n = n->next )
    {
      if ( !n->decomposition )
        return q;
      if ( n == a->p2_in_p )
        break;
    }
  }

  r = a->p;
  n1 = isom( a->p1_in_p, r );
  n2 = isom( a->p2_in_p, r );

  /*
   * Calculate the decomposition of the desired node-sum
   */
  d = get_decomposition_of_sum( n1, n2 );

  /*
   * Check whether the desired decomposition already exists
   * in the amalgamated pattern.  If so, make it the designated
   * point of the amalgamated pattern, and return that pattern.
   */
  for ( x = r->first_node; x; x = x->next )
  {
    if ( x->decomposition && same_decompositions( x->decomposition, d ) )
    {
      r->point = x;
      free(d);
      return r;
    }
  }

  /*
   * If the desired decomposition does not exist, insert it.
   */
  r->point = adstend_pattern_recurse(r,d,decomposition_length(d));

  free(d);

  return r;
}
