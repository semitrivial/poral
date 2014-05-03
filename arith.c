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
 * arith.c                                                                             *
 ***************************************************************************************
 * Multiplication, exponentiation, and logarithm algorithms for patterns.              *
 * These algorithms are in the paper:                                                  *
 * Samuel Alexander, 2013, "Arithmetical algorithms for elementary patterns" (preprint)*
 **************************************************************************************/

#include "patterns.h"
#include "por.h"
#include "core.h"

/*
 * Global variables
 */
pattern *additive_one;
pattern *additive_omega;
decomp_shell *first_decomp_shell;
decomp_shell *last_decomp_shell;

pattern log_unimplemented_struct;
pattern *log_unimplemented = &log_unimplemented_struct;

/*
 * Check whether a node notates an epsilon number.
 *
 * A nonzero node x notates an epsilon number iff x less1 x+x.
 * Since less1 is a forest respecting <, and since the "less1"
 * field of the pattern data structure points to the maximum thing
 * the node is less1 than, it follows that x notates an epsilon
 * number iff x->less1 is lexicographically >= x+x.
 */
int is_epsilon( node *n )
{
  /*
   * If n is decomposable, then it isn't less1 anything but itself,
   * and certainly isn't an epsilon number.
   */
  if ( n->decomposition )
    return 0;

  /*
   * Zero is not an epsilon number.
   */
  if ( n->position == 0 )
    return 0;

  /*
   * The rest of the function is a matter of checking whether n->less1
   * comes after n+n lexicographically.
   */
  if ( n->less1 == n )
    return 0;

  if ( !n->less1->decomposition )
    return 1;

  if ( n->less1->decomposition[0]->position < n->position )
    return 0;

  if ( n->less1->decomposition[0] == n && n->less1->decomposition[1]->position < n->position )
    return 0;

  return 1;
}

/*
 * Return an array of nodes representing a descending sum x_1+...+x_n of
 * indecomposables, such that n->less1 = n + x_1+...+x_n.
 *
 * In addition to returning the array, we also wrap the array in a
 * shell data structure (mainly so we can automate the garbage collection
 * associated with the arithmetical algorithms).
 */
node **get_reach( node *n )
{
  if ( n->less1 == n )
    return dshell_one_node(n->p->first_node)->d;

  if ( !n->less1->decomposition )
    return dshell_one_node(n->less1)->d;

  /*
   * Suppose n->less1 is a sum y_1+...+y_k.  Then there are two
   * possibilities.
   *
   * If y_1 is not n, then y_1 must be >n (by
   * lexicographical considerations), and thus
   * n->less1 = n + y_1+...+y_k and we want x_1+...+x_n=y_1+...+y_k.
   *
   * If y_1 is n, then n->less1 = n + y_2+...+y_k
   * and we want x_1+...+x_n=y_2+...+y_k.
   */
  if ( n->less1->decomposition[0] != n )
    return copy_decomp_to_shell(n->less1->decomposition)->d;

  if ( !n->less1->decomposition[2] )
    return dshell_one_node(n->less1->decomposition[1])->d;

  return copy_decomp_to_shell( n->less1->decomposition + 1 )->d;
}

/*
 * Get a node in a given pattern with a given decomposition.
 * Returns NULL if no such node exists.
 */
node *get_node_by_decomposition( pattern *p, node **d )
{
  node *n;

  if ( !d[1] )
    return d[0];

  for ( n = p->first_node; n; n = n->next )
  {
    if ( !n->decomposition )
      continue;
    if ( same_decompositions( n->decomposition, d ) )
      return n;
  }
  return NULL;
}

/*
 * Initialize a pattern representing omega (needed for certain
 * base cases in the exponentiation algorithm).
 *
 * This function is called as part of the initialization
 * routines when the whole program is run.
 *
 * Returns 1 if it creates a new additive_omega.  Returns 0 if
 * it manages to find a suitable additive_omega already in
 * memory.
 */
int init_additive_omega( void )
{
  pattern *omega;
  node *n;
  int i;

  /*
   * First search to see whether omega already exists.
   * For most users of the library, this search is unncessary
   * as it will never find a match.  The reason it is here is
   * for the official Online Patterns of Resemblance Ordinal Calculator.
   * The Calculator stores a database of patterns which persist
   * even over server crashes and reboots.  These are loaded
   * prior to init_additive_omega being called, hence the necessity
   * of the search here.
   */
  for ( omega = first_pattern; omega; omega = omega->next )
  {
    if ( omega->nodes == 3
    &&   !omega->last_node->decomposition
    &&   !omega->last_node->prev->decomposition
    &&   omega->last_node->prev->less1 == omega->last_node->prev
    &&   omega->point == omega->last_node )
    {
      additive_omega = omega;
      return 0;
    }
  }

  /*
   * By this point, omega does not already exist in memory.
   * Create it.
   */
  CREATE( omega, pattern, 1 );
  omega->nodes = 3;
  omega->type = PATTERN_ADDITIVE;
  omega->id = get_new_pattern_id();
  omega->first_node = NULL;
  omega->last_node = NULL;

  CREATE( n, node, 1 );
  n->p = omega;
  n->decomposition = NULL;
  n->less1 = n;
  n->isnatural = 1;
  n->natural = 0;
  n->position = 0;
  LINK( n, omega->first_node, omega->last_node, next, prev );

  n->id = assign_node_id(n,omega);

  for ( i = 1; i <= 2; i++ )
  {
    CREATE( n, node, 1 );
    n->p = omega;
    n->decomposition = NULL;
    n->less1 = n;
    n->isnatural = 0;
    n->natural = 0;
    /*
     * Bug fix: next line was erroneously n->position = 1;
     */
    n->position = i;
    LINK( n, omega->first_node, omega->last_node, next, prev );
    n->id = assign_node_id(n,omega);
  }

  omega->point = omega->last_node;
  LINK( omega, first_pattern, last_pattern, next, prev );
  additive_omega = omega;
  return 1;
}

/*
 * Initialize a pattern notating the ordinal 1.
 * Needed in base cases of various arithmetical algorithms.
 * This function is similar to init_additive_omega, and the
 * comments there apply here as well.
 */
int init_additive_one( void )
{
  pattern *one;
  node *n;

  /*
   * Search to see if a suitable pattern already exists.
   */
  for ( one = first_pattern; one; one = one->next )
  {
    if ( one->nodes == 2 && !one->last_node->decomposition && one->point == one->last_node )
    {
        additive_one = one;
        return 0;
    }
  }

  /*
   * Assuming a suitable pattern does not already exist, create one.
   */
  CREATE( one, pattern, 1 );
  one->nodes = 2;
  one->type = PATTERN_ADDITIVE;
  one->id = get_new_pattern_id();
  one->first_node = NULL;
  one->last_node = NULL;

  CREATE( n, node, 1 );
  n->p = one;
  n->decomposition = NULL;
  n->less1 = n;
  n->isnatural = 1;
  n->natural = 0;
  n->position = 0;
  LINK( n, one->first_node, one->last_node, next, prev );
  n->id = assign_node_id(n,one);

  CREATE( n, node, 1 );
  n->p = one;
  n->decomposition = NULL;
  n->less1 = n;
  n->isnatural = 0;
  n->natural = 0;
  n->position = 1;
  LINK( n, one->first_node, one->last_node, next, prev );
  n->id = assign_node_id(n,one);

  one->point = n;
  LINK( one, first_pattern, last_pattern, next, prev );

  additive_one = one;

  return 1;
}

/*
 * Compare two decompositions.  (A decomposition is a NULL-terminated "string",
 * except that instead of being an array of char's, it is an array of node *'s.)
 *
 * Returns -1 if x is lexicographically bigger, 1 if y is, 0 if x=y.
 */
int compare_decompositions( node **x, node **y )
{
  node **xptr, **yptr;

  for ( xptr = x, yptr = y; ;)
  {
    if ( !*xptr && !*yptr )
      return 0;
    if ( !*xptr )
      return 1;
    if ( !*yptr )
      return -1;
    if ( (*xptr)->position > (*yptr)->position )
      return -1;
    if ( (*xptr)->position < (*yptr)->position )
      return 1;
    xptr++;
    yptr++;
  }
}

/*
 * Multiply two pointed patterns.
 */
pattern *mult( node *x, node *y )
{
  if ( y->decomposition )
    return node_mult( x, y->decomposition );
  else
    return node_mult( x, dshell_one_node(y)->d );
}

/*
 * Create a shell data-structure to hold a length-1 decomposition.
 */
decomp_shell *dshell_one_node( node *n )
{
  decomp_shell *d;

  CREATE( d, decomp_shell, 1 );
  CREATE( d->d, node *, 2 );
  d->d[0] = n;
  d->d[1] = NULL;
  LINK( d, first_decomp_shell, last_decomp_shell, next, prev );
  return d;
}

/*
 * Create a shell data-structure to hold a decomposition.
 */
decomp_shell *copy_decomp_to_shell( node **d )
{
  decomp_shell *buf;
  node **ptr, **bptr;

  CREATE( buf, decomp_shell, 1 );
  CREATE( buf->d, node *, decomposition_length(d) + 1 );
  for ( ptr = d, bptr = buf->d; *ptr; ptr++ )
    *bptr++ = *ptr;
  *bptr = NULL;
  LINK( buf, first_decomp_shell, last_decomp_shell, next, prev );
  return buf;
}

/*
 * Multiply a node x by a descending sum y_1+...+y_k of indecomposables
 * (the descending sum being stored as a NULL-terminated string of node *'s)
 */
pattern *node_mult( node *x, node **y )
{
  node *left, *right, *one, *end;
  pattern *p,*q;
  node **map;
  node *ptr;
  node **minreach, **minreach_q;

  if ( !x->position )
    return additive_zero;

  /*
   * If y is decomposable, say y=y_1+...+y_k where k>1, then compute the
   * product recursively, using the distributive law
   */
  if ( y[1] )
  {
    pattern *summand1;
    pattern *summand2;
    node **y1;
    y1 = copy_decomp_to_shell( y+1 )->d;
    summand1 = node_mult( x, dshell_one_node( y[0] )->d ) ;
    summand2 = node_mult( x, y1 );
    return add_patterns_scratch( summand1, summand2 );
  }

  if ( !(y[0]->position) )
    return additive_zero;

  p = x->p;

  if ( !p->first_node->next )
    return additive_zero;

  /*
   * We need p to contain a node denoting the ordinal 1.
   * If it does not, we make a copy of p and insert such a node in it.
   */
  if ( p->first_node->next->less1 == p->first_node->next )
  {
    one = p->first_node->next;
    end = y[0];
  }
  else
  {
    node *nextnode;
    p = copy_pattern(p);
    x = isom(x,p);
    end = isom(y[0],p);
    for ( one = p->first_node->next; one; one = one->next )
      one->position++;
    CREATE( one, node, 1 );
    one->p = p;
    one->id = NULL;
    one->position = 1;
    one->decomposition = NULL;
    one->less1 = one;
    one->natural = 0;
    one->isnatural = 0;
    nextnode = p->first_node->next;
    INSERT( one, nextnode, p->first_node, next, prev );
    p->nodes++;
  }

  /*
   * We will now proceed as in the Node Multiplication Algorithm described in
   * "Arithmetical algorithms for elementary patterns"
   */
  q = copy_pattern(p);
  left = one;
  right = isom(x,q);

  /*
   * We will need a mapping from the original pattern into our copy q, so that as we
   * throw new things into q, we can still keep track of which nodes correspond to the
   * original nodes from p.  (This is implicit in the arithmetical algorithms paper.)
   */
  CREATE( map, node *, p->nodes );
  for ( ptr = p->first_node; ptr; ptr = ptr->next )
    map[ptr->position] = isom(ptr,q);

  /*
   * The main loop of the Node Multiplication Algorithm
   */
  while ( left->position < end->position )
  {
    do
    {
      left = left->next;
    }
    while (left->decomposition);  /* Note: left can't become NULL here because it has to reach end first */

    minreach = get_minreach( left );
    minreach_q = translate_minreach( minreach, map );

    right = next_with_minreach_destructive( right, minreach_q );
    free( minreach_q );
  }

  q->point = right;

  free(map);

  return q;
}

/*
 * translate_minreach:
 *
 * Suppose we start with a pattern p, make a copy q, and then insert various
 * additional nodes into q.  But as we insert new things in q, we maintain
 * a map from p to q so we can still tell which nodes are originally from p.
 * Given such a map, and given a sequence x_1,...,x_n of indecomposables
 * in the original p (call this sum "reach"), translate_minreach returns
 * the sequence x'_1,...,x'_n of nodes in q corresponding to x_1,...,x_n.
 */
node **translate_minreach( node **reach, node **map )
{
  node **d, **dptr, **rptr;

  CREATE( d, node *, decomposition_length( reach ) + 1 );

  for ( rptr = reach, dptr = d; *rptr; rptr++ )
    *dptr++ = map[(*rptr)->position];
  *dptr = NULL;

  return d;
}

/*
 * get_minreach:
 *
 * Given node n, return a descending sequence x_1,...,x_k of indecomposables in n's
 * pattern, such that either:
 *  1. n->less1 = n+x_1+...+x_n and x_1+...+x_k < n; or
 *  2. {x_1,...,x_k} is just the singleton {n}, and n->less1 >= n+n.
 *
 * Furthermore, return the sequence wrapped up in shell structure to facilitate paperwork.
 *
 * See "Arithmetical algorithms for elementary patterns" for details why minreach
 * is so important in ordinal arithmetic.
 */
node **get_minreach( node *n )
{
  if ( n->decomposition || n->less1 == n )
    return dshell_one_node( n->p->first_node )->d;

  if ( !n->less1->decomposition )
    return dshell_one_node( n )->d;

  if ( n->less1->decomposition[0]->position > n->position )
    return dshell_one_node( n )->d;

  if ( n->less1->decomposition[0]->position == n->position && n->less1->decomposition[1]->position >= n->position )
    return dshell_one_node( n )->d;

  return get_reach(n);
}

/*
 * Given a node "after", say in pattern p, and given a descending sum x_1+...+x_n of
 * indecomposables in p, call the sum "reach", return the next node m in p, after "after",
 * such that minreach(m)=x_1+...+x_n and such that for all after<m'<m, minreach(m')<x_1+...+x_n.
 *
 * If there is no such node m in p, then insert such an m, and insert it in the correct place.
 * (See: Minreach Insertion, in "Arithmetical algorithms for elementary patterns".
 *  In the context of that paper, this is one of the most important functions in arith.c)
 *
 * This function might alter the pattern p, hence the "destructive".  It should only be called
 * on temporary scratch-work patterns.
 */
node *next_with_minreach_destructive( node *after, node **reach )
{
  pattern *p = after->p;
  node *n, **d, **rptr, **dptr, **candidate_reach, *nptr;
  node *candidate;
  int cmp;

  /*
   * We'll search for the node we want, starting with the very next node after "after".
   */
  candidate = after;

  while(1)
  {
    /*
     * We won't consider decomposable nodes, as those have trivial reach, so skip
     * any decomposable candidates.  Also skip the current candidate (either it is
     * "after", in which case it's not what we want, or else we're going through the
     * while(1) loop again, in which case the current candidate has already been
     * ruled out in the previous iteration).
     */
    do
    {
      candidate = candidate->next;
    }
    while ( candidate && candidate->decomposition );

    /*
     * If we've run out of candidate nodes without a match, then we're going to have
     * to insert the desired node into p, at the very end of p.
     */
    if ( !candidate )
    {
      CREATE( n, node, 1 );
      n->p = p;
      n->id = NULL;
      n->position = p->last_node->position + 1;
      n->decomposition = NULL;
      n->less1 = n;
      n->natural = 0;
      n->isnatural = 0;
      LINK( n, p->first_node, p->last_node, next, prev );
      p->nodes++;

      if ( !reach[0]->position )
        return n;

      CREATE( d, node *, decomposition_length(reach) + 2 );
      d[0] = n;
      for ( rptr = reach, dptr = &d[1]; *rptr; rptr++ )
        *dptr++ = *rptr;
      *dptr = NULL;

      n->less1 = adstend_pattern_recurse( p, d, decomposition_length(d) );
      free(d);
      return n;
    }

    /*
     * We are now considering an indecomposable candidate, to the right of
     * "after", and no nodes in between were suitable.
     *
     * Compare the candidate's decomposition with "reach".
     *
     * If candidate->decomposition > reach, we must insert the node we're looking for just before candidate,
     *   except in a special case (see comments below).
     * If candidate->decomposition = reach, then this candidate is exactly what we were looking for.
     * If candidate->decomposition < reach, we must continue our search further to the right.
     */
    candidate_reach = get_reach(candidate);
    cmp = compare_decompositions( candidate_reach, reach );

    if ( cmp == -1 )
    {
      /*
       * candidate->decomposition > reach, so insert the node we want here.
       *
       * Special exception case: If reach[0] >= candidate, then this candidate actually
       * is what we want (due to the nature of minreach).
       */
      if ( reach[0]->position >= candidate->position )
        return candidate;

      CREATE( n, node, 1 );
      n->p = p;
      n->id = NULL;
      n->position = candidate->position;
      n->decomposition = NULL;
      n->less1 = n;
      n->natural = 0;
      n->isnatural = 0;
      n->prev = candidate->prev;
      n->next = candidate;
      candidate->prev = n;
      n->prev->next = n;

      for ( nptr = candidate; nptr; nptr = nptr->next )
        nptr->position++;
      p->nodes++;

      if ( !reach[0]->position )
        return n;

      CREATE( d, node *, decomposition_length(reach) + 2 );
      d[0] = n;
      for ( rptr = reach, dptr = &d[1]; *rptr; rptr++ )
        *dptr++ = *rptr;
      *dptr = NULL;

      n->less1 = adstend_pattern_recurse( p, d, decomposition_length(d) );
      free(d);
      return n;
    }

    if ( cmp == 0 )
    {
      /*
       * If candidate->decomposition = reach, then this candidate is exactly what we were looking for.
       */
      return candidate;
    }

    /*
     * If candidate->decomposition < reach, then we must continue our search further to the right.
     * No need to uncomment this, it is the default behavior of the "while(1)" loop anyway.
     *
     * if ( cmp == 1 )
     *   continue;
     */
  }
}

/*
 * Multiply two patterns while already working in scratch space.
 *
 * First we amalgamate them so they have the same nodes, then we multiply
 * their highlighted nodes using the node multiplication algorithm.
 */
pattern *mult_patterns_assuming_scratch_workspace( pattern *p, pattern *q )
{
  amal *a;
  pattern *r;

  a = amalgamate( copy_pattern(p), copy_pattern(q) );

  r = copy_pattern(a->p);
  a->p = r;
  r->point = isom(a->p1_in_p,r);
  a->p1_in_p = isom(a->p1_in_p,r);
  a->p2_in_p = isom(a->p2_in_p,r);

  r = mult(a->p1_in_p, a->p2_in_p);
  return r;
}

/*
 * Exponentiation (base omega)
 *
 * This algorithm should only be called while already working in scratchspace
 *
 * For a pseudo-code version of this algorithm, see:
 * "Arithmetical algorithms for elementary patterns" (preprint)
 */
pattern *omexp( pattern *p )
{
  pattern *x, *y, *loga, *r;
  amal *a;
  node **reach, *bydecomp;

  /*
   * If alpha is an epsilon number, then omega^alpha = alpha.
   */
  if ( is_epsilon( p->point ) )
    return p;

  /*
   * omega^0 = 1
   */
  if ( p->point == p->first_node )
    return additive_one;

  /*
   * omega^1 = omega
   *
   * p->point = 1 precisely if p->point is the first node after zero in p, and has trivial less1
   */
  if ( p->point == p->first_node->next && p->point->less1 == p->point )
    return additive_omega;

  if ( p->point->decomposition )
  {
    /*
     * If alpha=alpha_1+...+alpha_n, where alpha_1,...,alpha_n is a decreasing
     * sequence of indecomposables, n>1, then let x=alpha_1, let y=alpha_2+...+alpha_n,
     * recursively calculate omega^x and omega^y, and multiply them to get
     * omega^(x+y) = omega^alpha.
     */
    x = copy_pattern(p);
    x->point = isom( p->point->decomposition[0], x );

    /*
     * We are trying to make y=alpha_2+...+alpha_n.
     * If alpha_2+...+alpha_n is defined in p, this is easy:
     *  make a copy of p and change its point to that.
     *
     * If not, we'll have to add alpha_2+...+alpha_n to a copy of p,
     *  in the correct (lexicographical) position.
     *  This is further complicated by the fact that alpha_2,...,alpha_n
     *  live in the _original_ p, and we'll have to locate their
     *  counterparts in the copy of p.
     */
    y = copy_pattern(p);
    bydecomp = get_node_by_decomposition( p, p->point->decomposition + 1 );

    if ( bydecomp )
      y->point = isom(bydecomp, y);
    else
    {
      node **dtranslate, **dptr1, **dptr2;
      int dlen = decomposition_length(p->point->decomposition + 1);

      CREATE( dtranslate, node *, dlen + 1);

      for ( dptr1 = p->point->decomposition + 1, dptr2 = dtranslate; *dptr1; dptr1++ )
        *dptr2++ = get_node_by_position( y, (*dptr1)->position );

      *dptr2 = NULL;

      y->point = adstend_pattern_recurse( y, dtranslate, dlen );

      free( dtranslate );
    }

    x = omexp(x);
    y = omexp(y);

    return mult_patterns_assuming_scratch_workspace( x, y );
  }

  /*
   * If alpha is indecomposable and not an epsilon number, then
   * omega^alpha is the first node n after alpha in p such that
   * minreach(n) = log(alpha) and such that minreach(n')<alpha
   * for all alpha<n'<n.  We compute log(alpha) using a
   * logarithm algorithm which is below (which, in turn, calls
   * omexp, but always on smaller ordinals, so the whole mess will
   * terminate).
   *
   * Now, it may be that there is no such n in p (as above).  In
   * that case we must insert such an n into p in the correct place.
   * We can avoid manually doing such an insertion, by simply
   * amalgamating p with the pattern from omlog(p).
   */
  loga = omlog( p );

  a = amalgamate( copy_pattern( p ), copy_pattern( loga ) );

  r = copy_pattern(a->p);
  a->p = r;
  r->point = isom(a->p1_in_p,r);
  a->p1_in_p = isom(a->p1_in_p,r);
  a->p2_in_p = isom(a->p2_in_p,r);

  if ( a->p2_in_p->decomposition )
    reach = copy_decomp_to_shell( a->p2_in_p->decomposition )->d;
  else
    reach = dshell_one_node( a->p2_in_p )->d;

  r->point = next_with_minreach_destructive( a->p1_in_p, reach );

  return r;
}

/*
 * Logarithm base omega.
 * This very simple function simply redirects to the "index" function.
 * (The "index" of an ordinal is the order type of the indecomposables
 *  below that ordinal.  Every ordinal has an index, and if the ordinal
 *  has a base-omega logarithm, then its index is its base-omega
 *  logarithm.)
 */
pattern *omlog( pattern *p )
{
  if ( is_epsilon( p->point ) )
    return p;

  if ( !p->point->decomposition && p->point->position )
    return omind( p );

  /*
   * log(0) is undefined, and so is log(alpha) if alpha is
   * decomposable.
   */
  return log_unimplemented;
}

/*
 * The Index Algorithm, from "Arithmetical algorithms for elementary patterns"
 *
 * Given a pattern p, with point denoting ordinal alpha, this function
 * returns a pattern whose point denotes index(alpha).  The index of alpha
 * is the order type of the set of indecomposable ordinals below alpha.
 */
pattern *omind( pattern *p )
{
  pattern *q, *x, *y;

  /*
   * Index(0) = 0
   */
  if ( !p->point->position )
    return additive_zero;

  /*
   * Index(1) = 0
   */
  if ( p->point->position == 1 && p->point->less1 == p->point )
    return additive_zero;

  /*
   * If alpha is an epsilon number then index(alpha)=alpha
   */
  if ( is_epsilon( p->point ) )
    return p;

  /*
   * If alpha=alpha_1+...+alpha_n, where alpha_1,...,alpha_n is a decreasing
   * sequence of indecomposables, n>1, then index(alpha) = index(alpha_1)+1
   */
  if ( p->point->decomposition )
  {
    q = copy_pattern(p);
    q->point = isom( p->point->decomposition[0], q );

    q = omind( q );

    return add_patterns_scratch( copy_pattern(q), copy_pattern(additive_one) );
  }

  /*
   * If alpha is indecomposable but isn't less1 anything bigger than itself,
   * then there's no way to generate new indecomposables below alpha in a fair
   * sequence of patterns (see "Arithmetical algorithms for elementary patterns")
   * and consequently index(alpha)=index(beta)+1 where beta is the biggest
   * indecomposable below alpha in p.
   */
  if ( p->point->less1 == p->point )
  {
    q = copy_pattern(p);

    /*
     * Find the biggest indecomposable below p->point
     */
    q->point = isom( p->point->prev, q );

    while ( q->point->decomposition )
      q->point = q->point->prev;

    q = omind( q );

    return add_patterns_scratch( copy_pattern(q), copy_pattern(additive_one) );
  }

  /*
   * Finally, suppose alpha is a non-epsilon number indecomposable and
   * alpha is less1 something bigger than itself.  Say alpha->less1 = alpha+reach(alpha).
   * Then index(alpha) = index(beta) + omega^reach(alpha), where beta is the largest
   * indecomposable below alpha in p.
   */
  x = copy_pattern(p);
  x->point = isom( p->point->prev, x );
  x = omind(x);

  y = omexp_decomp( get_reach( p->point ) );

  return add_patterns_scratch( copy_pattern(x), copy_pattern(y) );
}

/*
 * Variation on the exponentiation algorithm:
 * Given a sequence x_1,...,x_n of nodes, calculate
 * omega^(x_1+...+x_n).  This is done by recursively
 * computing omega^(x_1) and omega^(x_2+...+x_n)
 * and multiplying.
 */
pattern *omexp_decomp( node **d )
{
  pattern *p,*q;

  p = copy_pattern( d[0]->p );
  p->point = isom( d[0], p );

  p = omexp( p );

  if ( !d[1] )
    return p;

  q = omexp_decomp( &d[1] );

  return mult_patterns_assuming_scratch_workspace( p, q );
}
