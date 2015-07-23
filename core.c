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
 * core.c                                                                              *
 ***************************************************************************************
 * Implementation of the pattern amalgamation algorithm implicit in Lemma 7.12 of:     *
 * T.J. Carlson, 2001, "Elementary patterns of resemblance", Ann. Pure Appl. Logic     *
 **************************************************************************************/

#include "patterns.h"
#include "por.h"
#include "core.h"

/*
 * Global variables (mostly heads and tails of linked lists)
 */
amal_over *first_amal_over;
amal_over *last_amal_over;
mapping *first_mapping;
mapping *last_mapping;
amal *first_amal;
amal *last_amal;
pattern *first_temp_pattern;
pattern *last_temp_pattern;
pattern *first_pattern_copy;
pattern *last_pattern_copy;
ao_record *first_ao_record;
ao_record *last_ao_record;
int global_showwork;

/*
 * There are two types of patterns, as far as pattern arithmetic goes:
 *   1. Patterns we care about, which will be stored in RAM until the user frees them (or the process ends)
 *   2. Patterns we only use as intermediate steps in computations
 * When performing calculations, all new patterns default into type 2.
 * When not performing calculations, all new patterns default into type 1.
 * Rather than duplicate everything, and have two versions of every function, instead we'll
 *  just change the linked lists themselves when switching between "performing calculations" and "not".
 * The function "setup_scratch_workspace" swaps the linked list of patterns with a linked list
 *   of temporary patterns.  The function "unsetup_scratch_workspace" reverses that.
 */
void setup_scratch_workspace(void)
{
  first_pattern_copy = first_pattern;
  last_pattern_copy = last_pattern;
  first_pattern = first_temp_pattern;
  last_pattern = last_temp_pattern;
}

void unsetup_scratch_workspace(void)
{
  first_temp_pattern = first_pattern;
  last_temp_pattern = last_pattern;
  first_pattern = first_pattern_copy;
  last_pattern = last_pattern_copy;
}

/*
 * The isom function will be used frequently below.
 *
 * Given node n, and pattern p, (where n is not necessarily in p, n may be in some other pattern),
 * return the kth node of p, where n is the kth node of whatever pattern n is in.
 *
 * "isom" is short for "isomorphism".  The intuition is that if we have a pattern P which
 * is an isomorphic copy of a pattern Q, and we have a node n in Q, we would like to find
 * the node in P corresponding to n under the isomorphism.
 *
 * It might be worth testing whether streamlining this function would improve performance.
 */
node *isom( node *n, pattern *p )
{
  return get_node_by_position( p, n->position );
}

/*
 * The next function is for checking whether an initial segment of one pattern is isomorphically
 * an initial segment of another pattern.
 *
 * Suppose we have a pattern Q, and initial segment [0,n], where n is a node in Q.
 * Suppose we want to know whether [0,n] (the closed interval in Q) is isomorphic
 *   to some initial segment of P.
 * Then we can call this function with input n, P.
 */
int is_initial_segment( node *n, pattern *p )
{
  node *m, *N, *M, **d, **D;

  if ( n->p == p )
    return 1;

  if ( p->nodes <= n->position )
    return 0;

  /*
   * Get the node N (in p) which would correspond to n (in n's pattern)
   *  _if_ [0,n] (in n's pattern) is indeed isomorphic to [0,N] (in p)
   */
  N = isom( n, p );

  /*
   * Check whether [0,n] (in n's pattern) is isomorphic to [0,N] (in p)
   * by brute force.  This means checking that the less1 relations agree
   * and that the decompositions of nodes into sums agree.
   *
   * We search for any disagreement and return 0 as soon as we find one.
   * If we haven't found any disagreement after searching everything, return 1.
   */
  for ( m = n->p->first_node; m; m = m->next )
  {
    M = isom( m, p );

    if ( m->less1->position < n->less1->position && M->less1->position >= N->less1->position )
      return 0;

    if ( m->less1->position >= n->less1->position && M->less1->position < N->less1->position )
      return 0;

    if ( (!m->decomposition && M->decomposition) || (m->decomposition && !M->decomposition) )
      return 0;

    if ( m->decomposition )
    {
      d = m->decomposition;
      D = M->decomposition;
      while(1)
      {
        if ( ( !*d && *D ) || ( *d && !*D ) )
          return 0;
        if ( !*d )
          break;
        if ( (*d)->position != (*D)->position )
          return 0;
        d++;
        D++;
      }
    }
  }
  return 1;
}

/*
 * To amalgamate two patterns, we amalgamate them over {0}.
 * The algorithm used is T.J. Carlson's Lemma 7.12, from Carlson 2001.
 */
amal *amalgamate( pattern *P1, pattern *P2 )
{
  amal_over *ao;
  amal *a;

  /*
   * Amalgamate P1 and P2 over {0}.
   *
   * For technical reasons, instead of passing a pointer to the pointed pattern ({0},0),
   * we instead pass a pointer to its point, 0.
   *
   * The fourh argument to amalgamate_over_Q is the recursion depth.
   */
  ao = amalgamate_over_Q( P1, P2, additive_zero->last_node, 0 );

  /*
   * Now that we have an amal_over data structure, convert it back into a regular amal data structure.
   * (The amal_over structure is free'd in the clean_scratch_workspace function)
   */
  CREATE( a, amal, 1 );
  a->p = ao->p;
  a->p1 = P1;
  a->p2 = P2;
  a->p1_in_p = ao->map1[P1->point->position];
  a->p2_in_p = ao->map2[P2->point->position];
  LINK( a, first_amal, last_amal, next, prev );

  return a;
}

/*
 * Amalgamate two patterns P1,P2 over a pattern Q (where P1 and P2 are similarly well-situated over Q).
 *
 * See Carlson 2001, Lemma 7.12 for the original form of the algorithm (as a constructive proof)
 * (including the definition of "similarly well-situated over")
 *
 * Undefined behavior if P1 and P2 are *not* similarly well-situated over Q.
 *  However, if P1 and P2 start out similarly well-situated over Q, then the similar well-situatedness
 *  is preserved in all of this recursive function's calls to itself.  And P1,P2 are always similarly
 *  well-situated over {0}, so it's always safe to amalgamate over {0}.
 *
 * For technical reasons we don't actually pass the pattern Q, but rather, its rightmost node.
 */
amal_over *amalgamate_over_Q( pattern *P1, pattern *P2, node *Q, int depth )
{
  node *a1, *a2, *b1, *b2, *x;
  amal_over *ao;
  int pos;
  ao_record *rec;

  /*
   * If the global_showwork variable is turned on, the algorithm will "show its work"
   *  in the form of a linked list of ao_record data structures, each ao_record roughly
   *  corresponding to one "step" of work; an ao_record includes a human-readable
   *  string which describes the step in the language of Carlson's Lemma 7.12 (Carlson2001)
   */
  if ( global_showwork )
  {
    int i;
    char *rectxtptr;

    CREATE( rec, ao_record, 1 );
    CREATE( rec->txt, char, SHOW_WORK_BUF_SIZE );

    /*
     * Indent the "show work" step according to how deep we are in the recursion
     */
    for ( i=0, rectxtptr=rec->txt; i < depth; i++ )
      *rectxtptr++ = '-';

    *rectxtptr = '\0';

    /*
     * Note, we will append more information to rec->txt later on in the algorithm, this is just the first part of it
     */
    sprintf( rec->txt + strlen(rec->txt), "Amalling a %d-node pattern with a %d-node pattern over the first %d nodes", P1->nodes, P2->nodes, Q->position+1 );
    LINK( rec, first_ao_record, last_ao_record, next, prev );
    /*
     * The ao_record even includes "details", i.e., copies of the patterns being worked with in that step
     */
    rec->details = create_details( P1, P2, Q );
  }

  if ( P1->nodes == Q->position + 1 || P2->nodes == Q->position + 1)
  {
    /*
     * We're in the "base case" of the recursion:
     * one of the patterns that we're amalgamating over Q, actually is Q itself.
     * (The conditional only tests number of nodes, but this implies equality
     *  due to the original patterns being similarly well-situated over Q.)
     *
     * Since the two patterns are similarly-well-situated over Q, it follows
     * that the smaller of the two is Q itself.  Output the bigger of the two.
     * (But don't just output it.  Also output embeddings of both patterns into it.)
     */
    if ( global_showwork ) strcat( rec->txt, " (Base Case)" );

    /*
     * Create the data structure to hold the stuff we're going to output
     */
    CREATE( ao, amal_over, 1 );
    ao->created = "Base Case";
    ao->swaps = 0;
    ao->killed = 0;

    /*
     * Allocate memory for the embeddings of the original patterns into the amalgamation
     */
    CREATE( ao->map1, node *, P1->nodes + 1 );
    CREATE( ao->map2, node *, P2->nodes + 1 );
    ao->over = Q;

    /*
     * Whichever of the two original patterns equals Q, store the _other_ original pattern in
     * our data structure to be output.
     */
    if ( P1->nodes == Q->position + 1 )
    {
      ao->p = P2;
      for ( x = P1->first_node, pos=0; x; x = x->next )
        ao->map1[pos++] = isom( x, P2 );
      ao->map1[pos] = NULL;
      for ( x = P2->first_node, pos=0; x; x = x->next )
        ao->map2[pos++] = x;
      ao->map2[pos] = NULL;
    }
    else
    {
      ao->p = P1;
      for ( x = P1->first_node, pos=0; x; x = x->next )
        ao->map1[pos++] = x;
      ao->map1[pos] = NULL;
      for ( x = P2->first_node, pos=0; x; x = x->next )
        ao->map2[pos++] = isom( x, P1 );
      ao->map2[pos] = NULL;
    }
    ao->p1 = P1;
    ao->p2 = P2;
    LINK( ao, first_amal_over, last_amal_over, next, prev );
    return ao;
  }

  /*
   * We're not in the base case.  Then there are two cases (with two subcases each) to test for.
   *
   * Let a1, a2 be the "next node after Q" in P1, P2, respectively.  Let b1,b2 be the right endpoints
   *  of whatever arcs a1,a2 are left endpoints of.  (If a1,a2 are not left endpoints of any nondegenerate
   *  arc, then b1=a1 and b2=a2.)
   */
  a1 = isom( Q, P1 )->next;
  a2 = isom( Q, P2 )->next;
  b1 = a1->less1;
  b2 = a2->less1;

  if ( b1 != P1->last_node || b2 != P2->last_node )
  {
    /*
     * Case 1: In at least one of the patterns P1,P2, the first circle after Q does *not*
     *  contain everything.
     *
     * Let P1bar be the initial segment of P1 from 0 up to the end of the first circle after Q.
     * Similar for P2bar.  Let Pbar be the amalgamation of P1bar and P2bar over Q (recursively).
     * Let b1bar,b2bar be the images of b1,b2 in Pbar.
     */
    pattern *P1bar, *P2bar;
    amal_over *Pbar, *P_mid, *P_amal;
    node *b1bar, *b2bar;

    P1bar = copy_initial_segment( P1, b1 );
    P2bar = copy_initial_segment( P2, b2 );
    Pbar = amalgamate_over_Q( P1bar, P2bar, Q, depth+1 );

    b1bar = Pbar->map1[b1->position];
    b2bar = Pbar->map2[b2->position];

    if ( b1bar == b2bar )
    {
      /*
       * Case 1 Subcase 1:
       *
       * When looking at the nodes of P1 and P2 as the ordinals they notate,
       * the first node after Q in P1, and the first node after Q in P2,
       * both have the same Sigma_1-elementary power.
       *
       * How to proceed in this case is highly technical.  We will try to
       * explain in a later version, but it won't be easy.  'Til then, the
       * details are in the proof of Lemma 7.12 of Carlson2001.
       */
      mapping *m1, *m2;

      if ( global_showwork ) strcat( rec->txt, " (Case 1 Subcase 1)" );
      /*
       * We invoke Lemma 7.11 of Carlson2001
       */
      m1 = lemma711( P1, Pbar->p, Pbar->map1 );
      m2 = lemma711( P2, Pbar->p, Pbar->map2 );
      P_mid = amalgamate_over_Q( m1->Ptilde, m2->Ptilde, Pbar->p->last_node, depth+1 );
      CREATE( P_amal, amal_over, 1 );
      P_amal->created = "B1bar == B2bar";
      P_amal->swaps = 0;
      P_amal->killed = 0;
      LINK( P_amal, first_amal_over, last_amal_over, next, prev );
      P_amal->over = Q;
      P_amal->p = P_mid->p;
      P_amal->p1 = P1;
      P_amal->p2 = P2;
      P_amal->map1 = compose_maps( P1, m1->Ptilde, P_amal->p, m1->map, P_mid->map1 );
      P_amal->map2 = compose_maps( P2, m2->Ptilde, P_amal->p, m2->map, P_mid->map2 );

      return P_amal;
    }
    else
    {
      /*
       * Case 1 Subcase 2:
       *
       * Looking at the nodes of P1,P2 as the ordinals they notate, the first node after
       * Q in P1 has a different Sigma_1-elementary power than the first node after Q in P2.
       *
       * Again, how to proceed is very technical.  We will try to explain better in a later
       * version.  Til then, the details are in Carlson2001, Lemma 7.12
       */
      mapping *m;

      /*
       * How to proceed depends which pattern's first-node-after-Q has greater Sigma_1-elementary power.
       * But it's symmetric, so we only handle the case where P2's first-node-after-Q has more power.
       * If we're in the other situation, swap P1 and P2.
       */
      if ( b1bar->position > b2bar->position )
      {
        if ( global_showwork ) strcat( rec->txt, " (Case 1 Subcase 2, but b1bar > b2bar so swap)" );
        goto swap_patterns;
      }
      else
        if ( global_showwork ) strcat( rec->txt, " (Case 1 Subcase 2)" );

      m = lemma711( P2, Pbar->p, Pbar->map2 );
      P_mid = amalgamate_over_Q( P1, m->Ptilde, P1bar->last_node, depth+1 );
      CREATE( P_amal, amal_over, 1 );
      P_amal->created = "B1bar not= B2bar";
      P_amal->swaps = 0;
      P_amal->killed = 0;
      LINK( P_amal, first_amal_over, last_amal_over, next, prev );
      P_amal->over = Q;
      P_amal->p = P_mid->p;
      P_amal->p1 = P1;
      P_amal->p2 = P2;
      P_amal->map2 = compose_maps( P2, m->Ptilde, P_amal->p, m->map, P_mid->map2 );
      P_amal->map1 = copy_map(P_mid->map1);

      return P_amal;
    }
  }
  else
  {
    /*
     * Case 2:
     *
     * In both input patterns, the first circle after Q contains everything.
     */
    amal_over *P_amal;

    if ( a1->decomposition || a2->decomposition )
    {
      /*
       * Case 2 Subcase 1:
       *
       * The first node after Q, in one of the input patterns is decomposable.
       *
       * How to proceed depends which of the input patterns has the decomposable node.
       * But it's symmetric, so we only handle the case where P1's first node after Q is
       *  decomposable.  If we're in the other situation, we swap the input patterns.
       */
      if ( !a1->decomposition )
      {
        if ( global_showwork ) strcat( rec->txt, " (Case 2 Subcase 1, but a1 indecomposable so swap)" );
        goto swap_patterns;
      }

      /*
       * Since decomposable nodes cannot be left endpoints of nondegenerate circles,
       * and since we're in Case 2, where the first circle after Q contains everything,
       * that means P1 has only one node after Q.
       *
       * If P2 also happens to have first-node-after-Q decomposable, then P2 also has
       * only one node after Q.  If that node's decomposition matches the decomposition in P1,
       * the two patterns are actually isomorphic, and either one can serve as amalgamation
       * (we'll use P2).
       */
      if ( a2->decomposition && same_decompositions( a1->decomposition, a2->decomposition ) )
      {
        if ( global_showwork ) strcat( rec->txt, " (Case 2 Subcase 1, a1 and a2 have same decompositions)" );
        CREATE( P_amal, amal_over, 1 );
        P_amal->created = "Same decompositions";
        P_amal->swaps = 0;
        P_amal->killed = 0;
        P_amal->over = Q;
        P_amal->p = P2;
        P_amal->p1 = P1;
        P_amal->p2 = P2;
        P_amal->map1 = isom_map( P1, P2 );
        P_amal->map2 = identity_map( P2 );
        LINK( P_amal, first_amal_over, last_amal_over, next, prev );

        return P_amal;
      }
      else
      {
        /*
         * But suppose P1 has only one node beyond Q (and that node is decomposable), and either P2 has multiple
         * nodes after Q (in which case its leftmost must be indecomposable since P2's first circle
         * after Q covers everything and decomposables cannot be left endpoints of nondegenerate
         * circles), or P2's lone node after Q has a different decomposition than the lone node after Q
         * in P1.
         *
         * Strategy: Add P1's first-node-after-Q into P2 (call the result Pnew).
         *  This may involve adding other nodes into P2 as well, to ensure P2's arithmetic is well behaved.
         *  Pnew serves as the amalgamation.
         */
        pattern *Pnew;
        node *newnode;

        if ( global_showwork ) strcat( rec->txt, " (Case 2 Subcase 1, a1 and a2 have different decompositions)" );
        Pnew = additively_extend_specialcase( P2, a1->decomposition, &newnode );
        CREATE( P_amal, amal_over, 1 );
        P_amal->created = "Additive Extension";
        P_amal->swaps = 0;
        P_amal->killed = 0;
        LINK( P_amal, first_amal_over, last_amal_over, next, prev );
        P_amal->over = Q;
        P_amal->p = Pnew;
        P_amal->p1 = P1;
        P_amal->p2 = P2;
        P_amal->map1 = isom_change_last_point( P1, Pnew, newnode );
        P_amal->map2 = isom_avoid_one_point( P2, Pnew, newnode );

        return P_amal;
      }
    }
    else
    {
      /* Case 2, Subcase 2:
       *
       * In each node, the circle after Q contains everything, and the points after Q are indecomposable.
       * In particular, if we extend Q by one more point, P1 and P2 will still be similarly well-situated
       *  over the extension Q', this is because the next point in P1 and the next point in P2 look
       *  identical (at least ignoring their interaction with later points).
       * So extend Q and amalgamate, recursively, over the extension.
       */
      pattern *Q_extend, *Pplus, *Pprime;
      amal_over *P_mid;
      node *abar, *b1bar, *b2bar, *z;
      node **Pmid_into_Pplus, *head, *tail;
      node **dx, *y;

      /*
       * Let Q_extend be Q, extended by one more point.
       * Since Q is an initial segment of P1, and its next point in P1 is a1,
       * Q_extend shall be the initial segment up to a1 in P1.
       */
      Q_extend = copy_initial_segment( P1, a1 );

      /*
       * Let P_mid be the amalgamation of P1,P2 over the extension Q_extend
       */
      P_mid = amalgamate_over_Q( P1, P2, Q_extend->last_node, depth+1 );

      /*
       * Now find where the next node after Q, in P1,P2, is located inside P_mid.
       * Call its location there: abar.
       * And then, find where the next circle after Q, ends.
       *  - But this is ambiguous, since "the next circle after Q" depends whether
       *    we're looking in P1 or in P2.  So check both.
       *    Let b1bar be the position of b1 in P_mid, i.e., where the next
       *    circle after Q in P1 ends, as embedded in P_mid.
       *    Similarly for b2bar.
       */
      abar = P_mid->map1[a1->position];
      b1bar = P_mid->map1[b1->position];
      b2bar = P_mid->map2[b2->position];

      /*
       * Now it may turn out that "where the next circle after Q ends, within P_mid", is actually
       *  independent whether we're talking about the next circle in P1, or in P2.
       *  If so, P_mid can be used as the amalgamation of P1,P2 over Q.
       */
      if ( b1bar == b2bar )
      {
        if ( global_showwork ) strcat( rec->txt, " (Case 2 Subcase 2, b1=b2)" );
        P_mid->over = Q;

        return P_mid;
      }

      /*
       * But assume the "next circle after Q (within P_mid)" does really depend on whether we're
       *  talking about circles in P1 or circles in P2.
       *
       * How to proceed depends which circle ends later (in P_mid).  But the two possibilities are symmetric,
       *  and we'll only treat the case when the P2-circle ends later.  If the P1-circle ends later,
       *  we simply swap the patterns and try again.
       */
      if ( b1bar->position > b2bar->position )
      {
        if ( global_showwork ) strcat( rec->txt, " (Case 2 Subcase 2, but b1 > b2 so swap)" );
        goto swap_patterns;
      }
      else
        if ( global_showwork ) strcat( rec->txt, " (Case 2 Subcase 2, b1 < b2)" );

      /*
       * Since the P2-circle ends later, it follows that it generates the P1-circle, that is,
       * we can insert a copy of the P1-circle into P2 just before the P2-circle, without changing
       * which ordinals are notated by the nodes of P2.  Call the resulting pattern Pplus.
       * At the same time as we build Pplus, we also build a map, Pmid_into_Pplus, that tells where
       * the elements of Pmid live inside Pplus.
       *
       * The following line contained a bug.  Bora Bosna detected it (via counterexample) on 25Feb2012.
       * The bugged line was:
       *   Pplus = reflect_specialcase( P_mid->p, abar, b1bar, abar, &Pmid_into_Pplus );
       */
      Pplus = reflect_specialcase( P_mid->p, a1, b1, abar, &Pmid_into_Pplus );

      /*
       * The pattern Pplus we have constructed, is the correct amalgamation we're looking for,
       * up to abar (abar was the first point after Q in P1/P2, though it is not the first
       * point after Q in Pplus---we've reflected additional stuff between it and Q).  After
       * abar, P2 is the amalgamation we're looking for.  So what we do now is we literally
       * take the initial segment of Pplus up to abar, and append the terminal segment of P2
       * onto it.  The rest is book-keeping.
       */
      Pprime = copy_initial_segment( Pplus, Pmid_into_Pplus[abar->position]->prev );
      free(Pmid_into_Pplus);

      head = copy_interval( P2, a2, b2, &tail );

      head->position = Pprime->last_node->position + 1;
      for ( z = head->next; z; z = z->next )
        z->position = z->prev->position + 1;

      head->prev = Pprime->last_node;
      Pprime->last_node->next = head;
      Pprime->last_node = tail;
      Pprime->nodes += tail->position - head->position + 1;
      CREATE( P_amal, amal_over, 1 );
      P_amal->created = "Reflection";
      P_amal->swaps = 0;
      P_amal->killed = 0;
      LINK( P_amal, first_amal_over, last_amal_over, next, prev );
      P_amal->over = Q;
      P_amal->p = Pprime;
      P_amal->p1 = P1;
      P_amal->p2 = P2;

      /*
       * Pprime is the amalgamation we're looking for, but we also need embeddings of P1 and P2 into Pprime,
       * in order for the recursion to go through.  It's easy to map P1 into Pprime: it's an initial segment.
       */
      P_amal->map1 = isom_map( P1, Pprime );

      /*
       * Mapping P2 into Pprime is trickier: it's an initial segment up until the first point, a2, after Q in
       * P2.  But in Pprime, there is additional stuff reflected between the image of Q and the image of a2,
       * and the mapping must skip over that additional stuff.
       */
      CREATE( P_amal->map2, node *, P2->nodes + 1 );

      for ( dx = P_amal->map2, y = P2->first_node; y; y = y->next )
      {
        /*
         * P2 embeds into Pprime as an initial segment......
         */
        if ( y->position < a2->position )
          *dx++ = isom( y, Pprime );
        else
        {
          /*
           * ......until it doesn't.
           *
           * Fix Bora Bosna's Counterexample -- 25 Feb 2012.
           * The next line used to be incorrect:
           * *dx++ = get_node_by_position( Pprime, y->position + b1bar->position - abar->position + 1 );
           */
          *dx++ = get_node_by_position( Pprime, y->position + b1->position - a1->position + 1 );
        }
      }
      *dx = NULL;

      /*
       * Make sure that the Sigma_1-elementary-power-of-the-image equals the image-of-the-Sigma_1-elementary-power.
       * (In other words, repair any arcs which were broken when we recklessly concatenated initial segments
       *  and terminal segments of different patterns to create Pprime).
       *
       * For example, suppose the last common node in Q and P2 was the left endpoint of an arc whose right
       * endpoint was the next node, a2, in P2.  When we reflect stuff between Q and a2, the "next node in P2"
       * is no longer a2, but one of the newly reflected nodes.  Before reflection, arc's right endpoint was
       * a2, but now the arc's right endpoint is the leftmost new reflected node: which is not intended, so
       * fix it.
       */
      for ( y = P2->first_node; y; y = y->next )
      {
        if ( (P_amal->map2[y->position])->less1->position < (P_amal->map2[y->less1->position])->position )
          (P_amal->map2[y->position])->less1 = P_amal->map2[y->less1->position];
      }

      return P_amal;
    }
  }

swap_patterns:
  /*
   * At various places above, the procedure depends on whether P1 has a certain property or whether P2 does,
   * but there is symmetry so we only treat one of the possibilities and in the other event we swap
   * P1 and P2.  One is tempted to just immediately do the swap and carry on, and this would work if we
   * were only computing the amalgamation; but since we're simultaneously computing embeddings of the
   * original patterns into the amalgamation, a naive swap wouldn't work.  Instead it's necessary
   * (at least in the Knuthian "avoid premature optimization" sense) to recursively call the function
   * with swapped arguments, and once we get the result, swap _its_ embeddings.
   */
  {
    pattern *pswap;
    node **mapswap;
    amal_over *P_amal;

    P_amal = amalgamate_over_Q( P2, P1, Q, depth+1 );
    pswap = P_amal->p1;
    P_amal->p1 = P_amal->p2;
    P_amal->p2 = pswap;
    mapswap = P_amal->map1;
    P_amal->map1 = P_amal->map2;
    P_amal->map2 = mapswap;
    P_amal->swaps++;

    return P_amal;
  }
}

/*
 * Our implementation of Carlson's Lemma 7.11 is recursive.  There is some
 * paperwork to be done after every call, so we employ a wrapper function.
 */
mapping *lemma711( pattern *P, pattern *Q, node **bintoQ )
{
  mapping *m;
  node *n;

  m = lemma711_wrapper( P, Q, bintoQ );
  for ( n = P->first_node; n; n = n->next )
  {
    if ( m->map[n->position]->less1->position < n->less1->position )
      (m->map[n->position])->less1 = m->map[n->less1->position];
  }
  return m;
}


/*
 * The actual implementation itself of Carlson's Lemma 7.11 is extremely
 * technical and very difficult to adequately comment.  Hopefully I will
 * be able to give it proper commenting in a later version.  (In the paper
 * itself the situation is similar: "a simple induction", "straightforward",
 * "we can assume"... which is fine in that context, but actually making
 * it machine-readable was very difficult.)
 *
 * For the present time, the user will probably have to treat the
 * Lemma 7.11 implementation as a "black box".
 */
mapping *lemma711_wrapper( pattern *P, pattern *Q, node **bintoQ )
{
  int pos,i;
  node *x, *x_in_P, **y, *after_x_in_P, *ptr, **newbintoQ;
  mapping *m, *n;
  pattern *Pnew;

  for ( pos = 0, x = Q->first_node; x; x = x->next )
  {
    if ( bintoQ[pos] == x )
    {
      pos++;
      continue;
    }
    Pnew = copy_pattern( P );
    if ( x->decomposition )
    {
      CREATE( x_in_P, node, 1 );
      x_in_P->id = NULL;
      x_in_P->p = Pnew;
      x_in_P->less1 = x_in_P;
      x_in_P->isnatural = 0;
      x_in_P->position = pos;
      CREATE( x_in_P->decomposition, node *, decomposition_length(x->decomposition) + 1 );
      for (i=0,y=x->decomposition; *y; y++ )
        x_in_P->decomposition[i++] = get_node_by_position( Pnew, (*y)->position );
      x_in_P->decomposition[i] = NULL;
      after_x_in_P = get_node_by_position( Pnew, pos );
      INSERT( x_in_P, after_x_in_P, Pnew->first_node, next, prev );
      for ( ptr = after_x_in_P; ptr; ptr = ptr->next )
        ptr->position++;
      Pnew->nodes++;
/*
      CREATE( newbintoQ, node *, Pnew->nodes + 1 );
      for ( y=newbintoQ, ptr=Pnew->first_node, i=0; ptr; ptr = ptr->next )
      {
        if ( ptr == x_in_P )
          *y++ = x;
        else
          *y++ = bintoQ[i++];
      }
*/
      CREATE( newbintoQ, node *, Pnew->nodes + 1 );
      for ( y=newbintoQ, ptr=Pnew->first_node, i=0; bintoQ[i]; ptr = ptr->next )
      {
        if ( ptr == x_in_P )
          *y++ = x;
        else
          *y++ = bintoQ[i++];
      }
      *y = NULL;

      //newbintoQ = ignore_new_interval( bintoQ, Pnew, x_in_P, x_in_P );

      m = lemma711( Pnew, Q, newbintoQ );   /* A map from newP into Ptilde.  Must convert into a map from P into Ptilde. */
      free( newbintoQ );

      CREATE( n, mapping, 1 );
      n->P = P;
      n->Ptilde = m->Ptilde;
      CREATE( n->map, node *, P->nodes + 1 );
      LINK( n, first_mapping, last_mapping, next, prev );
      for ( y = n->map, i=0, ptr=Pnew->first_node; m->map[i]; i++ )
      {
        if ( ptr != x_in_P )
          *y++ = m->map[i];
        ptr = ptr->next;
      }
      *y = NULL;
      return n;
    }
    else
    {
      node *less1 = bintoQ[pos]->prev, *head, *tail, *ptr;
      int j, offset, newstuffstart, newstuffend;

      after_x_in_P = get_node_by_position( Pnew, pos );
      i = less1->position - x->position;
      CREATE( newbintoQ, node *, Pnew->nodes + i + 2 );

      head = copy_interval( Pnew, x, less1, &tail );

      head->position = after_x_in_P->prev->position + 1;
      for ( ptr = head->next; ptr; ptr = ptr->next )
        ptr->position = ptr->prev->position + 1;

      newstuffstart = head->position;
      newstuffend = tail->position;
      tail->next = after_x_in_P;
      after_x_in_P->prev->next = head;
      head->prev = after_x_in_P->prev;
      after_x_in_P->prev = tail;
      Pnew->nodes += i + 1;
      for ( ptr = after_x_in_P; ptr; ptr = ptr->next )
        ptr->position += i + 1;

      //for ( ptr=Q->first_node, j = 0, offset=i+1; j < Pnew->nodes; j++ )
      for ( ptr=Q->first_node, j = 0, offset=i+1; j <= less1->position || bintoQ[j-offset]; j++ )
      {
        if ( j <= less1->position )
        {
          newbintoQ[j] = ptr;
          ptr = ptr->next;
        }
        else
          newbintoQ[j] = bintoQ[j-offset];
      }
      newbintoQ[j] = NULL;

      m = lemma711( Pnew, Q, newbintoQ );  /*  Map from Pnew into Ptilde.  Must convert to map from P into Ptilde. */
      free( newbintoQ );
      CREATE( n, mapping, 1 );
      LINK( n, first_mapping, last_mapping, next, prev );
      n->P = P;
      n->Ptilde = m->Ptilde;
      CREATE( n->map, node *, P->nodes + 1 );
      for ( y = n->map, j=0, ptr=Pnew->first_node; ptr; ptr = ptr->next )
      {
        if ( ptr->position < newstuffstart || ptr->position > newstuffend )
          *y++ = m->map[j];
        j++;
      }
      *y = NULL;
      return n;
    }
  }
  CREATE( m, mapping, 1 );
  m->P = P;
  m->Ptilde = P;
  CREATE( m->map, node *, P->nodes + 1 );
  for ( x = P->first_node, pos = 0; x; x = x->next )
    m->map[pos++] = x;
  m->map[pos] = NULL;
  LINK( m, first_mapping, last_mapping, next, prev );
  return m;
}

/*
 * Copy an initial segment of pattern P, including all
 * nodes from 0 to node b.
 *
 * The strategy is crude and could be optimized:
 * copy all of P, and throw away the parts after b.
 */
pattern *copy_initial_segment( pattern *P, node *b )
{
  pattern *seg;
  node *bstar, *x, *x_next;

  seg = copy_pattern( P );
  bstar = isom( b, seg );

  /*
   * If our copy of P contains any arc with right endpoint
   * beyond b, that arc needs to be shrunk so its right endpoint
   * equals b.
   */
  for ( x = seg->first_node; x!=bstar->next; x=x->next )
    if ( x->less1->position > bstar->position )
      x->less1 = bstar;

  /*
   * Kill the nodes we don't want.
   */
  for ( x = bstar->next; x; x = x_next )
  {
    x_next = x->next;
    if ( seg->point == x )
      seg->point = seg->first_node;
    kill_node(x);
  }

  seg->last_node = bstar;
  bstar->next = NULL;

  seg->nodes = b->position + 1;

  return seg;
}

/*
 * Copy an interval from node "start" to node "end".
 * Prepare the copied nodes to be inserted into pattern "dest".
 *
 * The specified start and endpoint of the interval may or may not already live
 * in dest.  They should, however, both live in the same pattern as each other
 * (or else the function yields undefined behavior).
 *
 * The function returns the head of a doubly-linked list of nodes, and
 * points tailptr at the tail of that list.
 */
node *copy_interval( pattern *dest, node *start, node *end, node **tailptr )
{
  node *x, *y, *z, *head=NULL, *tail=NULL, **d, **dx, *less1;
  int dlen;

  for ( x=start; x!=end->next; x=x->next )
  {
    CREATE( y, node, 1 );
    y->p = dest;

    /*
     * First pass:
     *
     * We cannot set the less1 pointers yet, as they
     * may need to be pointed toward nodes which we
     * will be creating later on in this loop.
     * Make all arcs degenerate initially, we'll have
     * to fix them in a second pass.  Same with
     * decompositions (which we simply leave uninitialized
     * for now).
     */
    y->less1 = y;

    y->position = x->position;
    y->isnatural = 0;
    y->id = NULL;
    LINK( y, head, tail, next, prev );
  }

  /*
   * Second pass:
   *
   * Now that the new nodes at least exist, go through
   * them again and set their less1's and decompositions.
   */
  for ( x = head, y=start; x; x = x->next )
  {
    if ( y->less1 != y )
    {
      if ( y->less1->position <= end->position )
        less1 = y->less1;
      else
        less1 = end;
      if ( less1 != y )
      {
        for ( z = x->next; ; z=z->next )
          if ( z->position == less1->position )
            break;
        x->less1 = z;
      }
    }
    if ( y->decomposition )
    {
      dlen = decomposition_length(y->decomposition);
      CREATE( x->decomposition, node *, dlen+1 );
      for ( d = y->decomposition, dx = x->decomposition; *d; d++ )
      {
        if ( (*d)->position < head->position )
          *dx++ = isom(*d, dest );
        else
        {
          for ( z = head; ; z=z->next )
            if ( z->position == (*d)->position )
              break;
          *dx++ = z;
        }
      }
      *dx = NULL;
    }
    y = y->next;
  }

  *tailptr = tail;
  return head;
}

/*
 * Create a copy of a map.
 * (Maps are essentially strings, except instead of being
 *  arrays of char's, they are arrays of node *'s.)
 */
node **copy_map( node **map )
{
  node **d, **dx, **y;

  CREATE( d, node *, decomposition_length(map) + 1 );
  for ( dx = d, y = map; *y; y++ )
    *dx++ = *y;

  *dx = NULL;
  return d;
}

/*
 * Compose maps, in the mathematical sense:
 * The value of (compose_maps(map1,map2))(x) shall equal map2(map1(x)).
 */
node **compose_maps( pattern *start, pattern *mid, pattern *end, node **map1, node **map2 )
{
  node **map, **x, *n;

  CREATE( map, node *, start->nodes + 1 );
  for ( n = start->first_node, x = map; n; n = n->next )
    *x++ = map2[(map1[n->position])->position];
  *x = NULL;
  return map;
}

/*
 * Create the identity map:
 * The value of (identity_map(p))(x) shall equal x.
 */
node **identity_map( pattern *p )
{
  node **d, *x, **dx;

  CREATE( d, node *, p->nodes + 1 );

  for ( dx = d, x = p->first_node; x; x = x->next )
    *dx++ = x;

  *dx = NULL;
  return d;
}

/*
 * Create an order-isomorphism from p to q:
 * If x is the nth node of p, then (isom_map(p,q))(x) shall be the nth node of q.
 *
 * Undefined behaviour if p has more nodes than q.
 */
node **isom_map( pattern *p, pattern *q )
{
  node **d, **dx, *x, *y;

  CREATE( d, node *, p->nodes + 1 );

  for ( dx = d, x=p->first_node, y=q->first_node; x; x = x->next )
  {
    *dx++ = y;
    y = y->next;
  }
  *dx = NULL;

  return d;
}

/*
 * Create an order-isomorphism from p to q, except, map the last node
 * of p to newlast instead.
 *
 * Undefined behaviour if p has at least 2 more nodes than q.
 */
node **isom_change_last_point( pattern *p, pattern *q, node *newlast )
{
  node **d, **dx, *x, *y;

  CREATE( d, node *, p->nodes + 1 );

  for ( dx=d, x=p->first_node, y=q->first_node; x; x = x->next )
  {
    if ( x == p->last_node )
      *dx++ = newlast;
    else
    {
      *dx++ = y;
      y = y->next;
    }
  }
  *dx = NULL;
  return d;
}

/*
 * Create an order-isomorphism from p to q\{avoid}, where \ denotes set difference.
 *
 * Undefined behavior in various cases that are hard to succinctly state.
 */
node **isom_avoid_one_point( pattern *p, pattern *q, node *avoid )
{
  node **d, **dx, *x, *y;

  CREATE( d, node *, p->nodes + 1 );

  for ( dx=d, x=p->first_node, y=q->first_node; x; x = x->next )
  {
    if ( y == avoid )
      y = y->next;
    *dx++ = y;
    y = y->next;
  }
  *dx = NULL;
  return d;
}

/*
 * Suppose we have a map "oldmap" into an old pattern.
 * Suppose a new pattern, "newptn", is obtained from the old pattern
 * by adding a new interval, [left,right] (possibly a single point,
 * if left=right).  Create a new map into the new pattern, identical
 * to the old map, i.e., ignoring the new interval.
 */
node **ignore_new_interval( node **oldmap, pattern *newptn, node *left, node *right )
{
  node **newmap, **oldptr, **newptr;
  int offset;

  offset = right->position - left->position + 1;

  CREATE( newmap, node *, decomposition_length(oldmap) + 1 );

  for ( oldptr=oldmap, newptr=newmap; *oldptr; oldptr++ )
  {
    if ( (*oldptr)->position < left->position )
      *newptr++ = isom( *oldptr, newptn );
    else
      *newptr++ = get_node_by_position( newptn, (*oldptr)->position + offset );
  }
  *newptr = NULL;

  return newptr;
}

/*
 * Add a new node to (a copy of) a given pattern, make that node have
 * a given decomposition, and insert it in the correct place based on that
 * decomposition.
 *
 * "decomp" is not required to live in p, neither is it required not to live in p.
 * It is, however, required that no node in p already have decomposition "decomp"
 * (or isomorphic thereto).
 *
 * In addition to returning the new pattern, the function also points "newnode"
 * at the new node.
 */
pattern *additively_extend_specialcase( pattern *p, node **decomp, node **newnode )
{
  pattern *q;
  int dlen;
  node **d, **dx, *n, *m;

  q = copy_pattern(p);

  CREATE( n, node, 1 );
  n->id = NULL;
  n->isnatural = 0;
  n->less1 = n;
  n->p = q;
  dlen = decomposition_length(decomp);
  CREATE( n->decomposition, node *, dlen + 1 );
  for ( d = decomp, dx = n->decomposition; *d; d++ )
    *dx++ = isom(*d,q);
  *dx = NULL;

  /*
   * Search for the proper place to insert the new node.
   */
  for ( m = q->first_node; m ; m = m->next )
  {
    if ( !m->decomposition && m->position > (*decomp)->position )
      break;
    if ( m->decomposition && !lex_leq(m->decomposition, decomp) )
      break;
  }

  /*
   * If no proper place was found to insert the new node,
   * then append it.
   */
  if ( !m )
  {
    n->position = q->nodes;
    LINK( n, q->first_node, q->last_node, next, prev );
  }
  else
  {
    n->position = m->position;
    INSERT( n, m, q->first_node, next, prev );
    for ( ; m ; m = m->next )
      m->position++;
  }
  q->nodes++;

  *newnode = n;
  return q;
}

/*
 * Make a copy of the interval from "start" to "end", and place it just to the left of "below"
 *
 * "start" and "end" must be nodes in the same pattern, but that pattern does not have to be p.
 *
 * In addition to returning the resulting pattern, the function points "map" toward an embedding
 * of the original pattern p into the resulting pattern.
 */
pattern *reflect_specialcase( pattern *p, node *start, node *end, node *below, node ***map )
{
  node *head, *tail, *below_in_q, *x;
  pattern *q;
  int i;

  q = copy_pattern(p);

  *map = isom_map( p, q );

  head = copy_interval( q, start, end, &tail );

  below_in_q = isom( below, q );

  head->position = below_in_q->position;
  for ( x = head->next; x; x = x->next )
    x->position = x->prev->position + 1;

  tail->next = below_in_q;
  head->prev = below_in_q->prev;
  below_in_q->prev->next = head;
  below_in_q->prev = tail;

  i = tail->position - head->position + 1;

  for ( x = below_in_q; x; x = x->next )
    x->position += i;

  q->nodes += i;

  return q;
}

/*
 * Free up all memory allocated for temporary patterns and related data structures.
 */
void clean_scratch_workspace(void)
{
  pattern *p, *p_next;
  amal *a, *a_next;
  amal_over *ao, *ao_next;
  mapping *m, *m_next;
  ao_record *rec, *rec_next;
  decomp_shell *d, *d_next;

  for ( p = first_temp_pattern; p; p = p_next )
  {
    p_next = p->next;
    UNLINK( p, first_temp_pattern, last_temp_pattern, next, prev );
    kill_pattern(p);
  }
  first_temp_pattern = NULL;
  last_temp_pattern = NULL;

  for ( ao = first_amal_over; ao; ao = ao_next )
  {
    ao_next = ao->next;
    kill_amal_over(ao);
  }
  first_amal_over = NULL;
  last_amal_over = NULL;

  for ( a = first_amal; a; a = a_next )
  {
    a_next = a->next;
    kill_amal(a);
  }
  first_amal = NULL;
  last_amal = NULL;

  for ( m = first_mapping; m; m = m_next )
  {
    m_next = m->next;
    kill_mapping(m);
  }

  for ( rec = first_ao_record; rec; rec = rec_next )
  {
    rec_next = rec->next;
    kill_ao_record( rec );
  }

  for ( d = first_decomp_shell; d; d = d_next )
  {
    d_next = d->next;
    free( d->d );
    free(d);
  }
  first_decomp_shell = NULL;
  last_decomp_shell = NULL;

  first_mapping = NULL;
  last_mapping = NULL;
}

void kill_amal_over( amal_over *ao )
{
  free( ao->map1 );
  free( ao->map2 );
  free(ao);
}

void kill_amal( amal *a )
{
  free(a);
}

void kill_mapping( mapping *m )
{
  free( m->map );
  free(m);
}

void kill_ao_record( ao_record *rec )
{
  free ( rec->txt );
  UNLINK( rec, first_ao_record, last_ao_record, next, prev );
  free ( rec );
}

/*
 * Create a "details" data structure (used when the amalgamate algorithm
 * is asked to show its work).
 *
 * A "details" structure contains pointers to patterns which were
 * used during a step in the amalgamation algorithm.
 * Now, such a pattern may be "true" (meaning it persists in memory
 * because it was the final result of some calculation), or may
 * be "non-true" (meaning that it was a temporary pattern and would
 * have been completely forgotten, if not for the fact that the
 * amalgamate algorithm was asked to show its work).
 *
 * Admittedly a little clumsily implemented, but that's because at the time
 * I wrote it, I assumed Bora Bosna would be the only person to ever use
 * the "showwork" feature.
 */
ao_detail *create_details( pattern *P1, pattern *P2, node *Q )
{
  static int id;
  ao_detail *d;
  pattern *truep;

  /*
   * Check whether P1 is "true" or not (whether it exists in persistent memory
   * aside from ao_details).
   *
   * The reason we iterate starting at first_pattern_copy instead of first_pattern
   * is because this function will ordinarily be called when we're working in
   * scratch space (at which time, the linked list of persistent patterns is swapped
   * with the linked list of temporary patterns).
   */
  for ( truep = first_pattern_copy; truep; truep = truep->next )
    if ( same_pattern( truep, P1 ) )
      break;

  CREATE( d, ao_detail, 1 );

  if ( truep )
  {
    d->p1_is_true = 1;
    d->p1 = truep;
  }
  else
  {
    /*
     * If this detail is the detail of a step involving a pattern not otherwise
     * persistently stored in memory, then make a persistent copy of that pattern here.
     */
    d->p1 = copy_pattern(P1);
    d->p1_is_true = 0;

    /*
     * The "copy_pattern" function automatically links the pattern it creates,
     * which is the correct thing to do in _every other_ instance _except_ here.
     */
    UNLINK(d->p1, first_pattern, last_pattern, next, prev );
  }

  /*
   * Now repeat all the above but for P2 instead of P1
   */
  for ( truep = first_pattern_copy; truep; truep = truep->next )
    if ( same_pattern( truep, P2 ) )
      break;

  if ( truep )
  {
    d->p2_is_true = 1;
    d->p2 = truep;
  }
  else
  {
    d->p2 = copy_pattern(P2);
    d->p2_is_true = 0;
    UNLINK( d->p2, first_pattern, last_pattern, next, prev );
  }

  LINK( d, first_detail, last_detail, next, prev );
  d->id = id++;
  d->over_n_nodes = Q->position + 1;

  return d;
}
