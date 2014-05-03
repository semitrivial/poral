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
 * example.c                                                                           *
 ***************************************************************************************
 * A bare-bones example file showing the multiplication of the ordinal Gamma_0 by the  *
 * ordinal epsilon_0.                                                                  *
 *                                                                                     *
 * To compile this simple example program (using GCC):                                 *
 *  gcc -Wall example.c por.c core.c arith.c simp.c patterns.c -o example              *
 **************************************************************************************/


/*
 * For sake of minimizing namespace overlap, the user
 * of the arithmetic library needs only include patterns.h,
 * the other header files are only used internally.
 */
#include "patterns.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

int main(void)
{
  pattern *Gamma0, *epsilon0, *product, *simplified;
  node *a,*b,*c,*d;
  node **decomposition;

  printf( "This example program will compute Gamma_0 times epsilon_0.\n" );
  printf( "--------------------------------\n\n" );

  printf( "Initializing basic patterns...\n" );
  patterns_initialize();
  printf( "--------------------------------\n\n" );

  printf( "Creating Gamma_0... ...\n" );
  printf( "(See http://www.xamuel.com/geometric-patterns-of-resemblance/ for a picture of Gamma_0)\n" );

  /*
   * The pattern notating Gamma_0 has four nodes
   */
  Gamma0 = new_pattern( 4 );

  /*
   * This wouldn't happen, but it's here to illustrate error handling:
   */
  if ( !Gamma0 )
  {
    printf( "Creating Gamma_0 failed: %s\n\n", global_pattern_error );
    abort();
  }
  if ( Gamma0 == pattern_too_large )
  {
    printf( "Gamma_0 has too many nodes.\n\n" );
    abort();
  }

  /*
   * Direct some pointers at the nodes of Gamma0
   */
  a = Gamma0->first_node;
  b = a->next;
  c = b->next;
  d = c->next;

  /*
   * Create an arc from node b to node d
   */
  b->less1 = d;

  /*
   * Create an arc from node c to node d
   */
  c->less1 = d;

  /*
   * Decompose node d into the sum c+b.
   * Decompositions are expressed as NULL-terminated
   * strings of node *'s.
   */
  decomposition = malloc( sizeof(node*) * (1+strlen("cb")) );
  decomposition[0] = c;
  decomposition[1] = b;
  decomposition[2] = NULL;
  d->decomposition = decomposition;

  /*
   * Designate b as the pattern's point (so the pattern notates Gamma_0)
   */
  Gamma0->point = b;

  printf( "...Gamma_0 successfully created.\n" );
  printf( "--------------------------------\n\n" );

  printf( "Creating epsilon_0... ...\n" );

  /*
   * epsilon_0 has three nodes
   * (See http://www.xamuel.com/geometric-patterns-of-resemblance/ for picture)
   */
  epsilon0 = new_pattern( 3 );

  if ( !epsilon0 || epsilon0 == pattern_too_large )
  {
    printf( "Failed: %s\n\n", global_pattern_error[0] ? global_pattern_error : "too many nodes" );
    abort();
  }

  /*
   * Get convenient pointers for the nodes
   */
  a = epsilon0->first_node;
  b = a->next;
  c = b->next;

  /*
   * Create an arc from b to c
   */
  b->less1 = c;

  /*
   * Decompose c into c=b+b
   */
  decomposition = malloc( sizeof(node*) * (1+strlen("bb")) );
  decomposition[0] = b;
  decomposition[1] = b;
  decomposition[2] = NULL;
  c->decomposition = decomposition;

  /*
   * Designate b as the pattern's point (so the pattern notates epsilon_0)
   */
  epsilon0->point = b;

  printf( "...epsilon_0 successfully created.\n" );
  printf( "--------------------------------\n\n" );

  printf( "Multiplying Gamma_0 times epsilon_0... ...\n" );
  printf( "--------------------------------\n\n" );

  product = pattern_product( Gamma0, epsilon0 );

  if ( !product || product == pattern_too_large )
  {
    printf( "Failed: %s\n\n", global_pattern_error[0] ? global_pattern_error : "too many nodes" );
    abort();
  }

  printf( "...Multiplication succeeded, yielding a pattern with %d nodes.\n", product->nodes );

  simplified = pattern_simplify( product );

  printf( "That product simplifies to a pattern with %d nodes.\n\n", simplified->nodes );

  return 1;
}
