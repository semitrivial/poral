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
 * macro.h                                                                             *
 ***************************************************************************************
 * Convenient macros to save coding time and improve code readability.                 *
 *                                                                                     *
 * Throughout, the "do ... while(0)" pattern is used to endow the macros with          *
 *  function-like syntax.                                                              *
 **************************************************************************************/

/*
 * Macro to swap A and B, given temporary storage C
 */
#define SWAP(a,b,c)\
do\
{\
   (c)=(a);\
   (a)=(b);\
   (b)=(c);\
} while (0)

/*
 * Memory allocation macro
 */
#define CREATE(result, type, number)\
do\
{\
    if (!((result) = (type *) calloc ((number), sizeof(type))))\
    {\
        fprintf(stderr, "Malloc failure at %s:%d\n", __FILE__, __LINE__ );\
        abort();\
    }\
} while(0)

/*
 * Add object to doubly-linked list
 */
#define LINK(link, first, last, next, prev)\
do\
{\
   if ( !(first) )\
   {\
      (first) = (link);\
      (last) = (link);\
   }\
   else\
      (last)->next = (link);\
   (link)->next = NULL;\
   if (first == link)\
      (link)->prev = NULL;\
   else\
      (link)->prev = (last);\
   (last) = (link);\
} while(0)

/*
 * Remove object from doubly-linked list
 */
#define UNLINK(link, first, last, next, prev)\
do\
{\
        if ( !(link)->prev )\
        {\
         (first) = (link)->next;\
           if ((first))\
              (first)->prev = NULL;\
        }\
        else\
        {\
         (link)->prev->next = (link)->next;\
        }\
        if ( !(link)->next )\
        {\
         (last) = (link)->prev;\
           if ((last))\
              (last)->next = NULL;\
        }\
        else\
        {\
         (link)->next->prev = (link)->prev;\
        }\
} while(0)

/*
 * Insert object into doubly-linked list
 */
#define INSERT(link, insert, first, next, prev)\
do\
{\
   (link)->prev = (insert)->prev;\
   if ( !(insert)->prev )\
      (first) = (link);\
   else\
      (insert)->prev->next = (link);\
   (insert)->prev = (link);\
   (link)->next = (insert);\
} while(0)

/*
 * Simple error reporting for patterns.c
 */
#define PTN_ERROR( errmsg ) do\
{\
  strncpy( global_pattern_error, errmsg, PATTERN_ERROR_BUFSIZE-1 );\
  global_pattern_error[PATTERN_ERROR_BUFSIZE] = '\0';\
  return NULL;\
} while(0)

#define PTN_ERRORF( errmsg, param ) do\
{\
  snprintf( global_pattern_error, PATTERN_ERROR_BUFSIZE-1, errmsg, param );\
  global_pattern_error[PATTERN_ERROR_BUFSIZE] = '\0';\
  return NULL;\
} while(0)
