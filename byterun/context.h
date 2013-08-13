/*************************************************************/
/*    Reentrant patch by phc                                 */
/*************************************************************/

#ifndef PHC_CONTEXT_H
#define PHC_CONTEXT_H

#include "misc.h"
#include "mlvalues.h"

#define NULL_CTX 0
#define MAX_TH 16

// finalise.c
struct final {
  value fun;
  value val;
  int offset;
};

struct to_do {
  struct to_do *next;
  int size;
  struct final item[1];  /* variable size */
};

// globroots.c
struct global_root {
  value * root;                    /* the address of the root */
  struct global_root * forward[1]; /* variable-length array */
};

#define NUM_LEVELS 17

struct global_root_list {
  value * root;                 /* dummy value for layout compatibility */
  struct global_root * forward[NUM_LEVELS]; /* forward chaining */
  int level;                    /* max used level */
};

struct caml_ref_table {
  value **base;
  value **end;
  value **threshold;
  value **ptr;
  value **limit;
  asize_t size;
  asize_t reserve;
};

#ifndef IO_BUFFER_SIZE
#define IO_BUFFER_SIZE 65536
#endif

#if defined(_WIN32)
typedef __int64 file_offset;
extern __int64 _lseeki64(int, __int64, int);
#define lseek(fd,d,m) _lseeki64(fd,d,m)
#elif defined(HAS_OFF_T)
#include <sys/types.h>
typedef off_t file_offset;
#else
typedef long file_offset;
#endif

// callback.c
#define Named_value_size 13

struct named_value {
  value val;
  struct named_value * next;
  char name[1];
};

struct channel {
  int fd;                       /* Unix file descriptor */
  file_offset offset;           /* Absolute position of fd in the file */
  char * end;                   /* Physical end of the buffer */
  char * curr;                  /* Current position in the buffer */
  char * max;                   /* Logical end of the buffer (for input) */
  void * mutex;                 /* Placeholder for mutex (for systhreads) */
  struct channel * next, * prev;/* Double chaining of channels (flush_all) */
  int revealed;                 /* For Cash only */
  int old_revealed;             /* For Cash only */
  int refcount;                 /* For flush_all and for Cash */
  int flags;                    /* Bitfield */
  char buff[IO_BUFFER_SIZE];    /* The buffer itself */
};

// freelist.c

/* The free-list is kept sorted by increasing addresses.
   This makes the merging of adjacent free blocks possible.
   (See [caml_fl_merge_block].)
*/

typedef struct {
  char *next_bp;   /* Pointer to the first byte of the next block. */
} block;

/* The sentinel can be located anywhere in memory, but it must not be
   adjacent to any heap object. */
typedef struct sentinel_t{
  value filler1; /* Make sure the sentinel is never adjacent to any block. */
  header_t h;
  value first_bp;
  value filler2; /* Make sure the sentinel is never adjacent to any block. */
} sentinel_t;

#define FLP_MAX 1000

typedef struct phc_global_context {
  char *caml_young_ptr;
  char *caml_young_limit;
  char *caml_young_base;
  char *caml_young_start;
  char *caml_young_end;

  intnat caml_globals;       // 40
  int caml_globals_len;

  intnat caml_globals_scanned;
  intnat caml_globals_inited;

  int count_id;

  struct caml_ref_table caml_ref_table;
  struct caml_ref_table caml_weak_ref_table;

  uint32 random_seed;
  int caml_in_minor_collection;

  struct channel *caml_all_opened_channels;
  struct named_value * named_value_table[Named_value_size];

  struct global_root_list caml_global_roots;
                  /* mutable roots, don't know whether old or young */
  struct global_root_list caml_global_roots_young;
                 /* generational roots pointing to minor or major heap */
  struct global_root_list caml_global_roots_old;
                  /* generational roots pointing to major heap */

  value oldify_todo_list;

  struct final *final_table;
  value final_old, final_young, final_size;

  struct to_do *to_do_hd;
  struct to_do *to_do_tl;

  int running_finalisation_function;

  asize_t caml_minor_heap_size;
  // major_gc.c
  uintnat caml_percent_free;
  uintnat caml_major_heap_increment;
  char *caml_heap_start;
  char *caml_gc_sweep_hp;
  int caml_gc_phase;        /* always Phase_mark, Phase_sweep, or Phase_idle */
  value *gray_vals;
  value *gray_vals_cur, *gray_vals_end;
  asize_t gray_vals_size;
  int heap_is_pure;   /* The heap is pure if the only gray objects
                                below [markhp] are also in [gray_vals]. */
  uintnat caml_allocated_words;
  uintnat caml_dependent_size, caml_dependent_allocated;
  double caml_extra_heap_resources;
  uintnat caml_fl_size_at_phase_change;
  
  char *markhp, *chunk, *limit;
  
  int caml_gc_subphase;     /* Subphase_{main,weak1,weak2,final} */
  value *weak_prev;
  
  #ifdef DEBUG
  unsigned long major_gc_counter; // phc todo = 0;
  #endif

  // weak.c
  value caml_weak_list_head;
  value weak_dummy;
  value caml_weak_none;

  // freelist.c
  sentinel_t sentinel; 
  
  char *fl_prev; /* Current allocation pointer.         */
  /* Last block in the list.  Only valid just after [caml_fl_allocate] returns NULL. */
  char *fl_last; 
  /* Current insertion pointer.  Managed jointly with [sweep_slice]. */
  char *caml_fl_merge; 
  /* Number of words in the free list, including headers but not fragments. */
  asize_t caml_fl_cur_size; 
  char *flp [FLP_MAX];
  int flp_size; 
  char *beyond; 

  // gc_ctrl.c
  double caml_stat_minor_words;
  double caml_stat_promoted_words;
  double caml_stat_major_words;

  intnat caml_stat_minor_collections;
  intnat caml_stat_major_collections;
  intnat caml_stat_heap_size;
  intnat caml_stat_top_heap_size;
  intnat caml_stat_compactions;
  intnat caml_stat_heap_chunks;


} phc_global_context;

typedef phc_global_context *pctxt;

// phc - main_ctx valid only in non-parallel mode
// inited once by startup 
// use main_ctx to call a reentrant function inside a normal function
extern int access_to_non_ctx;
extern pctxt main_ctx;
extern int num_th;

extern pctxt create_empty_context(void);
extern void destroy_context(pctxt);
extern void sync_with_global_vars(pctxt ctx);
extern void sync_with_context(pctxt ctx);

CAMLextern void (*caml_lock_phc_mutex_fptr)(void);
CAMLextern void (*caml_unlock_phc_mutex_fptr)(void);

void caml_enter_cond_lock(pctxt ctx);
CAMLextern void (*caml_phc_create_thread)(void *(*fn)(void*), void *arg);


#endif
