/*************************************************************/
/*    Reentrant patch by phc                                 */
/*************************************************************/

#include "misc.h"
#include "context.h"
#include "mlvalues.h"
#include "minor_gc.h"
#include "major_gc.h"
#include <stdlib.h>
#include <pthread.h>
#include "gc.h"

int access_to_non_ctx = 0;
pctxt main_ctx = NULL;
int num_th = 0;
pctxt ctxl[MAX_TH];
pthread_t thl[MAX_TH];
static int count_th = 0;
static int count_start = 0;
static pthread_mutex_t phc_mutex_;
static pthread_mutex_t phc_cond_lock;
static pthread_cond_t phc_cond_;
static pthread_key_t phc_ctx_key;
static pthread_mutex_t phc_io_lock;

CAMLexport void (*caml_lock_phc_mutex_fptr)(void) = NULL;
CAMLexport void (*caml_unlock_phc_mutex_fptr)(void) = NULL;
CAMLexport void (*caml_phc_create_thread)(void *(*fn)(void*), void *arg) = NULL;

void init_phc_ctx_key(void){
  pthread_key_create(&phc_ctx_key, NULL);
}

void caml_phc_io_lock(void){
  pthread_mutex_lock(&phc_io_lock);
}

void caml_phc_io_unlock(void){
  pthread_mutex_unlock(&phc_io_lock);
}
CAMLprim value caml_register_ctx(pctxt ctx, value v){
  int i;
  for (i=0;i<num_th;i++)
    if (ctx==ctxl[i])
      thl[i] = pthread_self();
  pthread_setspecific(phc_ctx_key, ctx);
  return Val_unit;
}

pctxt get_ctx(void){
/*  int i;
  pthread_t self;
  self = pthread_self();
  for (i=0;i<num_th;i++)
    if (thl[i]==self)
      break;
  return ctxl[i]; */
  return pthread_getspecific(phc_ctx_key);
}

CAMLprim value caml_get_ctx(value v){
  return Val_int(get_ctx());
}

pctxt create_empty_context(void){
  phc_global_context* res = NULL;
  phc_global_context _zero = {0,};
  struct caml_ref_table _ref_table = { NULL, NULL, NULL, NULL, NULL, 0, 0};
  struct global_root_list _global_roots = { NULL, { NULL, }, 0 };
  sentinel_t _sentinel = {0, Make_header (0, 0, Caml_blue), 0, 0};
  int i;

  res = malloc(sizeof(phc_global_context));
  *res = _zero;

  res->caml_young_ptr     = NULL;
  res->caml_young_limit   = NULL;
  res->caml_young_base    = NULL;
  res->caml_young_start   = NULL;
  res->caml_young_end     = NULL;

  res->count_id = count_th++;
 
  res->caml_ref_table = res->caml_weak_ref_table = _ref_table; 

  res->caml_in_minor_collection = 0;

  res->caml_globals_scanned = 0;
  res->caml_globals_inited = 0;

  res->caml_all_opened_channels = NULL;
  for (i=0; i<Named_value_size; i++)
    res->named_value_table[i] = NULL;

  res->caml_global_roots = _global_roots;
  res->caml_global_roots_young = _global_roots;
  res->caml_global_roots_old = _global_roots;

  res->random_seed = 0;

  res->oldify_todo_list = 0;
  res->final_table      = NULL;
  res->final_old        = 0;
  res->final_young      = 0;
  res->final_size       = 0;
  
  res->to_do_hd                      = NULL;
  res->to_do_tl                      = NULL;

  res->running_finalisation_function = 0;
  res->caml_fl_size_at_phase_change  = 0;

  #ifdef DEBUG
  ctx->major_gc_counter = 0;
  #endif

  res->caml_weak_list_head   = 0;
  res->weak_dummy            = 0;
  res->caml_weak_none        = (value)&(res->weak_dummy);

  res->sentinel         = _sentinel;
  res->fl_head          = ((char *) (&(res->sentinel.first_bp)));
  res->fl_prev          = res->fl_head;
  res->fl_last          = NULL;
  res->caml_fl_merge    = res->fl_prev;
  res->caml_fl_cur_size = 0;
  res->flp_size         = 0;
  res->beyond           = NULL;

  res->caml_stat_minor_words       = 0.0;
  res->caml_stat_promoted_words    = 0.0;
  res->caml_stat_major_words       = 0.0;

  res->caml_stat_minor_collections = 0;
  res->caml_stat_major_collections = 0;
  res->caml_stat_heap_size         = 0;
  res->caml_stat_top_heap_size     = 0;
  res->caml_stat_compactions       = 0;
  res->caml_stat_heap_chunks       = 0;

  res->caml_last_return_address = 1;

  res->compare_stack = res->compare_stack_init;
  res->compare_stack_limit = res->compare_stack_init + COMPARE_STACK_INIT_SIZE;

  strcpy(res->array_bound_error_msg.data, BOUND_MSG);

  if (main_ctx==NULL){
    main_ctx = res;
    pthread_mutex_init(&phc_mutex_, NULL);
    pthread_mutex_init(&phc_cond_lock, NULL);
    pthread_mutex_init(&phc_io_lock, NULL);
    pthread_cond_init(&phc_cond_, NULL);
  }
  return res;
}

CAMLprim value caml_lock_phc_mutex(pctxt ctx, value v){
  pthread_mutex_lock(&phc_mutex_);
  return Val_unit;
}

CAMLprim value caml_unlock_phc_mutex(pctxt ctx, value v){
  pthread_mutex_unlock(&phc_mutex_);
  return Val_unit;
}

void caml_enter_cond_lock(pctxt ctx){
  pthread_mutex_lock(&phc_mutex_);
  main_ctx = ctx;
  sync_with_context(ctx); 
}

CAMLprim value caml_wait_counter(pctxt ctx, value v){
// increase phc_count and wait for it to reach num_th 
// thus this fun blocks until it is OK to start parallel threading
// assumption :  pthread_mutex_lock(phc_mutex_);
  count_start++;
  pthread_mutex_unlock(&phc_mutex_);

  pthread_mutex_lock(&phc_cond_lock);
  while (count_start < num_th)
    pthread_cond_wait(&phc_cond_, &phc_cond_lock);
  pthread_cond_signal(&phc_cond_);
  pthread_mutex_unlock(&phc_cond_lock);
}

CAMLprim value caml_context_id(pctxt ctx, value v){
  return Val_int(ctx->count_id);
}

CAMLprim value caml_context_num(pctxt ctx, value v){
  return Val_int(count_th);
}

CAMLprim value caml_print_context(pctxt ctx){
  printf("caml_young_ptr     : %p\n", (void*)ctx->caml_young_ptr);
  printf("caml_young_limit   : %p\n", (void*)ctx->caml_young_limit);
  printf("caml_young_base    : %p\n", (void*)ctx->caml_young_base);
  printf("caml_young_start   : %p\n", (void*)ctx->caml_young_start);
  printf("caml_young_end     : %p\n", (void*)ctx->caml_young_end);
  return Val_unit;
}

void print_inconsis(char *name, value v1, value v2){
  printf("%s %p %p\n", name, v1, v2);
}

void sync_with_global_vars(pctxt ctx){
  if (num_th==0){

  if (ctx->caml_young_ptr!=caml_young_ptr)
    print_inconsis("sync_with_global_vars caml_young_ptr",
           ctx->caml_young_ptr, caml_young_ptr);
  if (ctx->caml_young_limit!=caml_young_limit)
    print_inconsis("sync_with_global_vars caml_young_limit",
           ctx->caml_young_limit, caml_young_limit);
  if (ctx->caml_young_base!=caml_young_base)
    print_inconsis("sync_with_global_vars caml_young_base",
           ctx->caml_young_base, caml_young_base);
  if (ctx->caml_young_start!=caml_young_start)
    print_inconsis("sync_with_global_vars caml_young_start",
           ctx->caml_young_start, caml_young_start);
  if (ctx->caml_young_end!=caml_young_end)
    print_inconsis("sync_with_global_vars caml_young_end",
           ctx->caml_young_end, caml_young_end);

  ctx->caml_young_ptr     = caml_young_ptr;
  ctx->caml_young_limit   = caml_young_limit;
  ctx->caml_young_base    = caml_young_base;
  ctx->caml_young_start   = caml_young_start;
  ctx->caml_young_end     = caml_young_end;

  }
}

void sync_with_context(pctxt ctx){
  if (num_th==0){

  if (ctx->caml_young_ptr!=caml_young_ptr)
    print_inconsis("sync_with_context caml_young_ptr",
           ctx->caml_young_ptr, caml_young_ptr);
  if (ctx->caml_young_limit!=caml_young_limit)
    print_inconsis("sync_with_context caml_young_limit",
           ctx->caml_young_limit, caml_young_limit);
  if (ctx->caml_young_base!=caml_young_base)
    print_inconsis("sync_with_context caml_young_base",
           ctx->caml_young_base, caml_young_base);
  if (ctx->caml_young_start!=caml_young_start)
    print_inconsis("sync_with_context caml_young_start",
           ctx->caml_young_start, caml_young_start);
  if (ctx->caml_young_end!=caml_young_end)
    print_inconsis("sync_with_context caml_young_end",
           ctx->caml_young_end, caml_young_end);

  caml_young_ptr     = ctx->caml_young_ptr; 
  caml_young_limit   = ctx->caml_young_limit;
  caml_young_base    = ctx->caml_young_base;
  caml_young_start   = ctx->caml_young_start;  
  caml_young_end     = ctx->caml_young_end;

  }
}

void destroy_context(pctxt ctxt){
  free(ctxt);
}

char* tag_string(int tag){
  if (Forward_tag==tag)
    return "Forward_tag";
  if (Lazy_tag==tag)
    return "Lazy_tag";
  if (Object_tag==tag)
    return "Object_tag";
  if (Infix_tag==tag)
    return "Infix_tag";
  if (Closure_tag==tag)
    return "Closure_tag";
  if (String_tag==tag)
    return "String_tag";
  if (Double_tag==tag)
    return "Double_tag";
  if (Double_array_tag==tag)
    return "Double_array_tag";
  if (Custom_tag==tag)
    return "Custom_tag";
  return "normal tag";
}

char *color_string(int col){
  if (col==Caml_black) return "Black";
  if (col==Caml_gray)  return "Gray ";
  if (col==Caml_white) return "White";
  if (col==Caml_blue)  return "Blue ";
  return "Unknown";
}

void traverse_all_blocks(pctxt ctx){
  char *chunk, *chend;
  char *block;
  header_t hd;
  value v;
  int wosize, col, tag;
  int i;
  
  printf("traverse_all_blocks young heap %p %p\n", ctx->caml_young_ptr, ctx->caml_young_end);
  
  block = ctx->caml_young_ptr;
  while (block < ctx->caml_young_end){
    v = Val_hp(block);
    hd = Hd_val(v);
    tag = Tag_hd(hd);
    wosize = Wosize_hd(hd);

    printf("young block ptr = %p tag = %3d wosize = %3d (%s)\n",
             block, tag, wosize,tag_string(tag));
    for (i=0; i<10 && i<wosize-1; i++)
      printf("%02p ", *(value*)(v+i));
    printf("\n");
    
    block += Bhsize_wosize(wosize);
  }
  
  printf("traverse_all_blocks old heap %p %d\n", ctx->caml_heap_start, Chunk_size(ctx->caml_heap_start));
  chunk = ctx->caml_heap_start;
  while (chunk!=NULL){
    chend = chunk + Chunk_size(chunk);
    block = chunk;
    while (block < chend){
      v = Val_hp(block);
      hd = Hd_val(v);
      tag = Tag_hd(hd);
      col = Color_hd(hd);
      wosize = Wosize_hd(hd);
      
      if (col!=Caml_blue){
        printf("old block ptr = %p tag = %3d color = %s  wosize = %3d (%s)\n",
                 block, tag, color_string(col), wosize, tag_string(tag));
        for (i=0; i<10 && i<wosize-1; i++)
          printf("%02p ", *(value*)(v+i));
        printf("\n");
      }
      block += Bhsize_wosize(wosize);
    }
    chunk = Chunk_next (chunk);
  }
}
