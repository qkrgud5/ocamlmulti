/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*             Damien Doligez, projet Para, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id: gc_ctrl.h 11156 2011-07-27 14:17:02Z doligez $ */

#ifndef CAML_GC_CTRL_H
#define CAML_GC_CTRL_H

#include "misc.h"
#include "context.h"

extern double
     caml_stat_minor_words,
     caml_stat_promoted_words,
     caml_stat_major_words;

extern intnat
     caml_stat_minor_collections,
     caml_stat_major_collections,
     caml_stat_heap_size,
     caml_stat_top_heap_size,
     caml_stat_compactions,
     caml_stat_heap_chunks;

void caml_init_gc (uintnat, uintnat, uintnat,
                   uintnat, uintnat);

void caml_init_gc_r (pctxt, uintnat, uintnat, uintnat,
                   uintnat, uintnat);


#ifdef DEBUG
void caml_heap_check (void);
#endif

#endif /* CAML_GC_CTRL_H */
