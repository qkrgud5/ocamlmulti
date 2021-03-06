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

/* $Id: compact.h 11156 2011-07-27 14:17:02Z doligez $ */

#ifndef CAML_COMPACT_H
#define CAML_COMPACT_H


#include "config.h"
#include "misc.h"

extern void caml_compact_heap (void);
extern void caml_compact_heap_r (pctxt);
extern void caml_compact_heap_maybe (void);
extern void caml_compact_heap_maybe_r (pctxt);


#endif /* CAML_COMPACT_H */
