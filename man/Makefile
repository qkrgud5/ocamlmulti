#########################################################################
#                                                                       #
#                                 OCaml                                 #
#                                                                       #
#            Xavier Leroy, projet Cristal, INRIA Rocquencourt           #
#                                                                       #
#   Copyright 1999 Institut National de Recherche en Informatique et    #
#   en Automatique.  All rights reserved.  This file is distributed     #
#   under the terms of the Q Public License version 1.0.                #
#                                                                       #
#########################################################################

# $Id: Makefile 12246 2012-03-16 15:53:07Z doligez $

include ../config/Makefile

DIR=$(MANDIR)/man$(MANEXT)

install:
	for i in *.m; do cp $$i $(DIR)/`basename $$i .m`.$(MANEXT); done
	echo '.so man$(MANEXT)/ocamlc.$(MANEXT)' > $(DIR)/ocamlc.opt.$(MANEXT)
	echo '.so man$(MANEXT)/ocamlopt.$(MANEXT)' > $(DIR)/ocamlopt.opt.$(MANEXT)
	echo '.so man$(MANEXT)/ocamlcp.$(MANEXT)' > $(DIR)/ocamloptp.$(MANEXT)
