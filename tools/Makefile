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

# $Id: Makefile 11184 2011-09-07 14:28:24Z xclerc $

include Makefile.shared

# To make custom toplevels

ocamlmktop: ocamlmktop.tpl ../config/Makefile
	sed -e 's|%%BINDIR%%|$(BINDIR)|' ocamlmktop.tpl > ocamlmktop
	chmod +x ocamlmktop

install::
	cp ocamlmktop $(BINDIR)

clean::
	rm -f ocamlmktop
