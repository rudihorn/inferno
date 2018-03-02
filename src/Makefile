.PHONY: all clean main

OCAMLBUILD := ocamlbuild -classic-display -use-ocamlfind -use-menhir -cflags "-g" -lflags "-g"

all:
# First build the library alone, so as to make sure it is stand-alone.
	$(OCAMLBUILD) -build-dir _build1 -I lib                   SolverHi.native
# Then, build the sample client.
	$(OCAMLBUILD) -build-dir _build2 -I lib -I client         Main.native
# Also build the miscellaneous tests that we may have on the side.
	$(OCAMLBUILD) -build-dir _build3 -I lib -I client -I test TestUnionFind.native

main: all
	time _build2/client/Main.native

clean:
	rm -f {lib,client,test}/*~
	rm -rf _build1 _build2 _build3
