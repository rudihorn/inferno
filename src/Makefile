.PHONY: all clean check install uninstall

OCAMLBUILD := ocamlbuild -classic-display -use-ocamlfind -cflags "-g" -lflags "-g"

all:
	$(OCAMLBUILD) -I lib inferno.cma inferno.cmxa inferno.cmxs

check:
	$(OCAMLBUILD) -I lib -I client client/Main.native
	time ./Main.native
	$(OCAMLBUILD) -I lib -I client test/TestUnionFind.native
	time ./TestUnionFind.native

clean:
	rm -f {lib,client,test}/*~ *~
	rm -rf _build

EXPORTED_SOURCES := $(wildcard lib/*.mli)

install: uninstall
	@ if [ x$(PREFIX) = x ]; then                                                           \
	  echo "Selecting OPAM based install.";                                                 \
	  echo "Specify PREFIX=... for system-wide install.";                                   \
	  ocamlfind install inferno META _build/lib/inferno.cm* $(EXPORTED_SOURCES);                  \
	else                                                                                    \
	  echo "Selecting system-wide install. PREFIX is $(PREFIX)";                            \
	  ocamlfind install -destdir $(PREFIX)/lib inferno META $(EXPORTED_SOURCES)             \
            _build/lib/inferno.cm* ;                                                                  \
	fi

uninstall:
	@ if [ x$(PREFIX) = x ]; then                                                           \
	  echo "Selecting OPAM based install.";                                                 \
	  echo "Specify PREFIX=... for system-wide install.";                                   \
	  ocamlfind remove inferno;                                                             \
	else                                                                                    \
	  echo "Selecting system-wide install. PREFIX is $(PREFIX)";                            \
	  ocamlfind remove -destdir $(PREFIX)/lib inferno;                                      \
	fi
