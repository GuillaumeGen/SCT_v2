# Current version number of Dedukti.
VERSION = devel

# Compile with "make Q=" to display the commands that are run.
Q = @


.PHONY: all
all: sct

#### Compilation of SCT ########################################

sct: sct.native

sct.native: $(wildcard src/*.ml src/*.mli)
	@echo "[OPT] $@"
	$(Q)ocamlbuild -quiet -package dedukti -use-ocamlfind src/sct.native

clean:
	$(Q)ocamlbuild -quiet -clean

distclean: clean
	$(Q)find -name "*~" -exec rm {} \;
	$(Q)rm -f kernel/version.ml
	$(Q)rm -f META
