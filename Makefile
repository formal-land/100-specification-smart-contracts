.PHONY: default all clean clean-util distclean

VFILES := $(shell find -L . -name "*.v" | sort)

default: all

# We use the '@' to avoid displaying this command as the parameters list is
# very long.
CoqMakefile: $(VFILES)
	@coq_makefile -f _CoqProject -o $@ $(VFILES)

MAKECOQ := +$(MAKE) -f CoqMakefile

%.vo: CoqMakefile %.v
	$(MAKECOQ) $@

all: CoqMakefile
	$(MAKECOQ) all

clean-coq: CoqMakefile
	$(MAKECOQ) clean

clean-util:
	rm -f *CoqMakefile*

clean: clean-coq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean
