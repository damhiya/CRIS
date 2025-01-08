COQMODULE    := CRIS
COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -iname '*.v')

.PHONY: all proof proof-quick graph

all:
	$(MAKE) proof

graph:
		sh make_graph.sh

%.vo: %.v
	$(MAKE) -f Makefile.coq $@

%.vos: %.v
	$(MAKE) -f Makefile.coq $@

proof-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))

proof: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
				 echo "-R lib $(COQMODULE)"; \
         echo "-R common $(COQMODULE)"; \
         echo "-R modules $(COQMODULE)"; \
         echo "-R simulations $(COQMODULE)"; \
         echo "-R cancellation $(COQMODULE)"; \
         echo "-R iris_system $(COQMODULE)"; \
         echo "-R imp_system $(COQMODULE)"; \
         echo "-R examples $(COQMODULE)"; \
         echo "-R extract $(COQMODULE)"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean || true
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -delete || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf
.PHONY: clean

# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

builddep: builddep-opamfiles
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install $(OPAMFLAGS) $(BUILDDEPFILES)
.PHONY: builddep
