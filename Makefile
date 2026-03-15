COQMODULE    := CRIS
COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -iname '*.v')

.PHONY: all all-quick

%.vo: %.v
	$(MAKE) -f Makefile.coq $@

%.vos: %.v
	$(MAKE) -f Makefile.coq $@

all: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))
all-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))

theories_files  := $(shell find theories -iname '*.v')
theories: Makefile.coq $(theories_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(theories_files))
theories-quick: Makefile.coq $(theories_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(theories_files))

scheduler_files  := $(shell find scheduler -iname '*.v')
scheduler: Makefile.coq $(scheduler_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(scheduler_files))
scheduler-quick: Makefile.coq $(scheduler_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(scheduler_files))

apc_files  := $(shell find apc -iname '*.v')
apc: Makefile.coq $(apc_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(apc_files))
apc-quick: Makefile.coq $(apc_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(apc_files))

helping_files  := $(shell find helping -iname '*.v')
helping: Makefile.coq $(helping_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(helping_files))
helping-quick: Makefile.coq $(helping_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(helping_files))

extract_files  := $(shell find extract -iname '*.v')
extract: Makefile.coq $(extract_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(extract_files))
extract-quick: Makefile.coq $(extract_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(extract_files))

prophecy_files  := $(shell find prophecy -iname '*.v')
prophecy: Makefile.coq $(prophecy_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(prophecy_files))
prophecy-quick: Makefile.coq $(prophecy_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(prophecy_files))

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
	 echo "-R theories $(COQMODULE)"; \
	 echo "-R scheduler $(COQMODULE)"; \
	 echo "-R apc $(COQMODULE)"; \
	 echo "-R helping $(COQMODULE)"; \
	 echo "-R extract $(COQMODULE)"; \
	 echo "-R prophecy $(COQMODULE)"; \
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
