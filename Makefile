COQMODULE    := CRIS
ROCQ         ?= rocq
COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -iname '*.v')
COQEXTRACT  := extract/ExtrOcamlCRIS.v
COQDIRS      := $(shell find itreeS library theories -type d | sort)
COQDIRS_QUICK := $(addsuffix -quick,$(COQDIRS))

coq_dir_vfiles = $(shell find $(1) -iname '*.v' | sort)
coq_dir_vofiles = $(patsubst %.v,%.vo,$(call coq_dir_vfiles,$(1)))
coq_dir_vosfiles = $(patsubst %.v,%.vos,$(call coq_dir_vfiles,$(1)))

.PHONY: all all-quick $(COQDIRS) $(COQDIRS_QUICK)

%.vo: %.v
	$(MAKE) -f Makefile.coq $@

%.vos: %.v
	$(MAKE) -f Makefile.coq $@

all: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))
all-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))

$(COQDIRS): Makefile.coq
	$(MAKE) -f Makefile.coq $(call coq_dir_vofiles,$@)

$(COQDIRS_QUICK): %-quick: Makefile.coq
	$(MAKE) -f Makefile.coq $(call coq_dir_vosfiles,$*)

extract : Makefile.coq $(COQEXTRACT)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQEXTRACT))
extract-quick: Makefile.coq $(COQEXTRACT)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQEXTRACT))
.PHONY: extract extract-quick

Makefile.coq: Makefile $(COQTHEORIES) $(extract_files)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
	 echo "-Q theories $(COQMODULE)"; \
	 echo "-Q library $(COQMODULE)"; \
	 echo "-Q itreeS ITreeS"; \
	 echo "-Q extract $(COQMODULE)"; \
	 echo $(COQTHEORIES)) > _CoqProject
	$(ROCQ) makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean || true
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -delete || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf
	(cd extract; dune clean)
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
