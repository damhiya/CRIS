#!/bin/bash

DEPS=$(cd ../; coqdep -R theories CRIS -R scheduler CRIS -R extract CRIS extract/Example0.v | grep -oE '[^ ]+\.vo' | grep -v 'extract/Example0\.vo')

find coq_extracted -maxdepth 1 -type f ! -name 'dune' -delete
(cd ../; make -f Makefile.coq $DEPS; coqc -R theories CRIS -R scheduler CRIS -R extract CRIS extract/Example0.v)
dune build
dune exec ./bin/main.exe
