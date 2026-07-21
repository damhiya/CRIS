#!/bin/bash

dune clean
find coq_extracted -maxdepth 1 -type f ! -name 'dune' -delete
find . -maxdepth 1 -type f -name '*.vo*' -and ! -name 'ExtrOcamlCRIS.*' -delete
find . -maxdepth 1 -type f -name '.*.aux' -and ! -name '.ExtrOcamlCRIS.aux' -delete
find . -maxdepth 1 -type f -name '*.glob' -and ! -name 'ExtrOcamlCRIS.glob' -delete
