# Changelog

This file records notable changes to CRIS starting with the `v2026-07-22`
release.

## Unreleased

- rename: `closed_adequacy` -> `ISim_closed_adequacy`
- add `gsim_closed_adequacy`, `lsim_closed_adequacy`
- move `theories/simulations/filter` to `theories/filter`
- change extraction setting of `SchI.choose_index` in `ExtrOcamlCRIS.v`
- optimize function lookup and post-inline normalization in `cStartFunSim`
  and `cInlineS`/`cInlineT`

## 2026-07-22

### Added

- Published the first versioned release of CRIS.
- Added opam package metadata and installation through `./configure`.
