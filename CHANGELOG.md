# Changelog

This file records notable changes to CRIS starting with the `v2026-07-22`
release.

## Unreleased

- rename: `closed_adequacy` -> `ISim_closed_adequacy`
- add `gsim_closed_adequacy`, `lsim_closed_adequacy`
- move `theories/simulations/filter` to `theories/filter`
- Add `Beh : Mod.t -> Tr.t -> iProp Σ`
- Redefine `refines` using `Beh`. This new definition is equivalent to the old one.
- change extraction setting of `SchI.choose_index` in `ExtrOcamlCRIS.v`
- optimize function lookup and post-inline normalization in `cStartFunSim`
  and `cInlineS`/`cInlineT`
- make certificate-based function lookup expose module aliases structurally
  and fail fast on unsupported map combinators before the `simpl_map`
  fallback; custom lookup instances must also be registered in the
  `fnsem_lookup` hint database
- replace Helping's client-visible request state with a resource-only
  `HelpPend`/`HelpDone` protocol and make `HelpingOn.try_run` request-ID-only
- add nested `IstHelp` transport and `helping_main_filtered` for client
  composition
- make `sYields` require progress and `sYield` introduce fresh continuation
  states atomically

## 2026-07-22

### Added

- Published the first versioned release of CRIS.
- Added opam package metadata and installation through `./configure`.
