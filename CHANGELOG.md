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
- add a goal-local fast path to `solve_msk` while preserving its existing
  fallback
- add a root-`own` fast path to `solve_sl_red` while preserving its existing
  fallback
- make `aUnfoldS` and `aUnfoldT` perform only the selected structural unfold;
  callers now request `cNormS` or `cNormT` explicitly when needed
- make certificate-based function lookup expose module aliases structurally
  and fail fast on unsupported map combinators before the `simpl_map`
  fallback; custom lookup instances must also be registered in the
  `fnsem_lookup` hint database
- restore certificate lookup for dependent function-body maps in the opaque
  `fnsem_lookup` hint database
- keep recursive function-lookup certificate search inside its opaque hint
  database so unsupported module maps reach the `simpl_map` fallback
- replace Helping's client-visible request state with a resource-only
  `HelpPend`/`HelpDone` protocol and make `HelpingOn.try_run` request-ID-only
- add nested `IstHelp` transport and `helping_main_filtered` for client
  composition
- make `sYields` require progress and `sYield` introduce fresh continuation
  states atomically
- add an Iris-compatible proof mode for `BiProset` entailments, with a third
  tensor context and the `jStartProof`, `jStopProof`, `jIntros`, `jDestruct`,
  `jPoseProof`, `jAssert`, `jSplitL`, `jSplitR`, `jApply`, `jFrame`, and
  `jUnitIntro` tactics
- Remove legacy tactics for `ctx_refines` composition. (`ctxr_refl`,
  `ctxr_transL`, `ctxr_transR`, `ctxr_norm`, `ctxr_swap`, `ctxr_rotate`,
  `ctxr_drop`)
- Rename `lsim_mod` to `lsim_lmod`. Add new `lsim_mod` and `gsim_mod`.
  Restate `gsim_closed_adequacy` and `lsim_closed_adequacy` using `lsim_mod`
  and `gsim_mod`.
- Redefine `sim_fsem`, `ISim.sim_fun`, and `ISim.t` as iProps.
- Replace explicit source/target module-state arguments in `msim`, `wsim`, and
  `isim` with separation-logic state ownership. The new `StatePredicate`
  resource provides `points_to_src`/`points_to_tgt` and
  `uninit_src`/`uninit_tgt`, with `stateGpreS` carried by `crisG` and `stateGS`
  allocated by adequacy.
- Add `IstEq M` for module-scoped state equality and strengthen the
  `ISim_reflL`/`ISim_reflR` interfaces to take the user initializer and selected
  function simulations directly as Iris premises.
- Add `cGetT`, `cGetS`, `cPutT`, `cPutS` tactics for module state reasoning.
- Strengthen `Own_bupd_split` with validity of the split resource.
- `CRIS.lib.AList` is no longer exported by other modules.

## 2026-07-22

### Added

- Published the first versioned release of CRIS.
- Added opam package metadata and installation through `./configure`.
