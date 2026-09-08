# Head-normalization benchmark

Measured on 2026-09-08 with Rocq 9.0.1, OCaml 4.14.3, and an Intel
Core i7-12700H. These are warm tactic microbenchmarks, not whole-build timings.

## Implementation

`HNorm.v` retains the goal-driven, typeclass-based driver:

- Reuse `simpl` only for exact structural children of the initially simplified,
  evar-free input in an evar-free local environment. Expansion, constructed
  children, and continued reductions invalidate this information.
- Use `simple notypeclasses refine` with explicit output-hole shelving and
  record construction, avoiding ordinary refinement's dependency scans.
- Preserve typeclass conversion, local instances, existential variables,
  head-only normalization, and the existing public tactic entrypoints.

Compact goal-driven equality proofs and a term-producing CPS prototype were
also tested. The former substantially increased tactic time; the latter did
not clearly outperform the simpler driver. Neither is retained.

The Elpi column uses the existing, unchanged `hnorm_itr_elpi` implementation.

## Method

`HNormBench.v` embeds the original tactic from commit `51699e56`, renamed
but otherwise unchanged. The baseline does not call the optimized driver.

All three implementations run an untimed 200-step warmup before measurements.
Each measured proof also has a same-tactic, same-goal warmup. Input construction
is outside `Time`. Each case is measured in original/current/Elpi order and
again in Elpi/current/original order. The table gives the median of six samples per
implementation, from three serial compiler runs. No project build, live proof
session, or other heavy job ran concurrently.

Without the initial shared warmup, an early 50-step sample took about 0.24s
instead of 0.11–0.12s. Swapping that pair moved the slowdown to the baseline
(0.248s baseline versus 0.105s optimized), demonstrating an order effect.
The shared warmup removes this artifact in the final runs.

## Results

Wall-clock seconds; percentages compare optimized Ltac with original Ltac
using unrounded medians. All three columns were freshly measured together.

| Case | Original Ltac | Optimized Ltac | Elpi | Less Ltac time |
| --- | ---: | ---: | ---: | ---: |
| `ret_chain 10` | 0.0175 | 0.0170 | 0.0075 | 3% |
| `ret_chain 50` | 0.1135 | 0.1075 | 0.0625 | 5% |
| `ret_chain 100` | 0.2990 | 0.2755 | 0.1700 | 8% |
| `map_chain 50` | 0.1310 | 0.1160 | 0.0720 | 11% |
| `map_chain 100` | 0.3525 | 0.2980 | 0.2350 | 15% |
| `map_chain 200` | 0.9530 | 0.8310 | 0.8095 | 13% |
| `mask_chain 5` | 0.0050 | 0.0040 | 0.0030 | — |

The shortest cases are close to timer resolution; their small differences
should not be overinterpreted. Larger return/map cases use 8–15% less Ltac
tactic time. Elpi is faster on these inputs, but its advantage over optimized
Ltac narrows to about 3% at `map_chain 200`.

For comparison, the earlier Ltac-only run measured `map_chain 200` at
0.9975s original versus 0.7925s optimized. The three-way run has different
imports and heap history; its samples are not mixed with that earlier batch.

`Qed` is timed separately and includes both the per-goal warmup proof and
the measured proof:

| Case | Original Ltac Qed | Optimized Ltac Qed | Elpi Qed |
| --- | ---: | ---: | ---: |
| `ret_chain 100` | 0.1170 | 0.1020 | 0.0865 |
| `map_chain 100` | 0.2065 | 0.1650 | 0.1145 |
| `map_chain 200` | 0.7090 | 0.5870 | 0.3035 |

## Reproduce

With imported dependencies up to date, run from the repository root:

```sh
rocq compile -w -notation-incompatible-prefix,-ambiguous-paths \
  -Q theories CRIS -Q library CRIS -Q itreeS ITreeS \
  theories/proofmode/HNormBench.v
```

Repeat serially for additional samples. Keep normal Rocq GC settings and
do not overlap measurements with builds or other heavy work. Direct compilation
is intentional: `make` skips an up-to-date benchmark.
