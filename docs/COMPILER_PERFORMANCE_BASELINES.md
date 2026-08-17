# Compiler performance baselines

These measurements cover complete checks through the canonical module pipeline.
They are diagnostic baselines, not CI timeouts: compare like-for-like hardware
and investigate a repeatable result outside the tolerant band before treating
it as a regression.

## Reproduce

```sh
MIX_ENV=test mix cure.bench.interfaces --warm-iterations 3
```

The cold sample starts without a checked-interface cache. Each warm sample runs
the identical source universe against the cache published by the preceding run.
The report includes exact rebuilt-module lists, top-level phase timings, SCC
component timings, and the slowest declaration/stage timings. The CLI prints
the top 20 entries in each ranking by default; use `--top N` to change that
without discarding the complete timing lists retained by the benchmark API. A
warm sample is cache evidence only when `rebuilt=0`.

Pass an explicit list of files only when it is a dependency-complete compilation
universe. A lone module that imports another source is intentionally rejected by
the canonical graph unless its dependency interface is supplied by the caller.

## 2026-08-09 canonical-pipeline baseline

Environment: Apple M1 Pro, macOS arm64, Erlang/OTP 29, Elixir 1.20.1.

| Measurement | Baseline | Investigation band |
|---|---:|---:|
| all 75 sources, cold total | 54.629 s | 27–110 s |
| cold manifest | 0.376 s | 0.2–0.8 s |
| cold expansion | 6.649 s | 3–14 s |
| cold module checking | 47.536 s | 24–96 s |
| all 75 sources, warm total | 3.211 s | 1.5–7 s |
| warm expansion | 2.642 s | 1.2–5.5 s |
| warm module checking | 0.244 s | 0.1–0.6 s |

The cold run rebuilt all 75 modules; the warm run rebuilt none. The dominant
cold component was `Std.Actor` at 36.121 s, followed by `Std.Bool` at 3.886 s,
`Std.Regex` at 1.661 s, and `Std.Fsm` at 0.671 s. The legal
`Std.Char`/`Std.Literal`/`Std.String` cycle is reported as one SCC component.

`Std.Actor` is therefore the first candidate for measured decomposition. A
split should preserve an acyclic module boundary and must be benchmarked again;
source line count alone is not sufficient justification.

For comparison, before shape-directed zonking and canonical-name interning, the
same cold check measured 93.402 s with `Std.Actor` at 71.349 s. Those numbers are
diagnostic evidence from the same machine, not a second supported baseline.

## 2026-08-10 declaration-stage profile

On the same machine, a cold run after adding declaration-stage timing measured
41.193 s overall, with `Std.Actor` accounting for 33.110 s. A no-rebuild warm
sample measured 1.351 s. The dominant declarations and their typed-elaboration
times were:

| Declaration | Typed elaboration |
|---|---:|
| `emit_actor_dep_call_parts` | 7.590 s |
| `derive_behavior_family` | 7.455 s |
| `emit_actor_call_parts` | 6.913 s |
| `emit_actor_parts_poly` | 3.322 s |
| `emit_actor_parts_aliased_raw` | 2.679 s |
| `emit_actor_parts_aliased` | 2.525 s |

The parsed `Std.Actor` body contains hundreds, not millions, of authored calls;
profiling therefore identifies repeated typed elaboration as the remaining
cost, rather than parsing, expansion size, interface publication, or totality
certification. This profile is the baseline for the next elaborator change.

## 2026-08-10 post-CharacterLiteral baseline

Environment: Apple M1 Pro, macOS arm64, Erlang/OTP 29, Elixir 1.20.1. This run
is after `674f9772`, which prevents decoded string-literal descriptor characters
from recursively re-entering `ExpressibleByCharacterLiteral`.

| Measurement | Observed |
|---|---:|
| all 75 sources, cold total | 12.351 s |
| cold `Std.Actor` component | 4.821 s |
| cold `Std.Bool` component | 1.400 s |
| cold `Std.Fsm` component | 0.605 s |
| cold `Std.Regex` component | 0.471 s |
| cold reviewed text/literal SCC | 0.166 s |
| warm total, three samples | 1.363 / 1.588 / 1.584 s |
| warm module checking | 0.274 / 0.278 / 0.257 s |

All warm samples rebuilt zero modules. The slowest declarations remain in
`Std.Actor`: `derive_behavior_family` (1.014 s),
`emit_actor_dep_call_parts` (1.007 s), `emit_actor_parts_aliased` (0.542 s),
`emit_actor_call_parts` (0.458 s), and `emit_actor_parts_aliased_raw`
(0.451 s). Their typed-elaboration stages account for most of those totals.

The earlier 41.193 s declaration-stage sample and this sample are not suitable
for claiming a precise speedup by subtraction: they were independent wall-time
measurements on a non-isolated development machine. The new sample does establish
the current post-fix baseline and preserves the same ranking: Actor elaboration,
not Regex, is the next measured target.

## 2026-08-14 Agda-style SCC-certificate profile

Environment: Apple arm64, macOS 26.4, Erlang/OTP 29 (ERTS 17.0.2), Elixir
1.20.1. The source universe is all 77 files under `lib/std`, including the
dependent runtime/proof SCC `Std.Regex` + `Std.Regex.Proof` and
`Std.Regex.Language`. Reproduce one independent cold sample and three warm
samples with:

```sh
CURE_SKIP_DOC_FENCES=1 mix cure.bench.interfaces --warm-iterations 3 --top 20
```

Three serialized invocations produced these independent cold totals:

| Sample | Cold total | `Regex` + `Regex.Proof` | `Regex.Language` |
|---|---:|---:|---:|
| 1 | 167.339 s | 105.756 s | 40.755 s |
| 2 | 149.305 s | 102.483 s | 26.542 s |
| 3 | 177.370 s | 123.594 s | 23.882 s |
| median / range | 167.339 s / 149.305–177.370 s | 105.756 s / 102.483–123.594 s | 26.542 s / 23.882–40.755 s |

All nine warm samples rebuilt zero modules. Their median was 5.146 s and their
range was 4.684–8.354 s. Warm module checking remained approximately
1.929–2.134 s; the remainder is manifest/expansion/interface work, not repeated
Core-body or size-change closure work.

The instrumented totality counts were identical in the two bounded-output
profiles: 5,493 direct-summary requests (4,943 misses, 484 hits, 66 stale-body
reconstructions), 3,601 SCC proposals and partition checks, 575 closure
generations, 506 closure verifications, 786 summed direct edges, 4,357 summed
closure edges, 357,262 matrix-composition attempts, and 3,571 admitted derived
edges. Depending on host load, measured totals were:

| Certificate operation | Total time |
|---|---:|
| trusted direct-summary extraction/validation | 1.359–2.357 s |
| untrusted SCC proposal | 0.050–0.104 s |
| kernel partition verification | 0.059–0.091 s |
| untrusted sparse closure generation | 1.229–1.231 s |
| kernel closure verification | 0.356–0.454 s |

The largest recursive component (`Std.Regex.Language` soundness) generated a
1,650-edge exact closure from 20 direct edges: 223,508 compatible sparse
compositions in 0.616–0.620 s, followed by 0.210–0.232 s of finite kernel proof
checking. This is measurable but not the dominant cold-build cost.

The dominant cost is typed elaboration of dependent proof declarations. In the
second sample, `Std.Regex` + `Std.Regex.Proof` and `Std.Regex.Language` consumed
129.025 of 149.305 seconds (86.4%). Individual typed-elaboration stages reached
25.295 s for `thompson_alternate_acceptance_captures`, 17.449 s for
`alternate_compilation_is_sound`, and 14.602 s for
`certified_alternate_acceptance_captures`. Thus the SCC migration has achieved
cheap finite kernel verification and zero warm closure work, but it cannot by
itself solve the current dependent-proof elaboration slowdown.

The 2026-08-10 75-source, pre-proof baseline is not a like-for-like wall-time
baseline: the current 77-source universe contains the subsequently added large
dependent regex proof development. It remains useful only as historical
evidence of how much authored proof work was added, not as evidence that the SCC
certificate implementation caused a cold-time regression.

### Final certificate/cache profile

After the partition diagnostic identity, sparse-matrix validation, provenance,
and component-cache instrumentation were complete, three more serialized
invocations of the command above produced:

| Sample | Cold total | Warm samples |
|---|---:|---:|
| 1 | 163.231 s | 11.794 / 5.416 / 10.070 s |
| 2 | 172.981 s | 10.478 / 4.777 / 4.757 s |
| 3 | 146.025 s | 4.554 / 8.322 / 4.918 s |
| median / range | 163.231 s / 146.025–172.981 s | 5.416 s / 4.554–11.794 s |

Every warm sample rebuilt zero modules. The cold median is 2.5% below the
preceding 167.339 s median and therefore introduces no cold regression. The
warm median is 5.2% (0.270 s) above the preceding 5.146 s median, but both
sample ranges overlap substantially and the warm path emits no totality events:
module checking remained approximately 1.895–2.330 s and the remaining variance
is manifest/expansion/interface and host scheduling time. Component-cache
instrumentation therefore cannot account for the difference.

The three cold runs had identical operation counts:

- 7,827 direct-summary requests: 4,098 misses, 3,339 hits, and 390 stale
  reconstructions;
- 3,601 SCC proposals and partition checks;
- 575 exact closure generations and 506 finite closure verifications;
- 4,213 component-certificate decisions: 4,051 misses and 162 hits;
- 53 explicit definition-change invalidation events;
- 357,262 compatible matrix compositions and 3,571 admitted derived edges.

Measured operation totals across the three runs were:

| Certificate operation | Total time |
|---|---:|
| trusted direct-summary extraction/validation | 2.392–2.812 s |
| untrusted SCC proposal | 0.062–0.066 s |
| kernel partition verification | 0.081–0.170 s |
| untrusted sparse closure generation | 1.098–1.323 s |
| kernel finite closure verification | 0.381–0.404 s |
| component-certificate cache lookup | 0.0015 s |

The detailed first sample again located the dominant work in typed elaboration:
`Std.Regex` + `Std.Regex.Proof` took 115.323 s and `Std.Regex.Language` took
25.902 s, together 86.5% of its 163.231 s cold total. The largest individual
declaration, `thompson_alternate_acceptance_captures`, spent 29.420 s in typed
elaboration. The completed SCC-certificate path remains measurable but is not
the cold-build bottleneck.

### 2026-08-16 blocked-constructor retry-cache profile

After the phase-1 dependent-constructor retry cache (`7ac7c705`), one serialized
`MIX_ENV=test` invocation of:

```sh
MIX_ENV=test CURE_SKIP_DOC_FENCES=1 mix cure.bench.interfaces --warm-iterations 1 --top 20
```

measured a cold total of **170.314 s** for all 77 sources, rebuilding all 77,
and one no-rebuild warm sample of **5.824 s** (module checking 2.202 s). The
single cold sample is within the existing 149–177 s investigation range and is
not evidence of a wall-clock speedup or regression by itself.

The dominant components remained `Std.Regex` + `Std.Regex.Proof` (103.865 s)
and `Std.Regex.Language` (36.757 s). The largest typed-elaboration stages were
`thompson_alternate_acceptance_captures` (20.087 s),
`thompson_evidence_acceptance_from_encodes_explicit` (19.493 s), and
`alternate_compilation_is_sound` (15.725 s). Totality and SCC work remained a
small fraction of the cold build.

The new focused regression records the relevant semantic signal rather than a
machine-dependent timeout: the blocked nested `Witnessed` constructor has one
bidirectional candidate attempt after the retry cache is installed. The cache
is operation-local and does not change interface or totality counters. A future
comparison needs three independent cold samples and should retain the same
source universe and doc-fence setting.

### 2026-08-18 direct staged-machine construction profile

Environment: Apple M1 Pro, macOS arm64, Erlang/OTP 29, Elixir 1.20.1. This is
one serialized sample over all 79 `lib/std` sources with
`CURE_SKIP_DOC_FENCES=1`, after commit `50340c0d`. It is a diagnostic profile,
not a new multi-sample CI threshold.

| Measurement | Observed |
|---|---:|
| all 79 sources, cold total | 102.519 s |
| cold `Std.Regex.Proof` component | 62.392 s |
| cold `Std.Regex.Language` component | 6.974 s |
| cold `Std.Regex.Runtime` component | 1.378 s |
| cold `Std.Regex` component | 0.664 s |
| warm total | 8.148 s |
| warm module checking | 2.079 s |

The active staged machine now let-binds each direct Thompson child once and
compiles transition rows from that machine; the proof layer checks its starts
and transitions against the reference constructor. Proof elaboration remains
the dominant cold cost. The sample is below the earlier 149–177 s cold range,
but one host-loaded run is insufficient to claim a stable percentage speedup;
repeat the three-sample protocol before tightening the baseline band.

## Stabilization warning policy

The stabilization gate means **no unexpected compiler warnings**, rather than
an unconditional zero-warning count. Exactly two reviewed `use` SCCs are
allowed, with membership equal to `{Std.Char, Std.Literal, Std.String}` and
`{Std.Regex, Std.Regex.Proof}`; each is reported once as W086. Any additional
warning, additional SCC, or change to either membership fails the gate and
requires review.

The gate compares complete SCC membership rather than the rendered closed walk.
A traversal may print `Char -> Literal -> Char` or `Char -> String -> Char` for
the same three-member component. The canonical-pipeline gate pins both complete
components and their two W086 reports; `mix cure.check.stdlib` independently
rejects unexpected module compiler warnings.

## Focused test startup

Test VMs publish through the shared `_build/cure/test/ebin` root. Publication
itself is lock-serialized and each generation beneath that root is immutable and
content-addressed, so separate Mix VMs safely reuse the same checked interfaces
instead of rebuilding into PID-specific directories.

After one cold publication, the command

```sh
MIX_ENV=test mix test test/cure/diagnostic/host_test.exs:229
```

reported `0 compiled, 75 up-to-date`; the full command completed in
approximately 11 seconds and the selected test itself in 0.4 seconds. Before
the shared publication root, every focused invocation rebuilt all 75 modules
and spent roughly 54 seconds in the canonical stdlib check. The cross-process
isolation regression runs two OS VMs against one publication root and verifies
that both resolve the same complete immutable generation.
