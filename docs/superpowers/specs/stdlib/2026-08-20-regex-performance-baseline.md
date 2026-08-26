# Cure Regex Portable Baseline

**Recorded:** 2026-08-20

**Checkout:** `e497709b` (`complete atomvm regex smoke closure`)

**Host:** `MacBookPro18,3`, 16 GiB RAM, macOS, OTP 29.0.2, Elixir 1.20.1.

This is the Phase 1 baseline for the embedded `cure_regex` package. Measurements
are serialized; no Mix invocations were concurrent. The accepted W086 warning
is the existing `Std.Char -> Std.Literal -> Std.Char` SCC.

## Canonical cold/warm pipeline

Command:

```text
mix cure.bench.interfaces --warm-iterations 3 --top 12
```

The source universe was the 68 foundational modules plus the 11 modules under
`lib/std_deps/regex` (79 total), through the canonical module pipeline.

| Measurement | Result |
|---|---:|
| Cold total | 122.686 s |
| Warm 1 | 10.972 s |
| Warm 2 | 6.664 s |
| Warm 3 | 6.208 s |
| Warm median | 6.664 s |
| Cold rebuilt modules | 79 |
| `Std.Regex.Proof` cold component | 78.929 s |
| `Std.Regex.Language` cold component | 7.532 s |
| `Std.Regex.Runtime` cold component | 3.791 s |
| `Std.Regex` cold component | 0.727 s |

The dominant declarations were `Std.Regex.Proof#thompson_alternate_acceptance_captures`
(16.272 s), `#certified_alternate_acceptance_captures` (9.963 s), and
`#thompson_repeat_acceptance_captures` (5.688 s). Totality instrumentation
reported 731 closure-generation operations, 12,207 closure edges, and 863,138
composition attempts in the cold sample. These figures are diagnostic evidence,
not a new optimization target by themselves.

## Verified artifact and runtime closure

The final verified stdlib artifact contains 79 Cure BEAM modules and 1,049,892
BEAM bytes. Starting at the declared package export `Std.Regex`, the canonical
BEAM-import audit reaches 9 Cure modules and 348,040 Cure BEAM bytes:

```text
PortableClosure.audit("_build/cure/ebin", package: "cure_regex")
roots      = ["Std.Regex"]
forbidden = []
nifs       = []
```

The AtomVM library archive used by the smoke gate contains this closure, the
`cure_std_char` bridge, and the pinned Unicode 1.21.1 dependency BEAMs (27
modules). The representative `--lib` archive is 3,145,500 bytes before the
probe wrapper, normalized filename aliases, and AtomVM's `estdlib` beams are
added.

## Runtime vector

The BEAM and generic-unix AtomVM gate runs the same compiled constructor-based
vector (`predicate(same('a'))` searched against `"za"`) and both return `true`.
The first BEAM invocation, including one-time code-path loading, measured
24,485 μs. After loading, 1,000 executions measured 5,439 μs total (5.439 μs
per call). VM-wide memory changed by 3,503,704 bytes over that 1,000-call
sample; this is an allocation delta, not a peak-live-memory bound.

The source-literal macro path remains covered by the existing Regex behavior
tests; this runtime measurement deliberately uses the already-constructed typed
API so parser/macro compilation is not mixed into execution timing.

## Reproduction and ratchet

Re-run the canonical benchmark and the serialized AtomVM gate after each phase:

```text
mix cure.bench.interfaces --warm-iterations 3 --top 12
mix test test/cure/compiler/regex_portability_gate_test.exs
mix test test/cure/compiler/atomvm_regex_container_test.exs --only atomvm
```

Compare like-for-like source universes and AtomVM revision (`89918dc1`). A warm
improvement does not justify a cold regression; any cache or module split must
first show its cold effect against this record.
