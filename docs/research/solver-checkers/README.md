# Solver and certificate-checker research trees

Local, ignored upstream working copies used while implementing Cure's checked
Presburger certificate boundary. They are research inputs, not dependencies and
must not be linked into the compiler or trusted by the kernel.

## Pinned checkouts — 2026-07-22

| Directory | Upstream | Revision |
| --- | --- | --- |
| `smtcoq/` | `https://github.com/smtcoq/smtcoq.git` | `894d2fc0b09eea6637787110a20afdde016caf7c` |
| `carcara/` | `https://github.com/ufmg-smite/carcara.git` | `81f0df827297245f1370353924784325d8adab51` |
| `cvc5/` | `https://github.com/cvc5/cvc5.git` | `ed5e08073b9cde60a6319924d316988802c1eba1` |
| `ethos/` | `https://github.com/cvc5/ethos.git` | `add55d07f74281b95e03e0bd4febbd2d1538782a` |
| `princess/` | `https://github.com/uuverifiers/princess.git` | `9d677038a90e1af8a334041277a116c6d00a9f03` |
| `verit-2026.05/` | `https://www.verit-solver.org/download/2026.05/verit-2026.05.tar.gz` | SHA-256 `c0d3754b599d02c0443590640ecefbd2ddf5603b7adcd8fbdfb31b84e59cc2f1` |

The official Alethe GitLab endpoint did not return refs on 2026-07-22, so
`alethe/` is an intentionally incomplete checkout. `alethe-spec.pdf` is the
current specification downloaded from `https://verit.loria.fr/alethe.pdf`.
Carcara also contains the parser and rule implementation needed for executable
comparison.

Existing local algorithm references are not duplicated here:

- `/Users/ch/Develop/rocq/plugins/micromega/`
- `/Users/ch/Develop/lean4/src/Lean/Elab/Tactic/Omega/`

## Build-first order

1. Carcara — fastest proof-format/parser smoke test (`cargo build --release`).
2. Ethos — independent CPC/Eunoia checker (`./configure.sh`, `make -C build`).
3. cvc5 — CPC proof producer paired with Ethos (`./configure.sh production
   --auto-download`, `make -C build`).
4. veriT — Alethe producer (`./configure --disable-lto`, `make`).
5. Princess — independent complete Presburger oracle/proof producer (`sbt` or
   its release launcher).
6. SMTCoq — architecture/reconstruction validation after an isolated Rocq/opam
   switch is available.

Record tool versions, build commands, required patches, and one checked
arithmetic proof before implementing a Cure adapter. Do not design the Cure
certificate language around any one native proof format.

## Local build results — 2026-07-22

| Project | Result | Reproduction notes |
| --- | --- | --- |
| Carcara | Pass | Rust 1.87; `cargo build --release` |
| Ethos | Pass | `./configure.sh && make -C build -j4`; system Homebrew GMP detected |
| cvc5 | Pass | `./configure.sh production --auto-download -DCMAKE_CXX_FLAGS=-I/opt/homebrew/include -DCMAKE_C_FLAGS=-I/opt/homebrew/include && make -C build -j4` |
| Princess | Pass | `sbt compile`; sbt selected Homebrew Java 26 and compiled 271 Scala sources |
| veriT | Pass | `CPPFLAGS=-I/opt/homebrew/include LDFLAGS=-L/opt/homebrew/lib ./configure --disable-lto && make -j4` |
| SMTCoq | Pass | OCaml 4.14.2 switch `cure-smtcoq`, Rocq 9.2, `rocq-extra-dev`, then `opam exec --switch=cure-smtcoq -- dune build -p rocq-smtcoq` |

cvc5's unmodified Apple Silicon build found `/opt/homebrew/lib/libgmp.dylib`
but did not propagate `/opt/homebrew/include` to sources including LibPoly's
`poly.h`. The explicit C and C++ include flags above repair the build without
patching the upstream checkout.

SMTCoq `main` currently requires the development `rocq-trakt` package, which
is not present in `rocq-released`. The isolated switch therefore also selects
the official `https://rocq-prover.org/opam/extra-dev` repository.
Its library build is green, but the aggregate upstream `unit-tests` and
`examples` targets are not standalone checker tests: they invoke PATH-installed
legacy `cvc4`, veriT, ZChaff, and GNU `flock`. On this macOS host they stop on
those missing executables (`flock` is also nonstandard on macOS). Do not report
that as a source-build failure or install the legacy solvers into Cure's normal
toolchain merely to satisfy the aggregate target.

## Arithmetic proof smoke tests — 2026-07-22

The tracked `fixtures/` directory contains a rational Farkas-style
contradiction and the integer-only divisibility contradiction `2*x = 1`.

| Producer → checker | Rational fixture | Integer fixture | Observation |
| --- | --- | --- | --- |
| cvc5 Alethe → Carcara | `valid` | Rejected by stock configuration | Integer proof uses cvc5 RARE rule `arith-int-eq-conflict`; this is not a self-contained stock-Alethe path |
| cvc5 CPC → Ethos | `correct` | `correct` | Both paths check completely with the ordinary `Cpc.eo` signature alone; no expert signature is needed |
| veriT Alethe → Carcara | `valid` | `valid` | Integer proof requires Carcara's `--allow-int-real-subtyping`; the decisive `la_generic` step carries coefficients `1/2, 1/2` |
| Princess | `unsat` | `unsat` | `+printProof` works, but preprocessing reduces the small integer fixture to `false`, so its displayed proof is not yet a useful adapter fixture |

The integer CPC fixture contains only `arith-int-eq-conflict`, polynomial
normalisation, equality resolution, evaluation, and transitivity. Ethos reports
`correct`, not `incomplete`. Cure will still translate accepted native output
into its own kernel-checkable certificate language rather than trusting CPC,
Ethos, or cvc5.

## OTP-first semilinear probe

The immediate B3 consumer is semantic inclusion between commutative-regex
mailbox patterns, not the standalone QF-LIA fixtures above. The locked first
pair is:

```text
positive: PStar(PTimes(PAtom(TA), PAtom(TA))) <= PStar(PAtom(TA))
negative: PStar(PAtom(TA)) <= PStar(PTimes(PAtom(TA), PAtom(TA)))
```

Normalization gives `L(0,{[2,0,0]}) <= L(0,{[1,0,0]})`. The positive
certificate maps the source period to coefficient vector `[2]` over the target
period. The negative counterexample is `[1,0,0]`. This is the first production
pipeline target; the SMT-LIB fixtures remain arithmetic checker/adapter probes
for the later general Presburger layer.
