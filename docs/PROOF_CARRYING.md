# Proof-carrying packages (v0.32.0)

Cure packages can embed a `.cureproof` artifact in their published
tarballs. The artifact captures the type-checker's proof certificates
so consumers can re-verify the publisher's claims offline without
re-running the full SMT solver from scratch.

## How it works

During `cure publish`, the compiler is re-invoked in `proof_collect`
mode. Each proof obligation discharged during type-checking -- equality
witnesses, SMT-backed constraints, and totality arguments -- is
serialized as a certificate and written into a compact binary file:

    my_pkg-0.1.0/
      Cure.toml
      lib/*.cure
      my_pkg.cureproof     <-- new in v0.32.0

The `.cureproof` format is a magic-header binary followed by a
gzip-compressed Erlang term:

    "CUREPROOF\0" <> <<0x01>> <> gzip(term_to_binary([cert, ...]))

Each certificate is a map `%{module, kind, statement, witness}` where
`kind` is one of `:equality`, `:smt`, or `:totality`.

## Opt-out

Add to `Cure.toml` if you want to disable proof inclusion:

```toml
[publish]
include_proofs = false
```

The default is `true`. Packages published without proofs are fully
functional; only `cure verify --strict` treats the absence as a hard
error (see below).

## Verifying a package offline

`cure verify` (or `mix cure.verify`) reads `.cureproof` files from a
tarball or installed dependency directory and replays each certificate
through the offline verifier:

```bash
# Verify the current project's own proofs
mix cure.verify

# Verify a downloaded tarball
mix cure.verify my_pkg-0.1.0.tar.gz

# Verify installed deps
mix cure.verify _build/cure/deps/my_pkg-0.1.0/

# Treat missing proof file as an error
mix cure.verify --strict my_pkg-0.1.0.tar.gz
```

### Exit codes

- `0` -- all certificates verified successfully.
- `1` -- a certificate failed (E066), or a proof file was missing with
  `--strict` (E065).

## CI integration

Add to your CI pipeline to verify that every dependency carries valid
proofs before running your test suite:

```bash
mix cure.verify --strict _build/cure/deps/
```

Set `strict_proofs: true` in `config/config.exs` to make strict
verification the permanent project-wide default:

```elixir
config :cure, strict_proofs: true
```

## Error codes

| Code | Meaning |
|------|---------|
| E065 | Proof file missing (only fatal with `--strict`) |
| E066 | Proof verification failed -- certificate could not be replayed |
| E067 | Proof schema incompatible -- `.cureproof` version mismatch |

## Certificate kinds

| Kind | Verified by |
|------|-------------|
| `:equality` | Structural equality of witness against `:cure_refl` |
| `:smt` | Z3 query replay (stub in v0.32.0; degrades to `:ok` when solver absent) |
| `:totality` | SCC structural-decrease argument |
