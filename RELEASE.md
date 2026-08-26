# Releasing Cure 0.34.0

Cure 0.34 is the dependent-pipeline release. The classic checker and code
generator are gone: every program is elaborated to dependent Core, checked by
the kernel, quantitatively erased, and emitted as BEAM code through one path.

This file is the operational release procedure. The feature narrative belongs
in [`ROADMAP-0.34.md`](ROADMAP-0.34.md), the public change inventory in
[`CHANGELOG.md`](CHANGELOG.md), and the live blockers in
[`docs/LAUNCH-CHECKLIST-0.34.md`](docs/LAUNCH-CHECKLIST-0.34.md).

## 1. Prepare the release metadata

1. Finish every non-deferred item in the launch checklist.
2. Set `@version` in `mix.exs` to `0.34.0`. This also sets the HexDocs
   `source_ref` and the CLI/REPL version returned by `Cure.version/0`.
3. Promote `CHANGELOG.md`'s `[Unreleased]` section to `[0.34.0] -- YYYY-MM-DD`.
4. Confirm its breaking-change list matches `ROADMAP-0.34.md`.
5. Build the docs and inspect the generated version, source links, macro page,
   proof page, and standard-library pages.

Do not tag while the tree contains an unexplained generated diff. In
particular, bundled standard-library sources and BEAMs under `priv/` are package
inputs, so rebuild and review them deliberately.

## 2. Run the repository gates

Run these from a clean checkout using the supported Elixir/OTP versions:

```sh
mix deps.get
mix quality.ci
mix test
mix check
mix cure.check.stdlib
mix cure.check.examples
mix cure.check.projects
./cure migrate --check --strict lib/std examples
mix cure.diagnostics --color=always --width=80 --coverage
mix dialyzer
mix antigen complete
mix docs
```

`mix test` includes the checked documentation snippets. `mix check` exercises
canonical stdlib compilation and the root Cure examples; `cure.check.projects`
runs every nested example in its own VM. The migration command must exit zero
and print nothing.

If the differential oracle fixtures changed intentionally, run the live oracle
on a machine with Idris2 installed, review `test/oracle/**/verdicts.json`, and
then run the offline oracle replay in the normal suite. Never regenerate oracle
verdicts merely to make a failing comparison green.

## 3. Verify downstream consumers

The release is not ready until the new package candidate compiles the supported
downstream corpus:

- `cure-otp`: `lib/` and `metatheory/src`, including its proof modules;
- the `esp32-beam` generic-Unix/AtomVM phase directories;
- the Phoenix site in this repository, including its embedded REPL and
  source-driven stdlib documentation.

Use the candidate checkout or packed Hex archive, not an older globally
installed `cure` executable. Record exact commands and revisions in the launch
checklist when this gate is run.

## 4. Inspect the package

```sh
mix hex.build
mix hex.build --unpack
```

Inspect the archive before publishing. It must contain the public Elixir
sources, `priv/std/*.cure`, bundled `priv/ebin/Cure.Std.*.beam` artifacts,
documentation, licence, README, changelog, and mix metadata. It must not contain
test output, local caches, temporary migration files, Antigen reports, or nested
example build directories.

Start the unpacked candidate in a fresh environment and verify at minimum:

```text
cure --version
cure repl
cure check <small dependent example>
cure compile <small dependent example>
```

The CLI and REPL must both report `0.34.0`; the REPL must evaluate an expression,
accept a multiline definition, and expose `:type`, `:doc`, `:holes`, and proof
inspection without rebuilding the stdlib from source.

## 5. Tag and publish

1. Commit the reviewed release metadata and generated package inputs.
2. Create the signed tag `v0.34.0` at that exact commit.
3. Push the commit and tag.
4. Publish to Hex only from the tagged tree.
5. Build and publish HexDocs.
6. Deploy the website and verify `/`, `/roadmap`, `/stdlib`, `/llms.txt`, and
   `/sitemap.xml` against the released version.
7. Create the GitHub release from the 0.34 changelog and roadmap narrative.

After publication, restore an empty `[Unreleased]` section only in the next
development commit. Never amend or move the published tag.

## 6. Rollback boundary

Before Hex publication, fix the candidate and recreate the unpublished tag if
necessary. After Hex publication, do not replace `0.34.0`; issue a new patch
release, document the correction, and repeat the full gates appropriate to the
change.
