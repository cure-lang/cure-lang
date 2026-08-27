# Publishing Cure Packages (v0.23.0)

This guide walks through the full lifecycle of publishing a Cure
package against the v0.23.0 registry. Every command below exists on
the shipped `cure` CLI.

## Before you start
- `cure version` should report `Cure 0.23.0` or newer.
- Decide on a **maintainer handle**. It should match your GitHub
  username for OAuth bootstrapping, but the registry does not require
  it to literally be a GitHub account.
- Have a `Cure.toml` at the root of the project. `cure new my_pkg`
  scaffolds one.

## 1. Generate a signing keypair
Every upload is signed with an Ed25519 private key. Generate one:

```bash
cure keys generate alice
```

This writes:
- `~/.cure/keys/alice.sec` (mode `0600`)
- `~/.cure/keys/alice.pub`
- appends `alice = "<hex>"` to `~/.cure/keys/trusted.toml`

Keep the `.sec` file private. Treat it like an SSH private key.

`cure keys list` shows every trusted handle known to the local client.

## 2. Verify the package locally
```bash
cure publish --dry-run
```
The dry-run assembles the tarball exactly as the live publish would,
prints the SHA-256 and byte size, and exits without uploading. Good
last-check before pushing.

## 3. Obtain an upload token
Upload tokens are short-lived OAuth bearers issued by the registry.
The exact provisioning flow is outside this doc, but typically:

```bash
export CURE_TOKEN="$(cure-registry-cli login --github alice)"
```

Any opaque string will do for `cure publish`; the registry handles
validation.

## 4. Publish
```bash
cure publish --handle alice --token "$CURE_TOKEN"
```
or, with env vars picked up implicitly:

```bash
CURE_HANDLE=alice CURE_TOKEN=$CURE_TOKEN cure publish
```

`cure publish`:
1. Calls `Cure.Project.Publisher.build_tarball/2` to assemble the
   gzipped tarball. The layout is:
   ```
   my_pkg-0.1.0/
     Cure.toml
     README.md
     LICENSE
     lib/*.cure
     docs/*.md
   ```
   When `[publish] include_proofs` is `true` (the default, added in
   v0.32.0), a `<name>.cureproof` certificate file is also embedded;
   see `docs/PROOF_CARRYING.md`.
2. Delegates to `Cure.Project.Signing.sign_tarball/4` to sign
   `name || NUL || version || NUL || sha256(tarball)`.
3. POSTs a JSON envelope to `/packages`:
   ```json
   {
     "name":      "<pkg>",
     "manifest":  { ... },
     "tarball":   "<base64 bytes>",
     "signature": "<base64 sig>"
   }
   ```
4. The registry appends a transparency-log entry; subsequent
   `cure deps` runs at other sites verify the tarball against the log.

## 5. Verify the published entry
```bash
cure info my_pkg
cure info my_pkg:0.1.0
```
`cure info` prints the manifest + SHA-256 so you can confirm the
upload matches the local state.

## 6. Cross-publish to Hex.pm
Cure can emit a Hex-compatible tarball that `mix hex.publish` can
consume directly. Produce the tarball:

```bash
cure publish --hex
```
Output: `_build/cure/publish/hex.tar`. Feed it into Hex:

```bash
mix hex.publish package --replace \
  --files _build/cure/publish/hex.tar
```

The Hex-compatible tarball layout is:
```
VERSION            ("3")
CHECKSUM           (sha256 over VERSION || contents.tar.gz || metadata.config)
metadata.config    (Erlang term file)
contents.tar.gz    (gzipped source tree under my_pkg-0.1.0/)
```
`cure publish --hex` does *not* upload to Hex. It produces the tar
locally so your existing Elixir release process owns the final push.

## 7. Key rotation
`cure keys generate <new_handle>` produces a fresh keypair. To rotate
an existing handle, generate under a new name, update the trust lists
of every downstream consumer, and stop using the old `.sec` file. A
future release will add a `cure keys rotate` ergonomic wrapper.

## 8. Strict verification
Set in your project's `config/config.exs`:
```elixir
config :cure, strict_transparency: true
```
This promotes a transparency-log fetch failure from a warning
(`E042`) to a hard error. Good for CI environments that should refuse
to install an unverified tarball.

## 9. Troubleshooting
- `E038 Registry Fetch Failed`: check the registry URL
  (`cure doctor` prints it) and your network.
- `E039 Registry Hash Mismatch`: the tarball served does not match the
  hash the index declared; rerun `cure deps update`.
- `E040 Registry Package Not Found`: the name is wrong, or the
  package has not been published yet.
- `E041 Registry Signature Invalid`: the publisher's key is not in
  your local `trusted.toml`. Add it via `cure keys generate` or ask
  the publisher to share the `.pub` file.
- `E042 Transparency Log Unreachable`: registry's `/log` endpoint is
  down. Installation continues with an `:unverified` annotation unless
  `strict_transparency: true` is set.

## 10. Rollback / yank
v0.23.0 ships no UI for yanking. The index accepts `?yanked=true` on
the manifest endpoint, and clients refuse to install yanked versions;
the shipped server implementation is left to the hosting registry.
