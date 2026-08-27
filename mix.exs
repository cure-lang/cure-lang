defmodule Cure.MixProject do
  use Mix.Project

  @app :cure
  @version "0.34.0"
  @source_url "https://github.com/cure-lang/cure-lang"

  def project do
    [
      app: @app,
      version: @version,
      elixir: "~> 1.18",
      elixirc_paths: elixirc_paths(Mix.env()),
      elixirc_options: elixirc_options(Mix.env()),
      start_permanent: Mix.env() == :prod,
      consolidate_protocols: Mix.env() not in [:dev, :test],
      deps: deps(),
      escript: [main_module: Cure.CLI],
      description: description(),
      docs: docs(),
      aliases: aliases(),
      package: package(),
      test_coverage: [tool: ExCoveralls],
      # Fixtures under test/**/fixtures are loaded manually by tests, not run as
      # test files — exclude them from the loader so 1.20 doesn't warn on them.
      test_ignore_filters: [~r{/fixtures/}],
      dialyzer: [
        plt_file: {:no_warn, ".dialyzer/dialyzer.plt"},
        plt_add_deps: :app_tree,
        plt_add_apps: [:mix, :ex_unit],
        plt_core_path: ".dialyzer",
        # 1.18 and 1.20 → until map type check is fully landed
        list_unused_filters: false,
        ignore_warnings: ".dialyzer/ignore.exs"
      ],
      name: "Cure",
      source_url: @source_url
    ]
  end

  defp elixirc_paths(:test), do: ["lib", "test/support"]
  defp elixirc_paths(_), do: ["lib"]

  # Under `mix test`, treat lib/support compile warnings as errors too. The
  # `test` alias's --warnings-as-errors only covers test-file + test-run
  # warnings; this catches warnings from compiling the project itself.
  defp elixirc_options(:test), do: [warnings_as_errors: true]
  defp elixirc_options(_), do: []

  def application do
    [
      extra_applications: [:logger, :inets, :ssl, :crypto, :public_key, :tools, :sasl, :runtime_tools],
      mod: {Cure.Application, []}
    ]
  end

  def cli do
    [
      preferred_envs: [
        # Antigen drives StreamData (a `:test`-only dep), so these tasks must run
        # in :test; auto-select it so no MIX_ENV=test prefix is needed. `antigen.prune`
        # (replays assays) and `antigen.merge` (pure file ops) don't generate, so they
        # run fine in :dev and are intentionally omitted.
        antigen: :test,
        "antigen.regen_seeds": :test,
        "cure.diagnostics": :test,
        coveralls: :test,
        "coveralls.detail": :test,
        "coveralls.post": :test,
        "coveralls.html": :test,
        "coveralls.json": :test
      ]
    ]
  end

  defp deps do
    [
      # Core -- MetaAST backing
      {:metastatic, "~> 0.18"},

      # Terminal diagnostics -- Unicode display-width properties
      {:unicode, "~> 1.21"},

      # REPL -- syntax highlighting and Markdown-to-ANSI rendering
      {:marcli, "~> 0.3"},
      {:makeup, "~> 1.2"},
      {:makeup_cure, "~> 0.1"},

      # Markdown -- pure-Elixir, NIF-free renderer used by `cure doc`,
      # `Cure.Doc.Markdown`, and the REPL helpers. `:md` is safe inside
      # the escript because it has no dynamically-loaded native code.
      {:md, "~> 0.12"},

      # Observability -- optional, used by Cure.Telemetry when loaded
      {:telemetry, "~> 1.3", optional: true},

      # TOML -- pure-Erlang parser (no NIF, escript-safe) used by
      # `Cure.REPL.Config` to load `.cure.repl.toml` on REPL start.
      {:toml, "~> 0.7"},

      # Development and documentation
      {:ex_doc, "~> 0.34", only: :dev, runtime: false},
      {:excoveralls, "~> 0.18", only: :test, runtime: false},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      {:oeditus_credo, "~> 0.4", only: [:dev, :test], runtime: false},

      # Antigen -- property-based metatheory testing (test-only; quarantined
      # behind Antigen.Backend.StreamData per the architecture rule).
      {:stream_data, "~> 1.0", only: [:test]}
    ]
  end

  defp aliases do
    compile =
      if Mix.env() == :test do
        # Tests compile the host application and a VM-local stdlib generation.
        # Packaged sources/BEAMs and the root escript are independent release
        # gates; writing them here makes concurrent test VMs race on shared
        # filesystem outputs.
        ["compile", "cure.compile_stdlib"]
      else
        [
          "compile",
          "cure.bundle_stdlib",
          "cure.compile_stdlib",
          "cure.bundle_stdlib_beams",
          "cure.escript"
        ]
      end

    [
      # Warnings during `mix test` are failures — keeps the suite output clean
      # and stops new compile warnings from slipping in. Covers lib AND test
      # files (unlike elixirc_options, which misses test compilation). The
      # documentation dragnet runs after ExUnit so fenced Cure examples and
      # source docstrings are part of the default test gate too.
      test: ["test --warnings-as-errors", "cure.check.docs"],
      quality: ["format", "credo --strict"],
      "quality.ci": [
        "format --check-formatted",
        "credo --strict"
      ],
      # `mix check` runs the Cure stdlib and example regression
      # suites. Invoke alongside `mix test` (CI does both).
      check: ["cure.compile_stdlib", "cure.check"],
      # Stage stdlib `.cure` sources under `priv/std/` before every
      # compile so host applications (notably the Cure REPL embedded
      # in `:cure_site`) can locate them via `:code.priv_dir(:cure)`
      # in both dev and prod releases. See
      # `Mix.Tasks.Cure.BundleStdlib` and `Cure.Stdlib.Paths`.
      #
      # After the regular Elixir `compile` step, `cure.bundle_stdlib_beams`
      # uses the freshly-built `Cure.Compiler` to emit `Cure.Std.*.beam`
      # into `priv/ebin/`. That directory rides along with every OTP
      # release so the embedded REPL can call into the stdlib at runtime
      # without relying on the build-time `_build/cure/ebin` artefact.
      compile: compile
    ]
  end

  defp description do
    """
    Dependently-typed programming language for the BEAM virtual machine
    with one kernel-checked compiler pipeline and first-class OTP concurrency.
    """
  end

  defp package do
    [
      maintainers: ["Aleksei Matiushkin"],
      licenses: ["MIT"],
      links: %{
        "GitHub" => @source_url,
        "Changelog" => @source_url <> "/blob/main/CHANGELOG.md"
      },
      # `priv/` is included so the hex tarball ships both the stdlib
      # sources (`priv/std/*.cure`, used by the type checker) and the
      # compiled stdlib BEAMs (`priv/ebin/Cure.Std.*.beam`, used by the
      # REPL at runtime). See `Mix.Tasks.Cure.BundleStdlib` and
      # `Mix.Tasks.Cure.BundleStdlibBeams`.
      files: ~w(lib priv mix.exs README.md CHANGELOG.md LICENSE docs)
    ]
  end

  defp docs do
    [
      main: "readme",
      extras: [
        "README.md",
        "CHANGELOG.md",
        "docs/TUTORIAL.md",
        "docs/LANGUAGE_SPEC.md",
        "docs/MACROS.md",
        "docs/TYPE_SYSTEM.md",
        "docs/DEPENDENT_TYPES.md",
        "docs/KERNEL.md",
        "docs/DEPENDENT_KERNEL_PEERNESS_ROADMAP.md",
        "docs/PATTERNS.md",
        "docs/BINARIES.md",
        "docs/PROOFS.md",
        "docs/PACKAGE_REGISTRY.md",
        "docs/PUBLISHING.md",
        "docs/FSM_GUIDE.md",
        "docs/SUPERVISION.md",
        "docs/APP.md",
        "docs/DOC.md",
        "docs/STDLIB.md",
        "docs/REPL.md",
        "docs/OBSERVABILITY.md",
        "docs/PROTOCOL.md",
        "docs/TEMPORAL.md",
        "docs/PLAYGROUND.md",
        "docs/BLESS.md",
        "docs/REPLAY.md",
        "docs/JOHN.md",
        "docs/PGO.md",
        "docs/PROOF_CARRYING.md",
        "docs/EXPORT_TYPES.md",
        "docs/SNAP.md",
        "docs/STORY.md",
        "docs/MATCH.md",
        "docs/PICKUP.md",
        "docs/FFI.md",
        "ROADMAP-0.34.md"
      ],
      source_url: @source_url,
      source_ref: "v#{@version}",
      formatters: ["html"],
      authors: ["Aleksei Matiushkin"],
      canonical: "https://hexdocs.pm/#{@app}"
    ]
  end
end
