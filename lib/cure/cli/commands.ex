defmodule Cure.CLI.Commands do
  @moduledoc """
  The single source of truth for the `cure` subcommand surface.

  `Cure.CLI` used to hard-code the command list in three places that could
  drift apart: the `@moduledoc` usage block, the `known_commands` list used to
  suggest a near-miss spelling, and the full `help/0` text. This module holds
  the one registry those three sites are derived from, so adding or renaming a
  subcommand touches exactly one list.

  Each entry is `{name, args, description}`:

    * `name` is the command word (`"compile"`, `"export-types"`, ...);
    * `args` is the usage tail (`"<file|dir>"`, `""` for a bare command);
    * `description` is the one-line summary shown by `cure help`.

  The registry is ordered for display: it is grouped by concern so `cure help`
  reads as a coherent list rather than an alphabetical dump.
  """

  @type command :: {name :: String.t(), args :: String.t(), description :: String.t()}

  @commands [
    {"compile", "<file|dir>", "Compile .cure files to BEAM bytecode"},
    {"run", "<file>", "Compile and execute a .cure file"},
    {"check", "<file>", "Type-check without compiling"},
    {"lsp", "", "Start the Language Server Protocol server"},
    {"mcp", "", "Start the Model Context Protocol server"},
    {"stdlib", "", "Compile the standard library"},
    {"doc", "[path|dir]", "Generate HTML documentation"},
    {"fmt", "[path|dir]", "Format .cure source files (algebra by default; --safe, --aggressive, --check)"},
    {"migrate", "[path|dir]", "Port source to an edition (--check, --print, --strict, --edition YYYY)"},
    {"repl", "", "Interactive Cure session (multi-line, :help for commands)"},
    {"watch", "[path]", "Recompile/check/test on every save"},
    {"new", "<name>", "Scaffold a new project (--lib | --app | --fsm)"},
    {"init", "<name>", "Same as `new --lib`"},
    {"deps", "", "Resolve project dependencies"},
    {"test", "[--cover]", "Run .cure tests under test/, optionally with coverage"},
    {"bench", "[path]", "Run .cure benchmarks under bench/"},
    {"explain", "<Eddd>", "Explain an error code"},
    {"why", "<Eddd>", "Alias for `explain`"},
    {"doctor", "", "Environment + project + source health report"},
    {"fix", "[--dry-run]", "Apply safe project-wide code fixes"},
    {"publish", "[opts]", "Package and upload to the Cure registry"},
    {"search", "<query>", "Search the registry for packages"},
    {"info", "<name[:ver]>", "Show registry manifest / version list"},
    {"keys", "generate <h>", "Generate an Ed25519 signing keypair"},
    {"keys", "list", "List trusted publisher keys"},
    {"release", "", "Build a BEAM release (requires `app`)"},
    {"trace", "<M.f/a>", "Typed tracer over :dbg (--duration N)"},
    {"replay", "<journal>", "Replay a recorded observation journal (--module M, --step)"},
    {"draw", "<path.cure>", "Render lifted modules as ASCII (--filter lifted|all)"},
    {"verify", "[path]", "Verify compiled artifacts against their sources (--strict)"},
    {"export-types", "[path]", "Export type definitions (--target protobuf, --out FILE)"},
    {"snap", "<save|load|list>", "Snapshot and restore compiler state (--out FILE)"},
    {"story", "", "Narrate the project as a build story (--out FILE, --diagrams)"},
    {"audit", "trust <Module>", "Print the unproved assumptions reachable from a module"},
    {"john", "", "Print everything: VM stats, tooling, project, logs"},
    {"version", "", "Show version"},
    {"help", "", "Show this help"}
  ]

  @doc "The full command registry, in display order."
  @spec all() :: [command()]
  def all, do: @commands

  @doc """
  The bare command words, for near-miss suggestion (e.g. `Cure.Compiler.Errors.suggest/2`).

  Multi-word commands contribute their first word only; `keys generate` and
  `keys list` both suggest `keys`, which is what a user typing `keis` wants.
  """
  @spec names() :: [String.t()]
  def names do
    @commands
    |> Enum.map(fn {name, _args, _description} -> name end)
    |> Enum.uniq()
  end

  @doc """
  The `Commands:` block of `cure help`, one aligned line per registry entry.

  The command column is padded to the width of the widest `name args` pair so
  the descriptions line up.
  """
  @spec help_lines() :: [String.t()]
  def help_lines do
    labels = Enum.map(@commands, fn {name, args, _description} -> String.trim("#{name} #{args}") end)
    width = labels |> Enum.map(&String.length/1) |> Enum.max(fn -> 0 end)

    @commands
    |> Enum.zip(labels)
    |> Enum.map(fn {{_name, _args, description}, label} ->
      "  #{String.pad_trailing(label, width)}   #{description}"
    end)
  end
end
