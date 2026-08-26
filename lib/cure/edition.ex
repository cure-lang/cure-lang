defmodule Cure.Edition do
  @moduledoc """
  Cure editions: a coarse, declared, calendar-named compatibility line a file or
  project is read against (design: docs/superpowers/specs/2026-07-10-editions-design.md).

  An edition is a 4-digit calendar-year string. The set of real editions is the
  closed allow-list `@known`; `current/0` is the compiler default, deliberately
  DECOUPLED from the newest known edition so a new edition can be minted as opt-in
  before promotion to default (Rust parity — see `current/0`). Ordering is by
  integer year and is deliberately independent of the allow-list so ordering logic
  is usable for editions not yet minted.
  """

  require Logger

  @known ["2026"]
  @current "2026"

  @type t :: String.t()

  @doc "All known editions, oldest-first."
  @spec all() :: [t()]
  def all, do: Enum.sort(@known, &(year(&1) <= year(&2)))

  @doc "Every known edition (declaration set; unordered)."
  @spec known() :: [t()]
  def known, do: @known

  @doc """
  The compiler default edition applied when none is declared.

  Deliberately a standalone constant, NOT derived from `all/0` — the default is
  decoupled from the newest *known* edition on purpose (Rust parity): a new
  edition may be minted into `@known` as opt-in (selectable via pragma/manifest)
  while the default stays on the older, stable one until it is promoted. Today
  `@known` has one entry so `@current` coincides with the newest; do not "fix"
  this to `List.last(all())` — that would collapse the staged-rollout capability.
  """
  @spec current() :: t()
  def current, do: @current

  @doc "True iff `edition` is a known edition."
  @spec valid?(term()) :: boolean()
  def valid?(edition), do: edition in @known

  @doc "Validate an edition string against the allow-list."
  @spec parse(term()) :: {:ok, t()} | {:error, {:unknown_edition, term()}}
  def parse(edition) do
    if valid?(edition), do: {:ok, edition}, else: {:error, {:unknown_edition, edition}}
  end

  @doc "Total order on editions by integer year (allow-list-independent)."
  @spec compare(t(), t()) :: :lt | :eq | :gt
  def compare(a, b) do
    cond do
      year(a) < year(b) -> :lt
      year(a) > year(b) -> :gt
      true -> :eq
    end
  end

  # Total over binaries: a non-numeric edition raises a clear domain error rather
  # than the opaque String.to_integer ArgumentError (F8). compare/2 is spec'd on
  # t(), so this only fires on a contract violation, but it fires legibly.
  defp year(edition) when is_binary(edition) do
    case Integer.parse(edition) do
      {n, ""} -> n
      _ -> raise ArgumentError, "not a valid edition (expected a numeric year): #{inspect(edition)}"
    end
  end

  @doc """
  The edition named by a file-leading `@edition("YYYY")` pragma, or `nil`. Uses a
  lightweight pre-parse line scan (not the full parser) because the edition must
  be known BEFORE parsing selects the keyword set. Skips leading blank lines and
  `#`/`##` comment lines; the first substantive line must be the pragma or there
  is none.
  """
  @spec pragma_edition(String.t()) :: t() | nil
  def pragma_edition(source) when is_binary(source) do
    # Bounded scan: the pragma (if any) is the first non-blank, non-comment line,
    # so split only at each leading newline (`parts: 2`) instead of materialising
    # the whole file — this runs on every compile now that resolution is wired
    # into the build pipeline (F-A), so it must not be O(file size).
    case first_substantive_line(source) do
      nil -> nil
      line -> pragma_capture(line)
    end
  end

  @doc """
  The 0-based index — into `String.split(source, "\\n")` — of the first
  substantive line, where a file-leading `@edition` pragma must sit, or `nil` if
  the file has none. Fence-aware in exactly the way `pragma_edition/1` is: a
  `###`-fenced doc comment before the pragma (whose body lines need not start
  with `#`) is skipped as one unit, so a rewriter can target the same line the
  resolver reads instead of re-deriving a divergent, fence-blind index.
  """
  @spec leading_line_index(String.t()) :: non_neg_integer() | nil
  def leading_line_index(source) do
    source |> String.split("\n") |> scan_leading_index(0)
  end

  defp scan_leading_index([], _idx), do: nil

  defp scan_leading_index([line | rest], idx) do
    cond do
      fence_open_line?(line) ->
        case drop_fence_lines(rest, idx + 1) do
          {:closed, rest2, idx2} -> scan_leading_index(rest2, idx2)
          :unterminated -> nil
        end

      trivia_line?(line) ->
        scan_leading_index(rest, idx + 1)

      true ->
        idx
    end
  end

  # Drop lines up to AND INCLUDING the next fence marker (the close), mirroring
  # `skip_fence/1`; return the remaining lines and the index just past the close,
  # or `:unterminated` if EOF is hit first (an unterminated fence has no
  # substantive line after it).
  defp drop_fence_lines([], _idx), do: :unterminated

  defp drop_fence_lines([line | rest], idx) do
    if fence_open_line?(line), do: {:closed, rest, idx + 1}, else: drop_fence_lines(rest, idx + 1)
  end

  defp first_substantive_line(source) do
    case String.split(source, "\n", parts: 2) do
      [line, rest] ->
        cond do
          # A `###...###` fenced doc comment: the lexer swallows the whole block
          # (opening line through the next `###` line) into ONE :doc_comment token,
          # so nothing inside it — including an `@edition(...)` line — is a pragma.
          # Skip the entire fence, exactly like the lexer, before scanning on.
          fence_open_line?(line) -> first_substantive_line(skip_fence(rest))
          trivia_line?(line) -> first_substantive_line(rest)
          true -> line
        end

      [line] ->
        # Last line, no trailing newline. An unterminated fence (opened but never
        # closed) swallows the rest of the file, so it yields no substantive line.
        if fence_open_line?(line) or trivia_line?(line), do: nil, else: line
    end
  end

  # A fenced doc comment opens (and closes) on a line whose first non-space
  # characters are `###`. The lexer measures leading indentation with
  # `count_leading_spaces`, which counts ONLY the ASCII space 0x20 (tabs are a hard
  # `:tab_not_allowed` error, and other whitespace — form-feed, vertical-tab — is
  # never indentation). So the pre-scan must strip only leading 0x20 spaces before
  # testing for `###`, NOT String.trim_leading/1 (which strips all Unicode
  # whitespace): a `\t###`/`\f###` line is fence *body* to the lexer, and treating
  # it as a fence marker made the pre-scan close a fence early and read a buried
  # @edition as a pragma the compiler never sees. `##` (exactly two hashes) is a
  # single-line doc comment, not a fence, and is handled by `trivia_line?`.
  defp fence_open_line?(line), do: String.starts_with?(drop_leading_spaces(line), "###")

  # Consume the body of a fenced doc comment: drop lines until (and including) the
  # next fence marker line (the close), matching the lexer's `fence_close_line?`.
  # Returns the source after the close. If EOF is reached first the whole remainder
  # is consumed (unterminated fence).
  defp skip_fence(source) do
    case String.split(source, "\n", parts: 2) do
      [line, rest] -> if fence_open_line?(line), do: rest, else: skip_fence(rest)
      [_line] -> ""
    end
  end

  # A line is trivia (blank or a `#`/`##` comment) iff, after stripping leading
  # ASCII spaces (the only whitespace the lexer treats as indentation), it is empty
  # or starts with `#`. Leading indentation is 0x20-only for the same reason as
  # `fence_open_line?`: a line whose non-space run leads with a tab is not a
  # skippable comment to the lexer (it is a `:tab_not_allowed` error), so the
  # pre-scan must stop there rather than skip it and fabricate a pragma downstream.
  defp trivia_line?(line) do
    t = line |> drop_leading_spaces() |> String.trim_trailing()
    t == "" or String.starts_with?(t, "#")
  end

  # Strip leading ASCII spaces (0x20) only, mirroring the lexer's
  # `count_leading_spaces`. Tabs and other whitespace are deliberately preserved so
  # the pre-scan classifies them exactly as the lexer would.
  defp drop_leading_spaces(<<?\s, rest::binary>>), do: drop_leading_spaces(rest)
  defp drop_leading_spaces(line), do: line

  defp pragma_capture(line) do
    # Anchored at column 0 (`^@`, not `^\s*@`): an INDENTED pragma is not
    # file-leading, and the parser rejects it (:edition_pragma_placement), so
    # resolution must not over-match it either — the two must agree on what a
    # valid pragma is (F1). The INTERIOR `@\s*edition\s*\(` still tolerates the
    # whitespace the parser's tokenizer ignores (`@ edition(...)`, `@edition
    # (...)`) so resolution never misses a pragma the compiler would accept (F-C).
    case Regex.run(~r/^@\s*edition\s*\(\s*"(\d{4})"\s*\)/, line) do
      [_, year] -> year
      nil -> nil
    end
  end

  @doc """
  Resolve the effective edition for a source/project per precedence:
  file `@edition` pragma > `Cure.toml` `[project].edition` > compiler default.
  """
  @spec resolve(map()) :: {:ok, t()} | {:error, term()}
  def resolve(input) do
    # `|| ""` coalesces an explicit `source: nil` (not just an absent key) so the
    # is_binary-guarded pre-scan never crashes on a nil source (F6).
    case pragma_edition(Map.get(input, :source) || "") do
      nil -> resolve_project(Map.get(input, :project_dir))
      pragma -> parse(pragma)
    end
  end

  defp resolve_project(nil), do: {:ok, current()}

  defp resolve_project(dir) do
    case Cure.Project.load(dir) do
      {:ok, %{edition: nil}} ->
        maybe_advise_missing_edition()
        {:ok, current()}

      {:ok, %{edition: edition}} ->
        {:ok, edition}

      {:error, :no_project_file} ->
        {:ok, current()}

      {:error, _} = err ->
        err
    end
  end

  @advisory_key {__MODULE__, :missing_edition_advisory_shown?}

  # Spec §3.2 point 2: a project with a Cure.toml but no `edition` key still
  # resolves (to `current/0`) rather than hard-failing, but logs a one-time
  # advisory so projects converge on an explicit edition. "Once" is
  # process-lifetime via :persistent_term (mirrors the existing memoisation
  # pattern in lib/cure/types/stdlib.ex), not per-file — a whole-project
  # build touching many undeclared files must not spam one warning per file.
  defp maybe_advise_missing_edition do
    case :persistent_term.get(@advisory_key, false) do
      true ->
        :ok

      false ->
        :persistent_term.put(@advisory_key, true)

        Logger.warning(
          "no `edition` declared in Cure.toml — add `edition = \"#{current()}\"` under [project] to pin the language surface this project reads against"
        )
    end
  end

  @doc false
  # Test-only: clears the one-time advisory flag so tests asserting on it are
  # isolated from each other and from resolve/1 calls made by other tests.
  @spec reset_advisory!() :: :ok
  def reset_advisory! do
    :persistent_term.erase(@advisory_key)
    :ok
  end

  @doc """
  The keywords retired at or before `edition`, derived from the migration
  registry (single source of truth). A rule retires each of its
  `retires_keywords` at its `enforced_in` edition: present for editions before
  it, absent at/after. `enforced_in: nil` never retires.

  `Cure.Migrate.rules()` is called at RUNTIME (the default arg) rather than at
  compile time to avoid a compile cycle (lexer → Edition → Migrate → rule
  modules).
  """
  @spec retired_keywords(t(), [Cure.Migrate.Rule.t()]) :: [String.t()]
  def retired_keywords(edition, rules \\ Cure.Migrate.rules()) do
    for r <- rules,
        r.enforced_in != nil,
        compare(edition, r.enforced_in) in [:eq, :gt],
        kw <- r.retires_keywords,
        uniq: true,
        do: kw
  end
end
