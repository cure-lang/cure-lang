defmodule Cure.Lean4Parity.Case do
  @moduledoc """
  One Lean-4-parity corpus entry.

  A parity case pins the CURRENT accept/reject behaviour of a Cure program so
  that later phases of `docs/PATH_TO_LEAN4_PLAN.md` can measure progress
  against a recorded baseline rather than against memory.

  ## Why pins, not goals

  These are REGRESSION PINS, not aspirations. A case whose program Cure
  currently rejects is recorded with `expect: :reject` and a `gap:` naming the
  plan item it belongs to. When a later phase widens reach, the pin flips to
  `:accept` in the same commit that widens it — so every reach change is a
  visible, reviewed diff in this directory rather than a silent behavioural
  drift.

  That is the whole point: `docs/PATH_TO_LEAN4_PLAN.md` §10 invariant 8 says
  "preserve older artifact bytes unless a reviewed semantic change requires
  migration". A flipped pin IS the review.

  ## Fields

    * `:id`     — stable identifier, `"<gap>-<slug>"` (e.g. `"g3-rfl-recursive"`).
    * `:gap`    — the plan's gap register id (`:g1` … `:g11`).
    * `:axis`   — the Lean-parity axis (`:l1` … `:l7`).
    * `:title`  — one line describing what is being pinned.
    * `:source` — the Cure program, as a string.
    * `:expect` — `:accept` or `:reject`.
    * `:reason` — why the current behaviour is what it is (required for
                  `:reject`, so a future reader knows whether the rejection is
                  a deliberate exclusion or a reach gap).
    * `:module` — the module the program defines, for the `:accept` assertion.

  ## Usage

      parity_case(
        id: "g3-rfl-recursive",
        gap: :g3,
        axis: :l2,
        title: "rfl-style reflexivity does not see through a recursive definition",
        expect: :reject,
        reason: "delta-unfolding is gated behind a totality certificate",
        source: "mod Parity.G3RflRecursive\n  ...\n"
      )

  (The real corpus uses heredocs for multi-line `:source` values; they are
  elided here so this documentation example stays a single heredoc.)
  """

  @enforce_keys [:id, :gap, :axis, :title, :source, :expect]
  defstruct [:id, :gap, :axis, :title, :source, :expect, :reason, :module]

  @type t :: %__MODULE__{
          id: String.t(),
          gap: atom(),
          axis: atom(),
          title: String.t(),
          source: String.t(),
          expect: :accept | :reject,
          reason: String.t() | nil,
          module: String.t() | nil
        }

  @doc """
  Build a parity case, validating the shape once at corpus-definition time so a
  malformed entry fails loudly instead of silently pinning nothing.
  """
  @spec parity_case(keyword()) :: t()
  def parity_case(attrs) do
    case struct!(__MODULE__, attrs) do
      %__MODULE__{expect: expect} = c when expect in [:accept, :reject] ->
        validate!(c)

      %__MODULE__{expect: other} ->
        raise ArgumentError,
              "parity case #{inspect(attrs[:id])}: expect must be :accept or :reject, got #{inspect(other)}"
    end
  end

  defp validate!(%__MODULE__{expect: :reject, reason: nil} = c) do
    raise ArgumentError,
          "parity case #{inspect(c.id)}: a :reject pin must carry a :reason so a " <>
            "future reader can tell a deliberate exclusion from a reach gap"
  end

  defp validate!(%__MODULE__{expect: :accept, module: nil} = c) do
    raise ArgumentError,
          "parity case #{inspect(c.id)}: an :accept pin must name the :module it defines"
  end

  defp validate!(%__MODULE__{} = c), do: c

  @doc """
  Compile the case and report whether it was accepted.

  Returns `{:accepted, module}` or `{:rejected, reason}`. Compilation goes
  through `Cure.Compiler.compile_and_load/2`, the same entry point the rest of
  the dependent test suites use, so a pin reflects the real pipeline (lex →
  parse → elaborate → kernel → emit), not a shortcut.
  """
  @spec run(t()) :: {:accepted, module()} | {:rejected, term()}
  def run(%__MODULE__{source: source, id: id}) do
    file = "lean4_parity/#{id}.cure"

    case Cure.Compiler.compile_and_load(source, file: file) do
      {:ok, module} -> {:accepted, module}
      {:error, reason} -> {:rejected, reason}
    end
  end
end
