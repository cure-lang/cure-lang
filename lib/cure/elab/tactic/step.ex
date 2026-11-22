defmodule Cure.Elab.Tactic.Step do
  @moduledoc """
  The closed vocabulary a `tactic` macro rule may expand to.

  Phase 3 of `docs/PATH_TO_LEAN4_PLAN.md` makes the proof vocabulary *open*: a
  library, not just the compiler, can define a new proof command. The safety
  argument is structural, not disciplinary:

  > A `tactic` rule expands to `Cure.Elab.Tactic` combinators — **never** to Core
  > terms. A user tactic may only produce goals and apply existing steps.

  A template is Cure source, so it cannot literally name an Elixir function
  like `Tactic.seq/2`. What it produces instead is a **tactic script**: an
  ordinary surface AST node whose shape is restricted to the steps below. This
  module owns that restriction — `classify/1` is the whitelist, and everything
  outside it is rejected rather than interpreted.

  ## Why a whitelist and not a blacklist

  The negative control the plan asks for is "a tactic emitting a raw Core node
  is rejected". A blacklist would have to enumerate every Core constructor and
  would silently admit the next one added to the kernel. A whitelist fails
  closed: a node is a step only if it is one of the shapes below, so a Core
  term, an arbitrary expression, a `let` chain, a lambda, or a call to an
  unknown function is `:not_a_step` by construction.

  ## The vocabulary

  Each step names an EXISTING proof command — the same ones `ProofGoal.command/2`
  already dispatches. That is what makes a tactic a *composition* facility
  rather than a second prover: `tactic close becomes simplify` cannot prove
  anything `simplify` could not, it only gives the composition a name.

    * `simplify` / `simplify using [rules]` — `:simplify_command`
    * `rewrite using e [all]` / `rewrite backwards using e` — `:rewrite_command`
    * `exact e` / `apply e` — `:proof_application`
    * `by search` / `by positivity` / `by decide [using e]` — `:solver_command`
    * `induction n` with its `case` block — `:induction`
    * `have name: T = e` — a checked local fact (`:assignment` with `:have`)

  Composition is `seq`: a tactic's steps run in order, and the tactic fails if
  any step fails. `Tactic.seq/2` is the combinator; see
  `Cure.Elab.Tactic.Script.run/2`.

  ## What a step may NOT be

  `classify/1` returns `{:error, reason}` for anything else, and the reason is
  surfaced as a diagnostic rather than a silent no-op. The cases that matter:

    * a Core-shaped tuple (`{:app, …}`, `{:lam, …}`, `{:global, …}`, …) — a
      tactic that tries to hand the kernel a term directly;
    * a bare expression that is not a command (a variable, a literal, a
      function call) — a tactic that tries to *be* its own proof;
    * a `:block` / `:lambda` / `:pattern_match` — control flow the tactic
      vocabulary deliberately does not expose, because each would need its own
      soundness argument about which goal the branches see.
  """

  @typedoc "A classified tactic step: a command node plus the combinator it needs."
  @type step :: {:command, tuple()} | {:sequence, [step()]}

  # The surface AST tags a tactic step may use. Kept as a plain module
  # attribute rather than a `@typedoc`: it documents a closed vocabulary, not a
  # type.
  @command_tags [
    :simplify_command,
    :rewrite_command,
    :proof_application,
    :solver_command,
    :induction
  ]

  @doc """
  Classify one expansion node as a tactic step.

  Returns `{:ok, step}` when the node is a member of the closed vocabulary, or
  `{:error, reason}` naming why it is not. `reason` is a stable atom so a
  diagnostic can be built from it without depending on `inspect/1` output.
  """
  @spec classify(term()) :: {:ok, step()} | {:error, atom()}
  def classify({:block, _meta, statements}) when is_list(statements) do
    # A block is a SEQUENCE of steps, which is how a multi-command tactic body
    # is written. An empty block is not a tactic: it would silently succeed on
    # every goal.
    case statements do
      [] -> {:error, :empty_tactic_body}
      statements -> classify_sequence(statements)
    end
  end

  def classify({tag, _meta, _children} = node) when tag in @command_tags, do: {:ok, {:command, node}}

  def classify({:assignment, meta, [{:variable, _vmeta, _name}, _rhs]} = node) when is_list(meta) do
    # Only a `have`-shaped assignment is a step. A plain `let` is an ordinary
    # local binding and has no goal semantics.
    if Keyword.get(meta, :have, false),
      do: {:ok, {:command, node}},
      else: {:error, :not_a_step}
  end

  def classify({tag, _meta, _children}) when is_atom(tag), do: {:error, core_tag_reason(tag)}

  def classify(_other), do: {:error, :not_a_step}

  defp classify_sequence(statements) do
    statements
    |> Enum.reduce_while({:ok, []}, fn statement, {:ok, acc} ->
      case classify(statement) do
        {:ok, step} -> {:cont, {:ok, [step | acc]}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:ok, steps} -> {:ok, {:sequence, Enum.reverse(steps)}}
      {:error, _} = error -> error
    end
  end

  # A Core constructor reaching a tactic expansion is the exact failure the
  # plan's negative control names, so it gets its own reason rather than being
  # lumped in with "not a step". These are the kernel's own term tags; naming
  # them here is documentation, not a second source of truth — the whitelist
  # above is what actually decides.
  #
  # `:hole` is deliberately NOT in this list: a `?goal` in a tactic body is a
  # hole, not an attempt to smuggle in a term, and telling its author "a tactic
  # may not emit a Core term" would send them looking in the wrong place.
  @core_tags [:app, :lam, :pi, :let, :case, :ctor, :global, :var, :data, :meta, :type]

  defp core_tag_reason(tag) when tag in @core_tags, do: :core_term_is_not_a_tactic
  defp core_tag_reason(_tag), do: :not_a_step
end
