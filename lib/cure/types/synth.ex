defmodule Cure.Types.Synth do
  @moduledoc """
  Typed-hole synthesis engine (v0.27.0).

  Given a hole's goal type, the local variable context, an effect
  bound, and a depth budget, produce a ranked list of candidate
  expressions that are well-typed at the hole's position.

  This is a pragmatic, non-complete search -- comparable to Haskell's
  `hoogle` plus a small unifier. The candidates are *structurally*
  type-correct against a lightweight canonicaliser of the goal type
  (`display/1`-style comparison) and are ranked by:

    1. Shorter expressions beat longer ones.
    2. Pure candidates beat effectful ones when the effect budget is
       tight.
    3. Local-context variables beat stdlib functions.
    4. Fewer type-variable instantiations beat many.

  ## Seeded stdlib catalogue

  The search is seeded with a hand-maintained subset of the Cure
  stdlib: `Std.Core.{identity, compose}`, `Std.Option.{some, none,
  unwrap_or}`, `Std.Result.{ok, error}`, and `Std.List.{head, tail,
  map, filter, length, reverse}`. Additional seeds are welcome as
  follow-up work; the catalogue is kept small intentionally so the
  search stays fast on small budgets.

  Pipeline events: `:synthesis, :candidate` per emitted candidate and
  `:synthesis, :no_candidates` when the bounded catalogue search has no usable
  result. This is observational telemetry, not a compiler diagnostic: returning
  no hole suggestions is a valid synthesis result rather than an error.
  """

  alias Cure.Pipeline.Events
  alias Cure.Types.Holes

  @type goal :: String.t()
  @type ctx :: %{optional(String.t()) => String.t()}
  @type candidate :: %{expr: String.t(), cost: non_neg_integer(), effects: [atom()]}

  @doc """
  Synthesise up to `n` candidates for the given goal and context.

  ## Options

    * `:depth`   -- search depth budget (default `3`).
    * `:max`     -- maximum number of candidates to return (default `3`).
    * `:effects` -- set of permitted effects; candidates that require
      effects outside this set are excluded. Default: `[]` (pure).
    * `:file` / `:line` -- used for pipeline event metadata.

  Returns a list of candidate maps ordered by cost (ascending).
  """
  @spec synthesise(goal(), ctx(), Holes.ctx(), keyword()) :: [candidate()]
  def synthesise(goal, ctx, _hole_ctx, opts \\ []) when is_binary(goal) and is_map(ctx) do
    depth = Keyword.get(opts, :depth, 3)
    max_results = Keyword.get(opts, :max, 3)
    effects = Keyword.get(opts, :effects, [])
    file = Keyword.get(opts, :file, "nofile")
    line = Keyword.get(opts, :line, 1)

    candidates =
      []
      |> enumerate_vars(goal, ctx)
      |> enumerate_stdlib(goal, ctx, depth)
      |> enumerate_pipes(goal, ctx, depth)

    filtered =
      candidates
      |> Enum.filter(fn c -> Enum.all?(c.effects, &(&1 in effects)) end)
      |> Enum.sort_by(& &1.cost)
      |> Enum.take(max_results)

    Enum.each(filtered, fn c ->
      Events.emit(:synthesis, :candidate, c, Events.meta(file, line))
    end)

    if filtered == [] do
      Events.emit(
        :synthesis,
        :no_candidates,
        %{goal: goal, depth: depth},
        Events.meta(file, line)
      )
    end

    filtered
  end

  # -- Variable enumeration --------------------------------------------------

  defp enumerate_vars(acc, goal, ctx) do
    ctx
    |> Enum.flat_map(fn {name, type} ->
      if type_compatible?(type, goal) do
        [%{expr: name, cost: 1, effects: []}]
      else
        []
      end
    end)
    |> Kernel.++(acc)
  end

  # -- Stdlib catalogue ------------------------------------------------------

  @stdlib [
    # name,                    arg_types,                 ret_type,     effects
    {"Std.Core.identity", ["T"], "T", []},
    {"Std.Option.some", ["T"], "Option(T)", []},
    {"Std.Option.none", [], "Option(T)", []},
    {"Std.Option.unwrap_or", ["Option(T)", "T"], "T", []},
    {"Std.Result.ok", ["T"], "Result(T,E)", []},
    {"Std.Result.error", ["E"], "Result(T,E)", []},
    {"Std.List.head", ["List(T)"], "Option(T)", []},
    {"Std.List.tail", ["List(T)"], "List(T)", []},
    {"Std.List.length", ["List(T)"], "Int", []},
    {"Std.List.reverse", ["List(T)"], "List(T)", []},
    {"Std.List.map", ["List(T)", "(T) -> U"], "List(U)", []},
    {"Std.List.filter", ["List(T)", "(T) -> Bool"], "List(T)", []},
    {"Std.Math.abs", ["Int"], "Int", []},
    {"Std.Math.sqrt", ["Float"], "Float", []},
    {"Std.String.length", ["String"], "Int", []},
    {"Std.String.upcase", ["String"], "String", []},
    {"Std.Io.println", ["String"], "Atom", [:io]}
  ]

  defp enumerate_stdlib(acc, goal, ctx, depth) when depth > 0 do
    new =
      @stdlib
      |> Enum.flat_map(fn {name, args, ret, effects} ->
        if type_compatible?(ret, goal) do
          case find_args(args, ctx) do
            {:ok, arg_names} ->
              arg_string = Enum.join(arg_names, ", ")
              expr = "#{name}(#{arg_string})"
              [%{expr: expr, cost: 2 + length(args), effects: effects}]

            :no_fit ->
              []
          end
        else
          []
        end
      end)

    new ++ acc
  end

  defp enumerate_stdlib(acc, _goal, _ctx, _depth), do: acc

  # -- Pipe enumeration ------------------------------------------------------
  # Try `var |> fn` for each var in context and each stdlib function whose
  # first argument accepts that variable's type and whose return type
  # matches the goal.

  defp enumerate_pipes(acc, goal, ctx, depth) when depth > 1 do
    new =
      Enum.flat_map(ctx, fn {var_name, var_type} ->
        Enum.flat_map(@stdlib, fn {fn_name, args, ret, effects} ->
          case args do
            [first | _rest] ->
              if type_compatible?(var_type, first) and type_compatible?(ret, goal) and
                   length(args) == 1 do
                [%{expr: "#{var_name} |> #{fn_name}", cost: 3, effects: effects}]
              else
                []
              end

            _ ->
              []
          end
        end)
      end)

    new ++ acc
  end

  defp enumerate_pipes(acc, _goal, _ctx, _depth), do: acc

  # -- Type compatibility ----------------------------------------------------
  # A *very* permissive structural matcher. Treats single-character
  # uppercase identifiers (`T`, `U`, `E`) as universally-quantified
  # type variables that match anything. Everything else must match
  # exactly (up to whitespace).

  defp type_compatible?(a, b) when is_binary(a) and is_binary(b) do
    aa = canon(a)
    bb = canon(b)

    cond do
      aa == bb -> true
      type_var?(aa) -> true
      type_var?(bb) -> true
      true -> unify_shape(aa, bb)
    end
  end

  defp type_compatible?(_, _), do: false

  defp type_var?("T"), do: true
  defp type_var?("U"), do: true
  defp type_var?("E"), do: true
  defp type_var?(_), do: false

  # Try a shallow structural match: allow `Option(T)` to match `Option(Int)`.
  defp unify_shape(a, b) do
    case {Regex.run(~r/^(\w+)\((.*)\)$/, a), Regex.run(~r/^(\w+)\((.*)\)$/, b)} do
      {[_, head1, _args1], [_, head2, _args2]} when head1 == head2 -> true
      _ -> false
    end
  end

  defp canon(s), do: String.replace(s, ~r/\s+/, "")

  # -- Argument fitter -------------------------------------------------------

  defp find_args(arg_types, ctx) do
    fit_args(arg_types, ctx, [])
  end

  defp fit_args([], _ctx, acc), do: {:ok, Enum.reverse(acc)}

  defp fit_args([t | rest], ctx, acc) do
    match =
      Enum.find(ctx, fn {_name, type} ->
        type_compatible?(type, t)
      end)

    case match do
      {name, _} -> fit_args(rest, ctx, [name | acc])
      nil -> :no_fit
    end
  end
end
