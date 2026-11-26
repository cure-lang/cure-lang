defmodule Cure.Elab.Tactic.Computed do
  @moduledoc """
  Goal-inspecting computed tactics (C1.2).

  A `tactic <rule> computed by <fn>` rule names an ordinary Cure function that
  receives a **goal value** and returns the checked operations to perform. This
  module is the bridge between that expander and the proof commands:

    * it builds the goal value (`Std.Tactic.Goal`) from the elaborator's
      `Cure.Elab.ProofGoal`,
    * runs the expander at compile time through the same executor the
      `computed by` macro tier uses (`Cure.Elab.MacroExpand`),
    * validates the returned operations against a closed vocabulary, and
    * runs each one as an ordinary proof command via
      `Cure.Elab.Tactic.Script`, so the evidence is kernel-checked at the
      ORIGINAL goal.

  ## The firewall

  The expander is untrusted. It sees a goal value and it returns *requests*.
  It cannot return evidence, a Core term, or a proof object, because the
  operation vocabulary has no such form: `classify_operation/2` accepts an
  operation name from a fixed list and rejects everything else. A rejected
  operation is a diagnostic, never a silent no-op, and the operations that do
  run are the same `simplify`/`rewrite`/`apply`/solver commands an author could
  have written by hand.

  Nothing here adds a kernel rule, a Core constructor, or a postulate.

  ## Why the goal value carries an opaque handle

  The expander is ordinary Cure code, so the goal it inspects has to be an
  ordinary Cure value. The target and hypotheses are quoted `Syntax` (the same
  representation `Std.Syntax` already defines for the macro tier). The `state`
  field is a leaf holding a fresh opaque invocation token. Returned requests
  must retain it; commands still run on the original elaborator goal, not on
  any target the callback reconstructs.

  ## Limits

  The expander is run once per invocation, at compile time, and its operations
  run in the order it emitted them. A failed operation fails the whole tactic.
  Induction templates remain refused: recursive command lowering is not wired
  into this API.
  """

  alias Cure.Compiler.MacroSyntax
  alias Cure.Core.Env
  alias Cure.Elab.{MacroExpand, ProofGoal}
  alias Cure.Elab.Tactic.{Result, Script}

  # The closed operation vocabulary. Each entry names an EXISTING checked proof
  # command; the value is the arity of the argument list the operation accepts.
  # A name outside this table is refused, which is what keeps the expander from
  # inventing a proof step.
  @operations %{
    simplify: 0,
    simplify_using: 1,
    rewrite: 1,
    rewrite_backwards: 1,
    rewrite_all: 1,
    exact: 1,
    apply: 1,
    search: 0,
    positivity: 0,
    assumption: 0,
    decide: 0,
    decide_using: 1,
    omega: 0
  }

  @doc """
  Run a computed tactic at `goal`.

  `meta` is the use-site metadata (`:tactic_expander`, `:keyword`, ...) and
  `arguments` are the captured surface arguments. Returns the ordinary
  `Cure.Elab.Tactic` result shape, or `{:error, reason}` with a diagnostic the
  caller can surface unchanged.
  """
  @spec run(keyword(), [term()], ProofGoal.t()) :: {:ok, Result.t()} | {:error, term()}
  def run(meta, arguments, goal) do
    expander = Keyword.fetch!(meta, :tactic_expander)
    state = handle_syntax(make_ref())

    with {:ok, goal_value} <- goal_value(goal, state),
         {:ok, operations} <- invoke(meta, expander, arguments, goal_value, goal),
         {:ok, steps} <- classify_operations(operations, Keyword.put(meta, :goal_state, MacroSyntax.from_syntax(state))) do
      Script.run({:sequence, steps}, goal)
    end
  end

  # -- The goal value --------------------------------------------------------

  # Build the `Std.Tactic.Goal` value the expander receives. The handle is a
  # fresh reference rendered as a leaf so the value stays ordinary Cure data.
  defp goal_value(goal, state) do
    inspection = ProofGoal.inspect_goal(goal)
    pending = Enum.count(goal.builders, &match?({:assignment, _, _}, &1))
    names = Enum.drop(goal.names, pending)

    target = core_syntax(inspection.target, names)

    hypotheses =
      Enum.map(inspection.hypotheses, fn %{name: name, type: type} ->
        {:ctor, Env.resolve_key(goal.env, goal.env.ctors, :"Std.Tactic#Hypothesis"),
         [
           {:ctor, :"Std.String#String", [core_list(Enum.map(String.to_charlist(name), &{:bounded_lit, &1}))]},
           MacroSyntax.to_core(core_syntax(type, names))
         ]}
      end)

    value =
      {:ctor, Env.resolve_key(goal.env, goal.env.ctors, :"Std.Tactic#Goal"),
       [MacroSyntax.to_core(target), core_list(hypotheses), MacroSyntax.to_core(state)]}

    {:ok, value}
  end

  # Inspection is deliberately structural, not a quotation of evaluator values
  # or a lossy pass through parser-AST reflection. These nodes are data only.
  defp core_syntax({:level_type}, _names), do: {:syn_node, :level_type, [], []}

  defp core_syntax({:type, {:omega, n}}, _names),
    do: {:syn_node, :type, [], [{:syn_node, :omega, [index: {:s_int, n}], []}]}

  defp core_syntax({:type, {:finite, level}}, names),
    do: {:syn_node, :type, [], [{:syn_node, :finite, [], [level_syntax(level, names)]}]}

  defp core_syntax({:level_value, level}, names),
    do: {:syn_node, :level_value, [], [level_syntax(level, names)]}

  defp core_syntax({:data, name, params, indices}, names),
    do:
      {:syn_node, short_name(name), [name: {:s_atom, name}, parameters: {:s_int, length(params)}],
       Enum.map(params ++ indices, &core_syntax(&1, names))}

  defp core_syntax({:ctor, name, args}, names),
    do: {:syn_node, short_name(name), [name: {:s_atom, name}], Enum.map(args, &core_syntax(&1, names))}

  defp core_syntax({:global, name}, _names),
    do: {:syn_leaf, :global, [name: {:s_atom, name}], {:s_atom, name}}

  defp core_syntax({:var, index}, names),
    do: {:syn_leaf, :variable, [index: {:s_int, index}], {:s_str, Enum.at(names, index, "$#{index}")}}

  defp core_syntax({tag, grade, domain, body}, names) when tag in [:pi, :lam] do
    {:syn_node, tag, [grade: {:s_str, inspect(grade)}],
     [core_syntax(domain, names), core_syntax(body, ["$binder" | names])]}
  end

  defp core_syntax({:let, grade, type, value, body}, names) do
    {:syn_node, :let, [grade: {:s_str, inspect(grade)}],
     [core_syntax(type, names), core_syntax(value, names), core_syntax(body, ["$binder" | names])]}
  end

  defp core_syntax({:case, scrutinee, motive, branches}, names) do
    branches =
      Enum.map(branches, fn {name, arity, body} ->
        {:syn_node, :branch, [name: {:s_atom, name}, arity: {:s_int, arity}],
         [core_syntax(body, List.duplicate("$binder", arity) ++ names)]}
      end)

    {:syn_node, :case, [], [core_syntax(scrutinee, names), core_syntax(motive, names) | branches]}
  end

  defp core_syntax(term, names) when is_tuple(term) do
    [tag | fields] = Tuple.to_list(term)
    {:syn_node, tag, [], Enum.map(fields, &core_syntax(&1, names))}
  end

  defp core_syntax(items, names) when is_list(items),
    do: {:syn_node, :list, [], Enum.map(items, &core_syntax(&1, names))}

  defp core_syntax(value, _names) when is_integer(value), do: {:syn_raw, {:s_int, value}}
  defp core_syntax(value, _names) when is_float(value), do: {:syn_raw, {:s_float, value}}
  defp core_syntax(value, _names) when is_binary(value), do: {:syn_raw, {:s_str, value}}
  defp core_syntax(value, _names) when is_atom(value), do: {:syn_raw, {:s_atom, value}}

  defp level_syntax(%Cure.Core.UniverseLevel{constant: constant, atoms: atoms}, names) do
    {:syn_node, :level_nf, [constant: {:s_int, constant}],
     Enum.map(atoms, fn {atom, offset} ->
       {:syn_node, :level_atom, [offset: {:s_int, offset}], [core_syntax(atom, names)]}
     end)}
  end

  defp short_name(name), do: name |> Atom.to_string() |> String.split("#") |> List.last() |> String.to_atom()

  defp core_list([]), do: {:ctor, :"Std.List#Nil", []}
  defp core_list([head | tail]), do: {:ctor, :"Std.List#Cons", [head, core_list(tail)]}

  defp handle_syntax(reference) do
    encoded =
      reference
      |> :erlang.term_to_binary()
      |> Base.encode16()

    {:syn_leaf, :tactic_state, [], {:s_str, encoded}}
  end

  # -- Invoking the expander -------------------------------------------------

  # The expander is ordinary Cure, so it is run through the same compile-time
  # executor the `computed by` macro tier uses. That executor elaborates the
  # reference, checks the application, normalizes the result, and reflects it
  # back to surface syntax -- exactly the machinery a goal-value API needs.
  defp invoke(meta, expander, arguments, goal_value, goal) do
    inputs = Enum.map(arguments, &MacroSyntax.to_core(MacroSyntax.to_syntax(&1))) ++ [goal_value]

    case MacroExpand.expand_typed(
           meta,
           expander,
           inputs,
           goal.env
         ) do
      {:ok, expanded} -> operations_from_expansion(expanded, meta)
      {:error, _} = error -> error
    end
  end

  # MacroExpand already unwraps Expanded and returns author refusals as errors.
  defp operations_from_expansion({:tactic_operation, _, _} = operation, _site_meta), do: {:ok, [operation]}
  defp operations_from_expansion({:list, _, operations}, _site_meta), do: {:ok, operations}

  defp operations_from_expansion(other, site_meta),
    do: {:error, {:invalid_tactic_result, other, site_meta}}

  # -- Classifying operations ------------------------------------------------

  defp classify_operations(operations, meta) when length(operations) > 256,
    do: {:error, {:invalid_tactic_result, :too_many_operations, Keyword.delete(meta, :goal_state)}}

  defp classify_operations(operations, meta) do
    operations
    |> Enum.reduce_while({:ok, []}, fn operation, {:ok, acc} ->
      case classify_operation(operation, meta) do
        {:ok, step} -> {:cont, {:ok, [step | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, steps} -> {:ok, Enum.reverse(steps)}
      {:error, _} = error -> error
    end
  end

  # One operation is a `tactic_operation` node: its `:kind` attribute names the
  # command and its children are the arguments. The name is looked up in the
  # closed table above; an unknown name is refused here rather than reaching the
  # proof commands.
  defp classify_operation({:tactic_operation, meta, arguments}, site_meta) do
    kind = Keyword.get(meta, :kind)
    state = Keyword.fetch!(site_meta, :goal_state)
    site_meta = Keyword.delete(site_meta, :goal_state)

    cond do
      Keyword.get_values(meta, :state) != [state] ->
        {:error, {:invalid_tactic_state, kind, site_meta}}

      Keyword.get_values(meta, :kind) != [kind] ->
        {:error, {:invalid_tactic_operation, :duplicate_kind, site_meta}}

      MacroExpand.contains_computed_use?(arguments) ->
        {:error, {:invalid_tactic_operation_argument, kind, site_meta}}

      true ->
        case Map.fetch(@operations, kind) do
          {:ok, arity} when arity == length(arguments) ->
            build_command(kind, arguments, site_meta)

          {:ok, _arity} ->
            {:error, {:invalid_tactic_operation_arity, kind, length(arguments), site_meta}}

          :error ->
            {:error, {:unknown_tactic_operation, kind, site_meta}}
        end
    end
  end

  defp classify_operation(other, site_meta),
    do: {:error, {:invalid_tactic_operation, other, site_meta}}

  defp build_command(:simplify, [], site_meta),
    do: {:ok, {:command, {:simplify_command, command_meta(site_meta), []}}}

  defp build_command(:simplify_using, [{:list, _meta, items}], site_meta),
    do:
      {:ok, {:command, {:simplify_command, Keyword.put(command_meta(site_meta), :using, :rules), [{:list, [], items}]}}}

  defp build_command(:rewrite, [proof], site_meta),
    do: {:ok, {:command, {:rewrite_command, rewrite_meta(site_meta, :forward, :goal), [proof]}}}

  defp build_command(:rewrite_backwards, [proof], site_meta),
    do: {:ok, {:command, {:rewrite_command, rewrite_meta(site_meta, :backwards, :goal), [proof]}}}

  defp build_command(:rewrite_all, [proof], site_meta),
    do: {:ok, {:command, {:rewrite_command, rewrite_meta(site_meta, :forward, :all), [proof]}}}

  defp build_command(:exact, [proof], site_meta),
    do: {:ok, {:command, {:proof_application, Keyword.put(command_meta(site_meta), :kind, :exact), [proof]}}}

  defp build_command(:apply, [proof], site_meta),
    do: {:ok, {:command, {:proof_application, Keyword.put(command_meta(site_meta), :kind, :apply), [proof]}}}

  defp build_command(kind, [], site_meta) when kind in [:search, :positivity, :assumption, :decide, :omega],
    do: {:ok, {:command, {:solver_command, Keyword.put(command_meta(site_meta), :solver, kind), []}}}

  defp build_command(:decide_using, [decision], site_meta),
    do: {:ok, {:command, {:solver_command, Keyword.put(command_meta(site_meta), :solver, :decide), [decision]}}}

  defp build_command(kind, _arguments, site_meta),
    do: {:error, {:invalid_tactic_operation_argument, kind, site_meta}}

  defp command_meta(site_meta) do
    [line: Keyword.get(site_meta, :line), col: Keyword.get(site_meta, :col)] ++ source_info(site_meta)
  end

  defp rewrite_meta(site_meta, direction, target),
    do: [direction: direction, target: target] ++ command_meta(site_meta)

  defp source_info(site_meta) do
    case Keyword.get(site_meta, :source_info) do
      nil -> []
      info -> [source_info: info]
    end
  end
end
