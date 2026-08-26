defmodule Cure.Elab.ProofGoal do
  @moduledoc "Typed, compile-time-only state for compositional proof commands."

  alias Cure.Core.{Context, Env, Eval, Grade, Kernel, Quote}
  alias Cure.Diagnostic.{ProofChainMismatchProblem, ProofChainSyntaxProblem, RewriteProblem}
  alias Cure.Elab.{Elaborator, Rewrite, Subst}
  alias Cure.MetaAST.Metadata

  @enforce_keys [:expected, :names, :context, :env, :source, :status, :builders, :trace]
  defstruct [:expected, :names, :context, :env, :source, :status, :builders, :trace]

  @type status :: :open | :closed
  @type t :: %__MODULE__{
          expected: Cure.Core.Term.t(),
          names: [String.t()],
          context: Cure.Core.Context.t(),
          env: Cure.Core.Env.t(),
          source: term(),
          status: status(),
          builders: [term()],
          trace: [term()]
        }

  @type command_result :: {:open, t()} | {:closed, Cure.Core.Term.t(), [term()]} | {:error, term()}

  def run({:proof_justification, meta, statements}, expected, names, context, env, step_index) do
    goal = %__MODULE__{
      expected: expected,
      names: names,
      context: context,
      env: env,
      source: meta,
      status: :open,
      builders: [],
      trace: []
    }

    execute(statements, goal, step_index)
  end

  defp execute([], %__MODULE__{status: :open} = goal, step_index) do
    info = Metadata.source_info(goal.source)

    {:error,
     {:proof_chain_mismatch,
      %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: step_index,
        justification: info && info.whole,
        residual_goal: goal.expected,
        cause: {:open_goal, fact_names(goal.builders)}
      }}}
  end

  defp execute([statement | rest], %__MODULE__{status: :open} = goal, step_index) do
    case command(statement, goal) do
      {:open, next_goal} ->
        execute(rest, next_goal, step_index)

      {:closed, evidence, trace} when rest == [] ->
        {:ok, evidence, trace}

      {:closed, _evidence, trace} ->
        first_unreachable = hd(rest)
        closed_at = trace |> List.last() |> trace_span()

        {:error,
         {:proof_chain_syntax,
          %ProofChainSyntaxProblem{
            kind: :unreachable_proof_statement,
            construct: closed_at || surface_span(goal.source),
            step: surface_span(first_unreachable),
            observed: expression_kind(first_unreachable),
            expected: :end_of_justification
          }}}

      {:error, _} = error ->
        error
    end
  end

  defp command({:assignment, meta, [{:variable, _, name}, _rhs]} = statement, goal)
       when is_list(meta) do
    if Keyword.get(meta, :have, false) do
      {:open,
       %{
         goal
         | names: [name | goal.names],
           builders: goal.builders ++ [statement],
           trace: goal.trace ++ [{:have, name, surface_span(statement)}]
       }}
    else
      close_with_expression(statement, goal)
    end
  end

  defp command({:rewrite_command, meta, [proof_ast]}, goal) do
    case Keyword.get(meta, :target, :goal) do
      :goal -> rewrite_goal(proof_ast, meta, goal, nil)
      {:at, occurrence} -> rewrite_goal(proof_ast, meta, goal, occurrence)
      {:in, name} -> rewrite_hypothesis(proof_ast, meta, goal, name)
    end
  end

  defp command({:simplify_command, meta, rules}, goal) do
    if Keyword.get(meta, :using) == :proof do
      adapt_existing_proof(hd(rules), meta, goal)
    else
      simplify_command_rules(meta, rules, goal)
    end
  end

  defp command(statement, goal), do: close_with_expression(statement, goal)

  defp simplify_command_rules(meta, rules, goal) do
    with {:ok, simplified} <- simplify_rules(rules, goal, meta),
         {:ok, evidence, trace} <-
           Cure.Elab.Simplifier.solve(simplified.expected, simplified.context, surface_span(meta)) do
      transports = Enum.reject(simplified.builders, &match?({:assignment, _, _}, &1))
      evidence = Enum.reduce(Enum.reverse(transports), evidence, &apply_builder/2)
      {:closed, evidence, simplified.trace ++ trace}
    else
      {:error, {:simplification_failed, problem}} ->
        {:error, {:simplification_failed, enrich_simplification(problem, goal.names)}}

      {:error, _} = error ->
        error
    end
  end

  defp enrich_simplification(problem, names) do
    %{
      problem
      | before_surface: Cure.Elab.ProofDisplay.format(problem.before_goal, names),
        after_surface: Cure.Elab.ProofDisplay.format(problem.after_goal, names)
    }
  end

  defp adapt_existing_proof(proof_ast, meta, goal) do
    surface_builders = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))
    proof_block = {:block, [], surface_builders ++ [proof_ast]}
    original_names = Enum.drop(goal.names, length(surface_builders))
    depth = Context.length(goal.context)
    expected_value = Eval.eval(goal.expected, Context.env(goal.context))

    with {:ok, proof, proof_type} <-
           Elaborator.elaborate_expr_typed(proof_block, original_names, goal.context, goal.env),
         {:ok, proof, carrier, left, right} <- adaptation_evidence(proof, proof_type, goal, depth) do
      supplied = Rewrite.mk_eq(carrier, left, right)
      simplified_supplied = Kernel.normalize(goal.context, supplied)
      simplified_goal = Kernel.normalize(goal.context, goal.expected)

      cond do
        Kernel.check(goal.context, proof, expected_value) == :ok ->
          transports = Enum.reject(goal.builders, &match?({:assignment, _, _}, &1))
          evidence = Enum.reduce(Enum.reverse(transports), proof, &apply_builder/2)

          {:closed, evidence,
           goal.trace ++ [%{id: "adapt-direct", kind: :proof_adaptation, rule: surface_span(proof_ast)}]}

        true ->
          {:ok, symmetric} = Rewrite.symmetry_proof(proof, carrier, left)

          if Kernel.check(goal.context, symmetric, expected_value) == :ok do
            transports = Enum.reject(goal.builders, &match?({:assignment, _, _}, &1))
            evidence = Enum.reduce(Enum.reverse(transports), symmetric, &apply_builder/2)

            {:closed, evidence,
             goal.trace ++ [%{id: "adapt-symmetric", kind: :proof_adaptation, rule: surface_span(proof_ast)}]}
          else
            adaptation_error(meta, proof_ast, goal, supplied, simplified_supplied, simplified_goal, :proof_mismatch)
          end
      end
    else
      {:error, cause} ->
        adaptation_error(meta, proof_ast, goal, nil, nil, Kernel.normalize(goal.context, goal.expected), cause)

      :no_match ->
        adaptation_error(
          meta,
          proof_ast,
          goal,
          nil,
          nil,
          Kernel.normalize(goal.context, goal.expected),
          :no_matching_equation_instance
        )
    end
  end

  defp adaptation_evidence(proof, proof_type, goal, depth) do
    case generated_rule(proof, goal.env) do
      {:ok, theorem_type} ->
        instantiate_generated_rule(theorem_type, proof, goal.expected, goal)

      :ordinary ->
        with {:ok, ty_value, left_value, right_value} <-
               Rewrite.eq_parts(proof_type, Context.signature(goal.context)) do
          {:ok, proof, Kernel.normalize(goal.context, Quote.reify(ty_value, depth)),
           Kernel.normalize(goal.context, Quote.reify(left_value, depth)),
           Kernel.normalize(goal.context, Quote.reify(right_value, depth))}
        end

      {:error, cause} ->
        {:error, cause}
    end
  end

  defp adaptation_error(meta, proof_ast, goal, supplied, simplified_supplied, simplified_goal, cause) do
    {:error,
     {:simplification_failed,
      %Cure.Diagnostic.SimplificationProblem{
        kind: :proof_mismatch,
        command: surface_span(meta),
        rule: surface_span(proof_ast),
        before_goal: goal.expected,
        after_goal: simplified_goal,
        before_surface: Cure.Elab.ProofDisplay.format(goal.expected, goal.names),
        after_surface: Cure.Elab.ProofDisplay.format(simplified_goal, goal.names),
        supplied_proposition: supplied,
        simplified_supplied: simplified_supplied,
        simplified_goal: simplified_goal,
        supplied_surface: supplied && Cure.Elab.ProofDisplay.format(supplied, goal.names),
        simplified_supplied_surface:
          simplified_supplied && Cure.Elab.ProofDisplay.format(simplified_supplied, goal.names),
        progressed_rules: [],
        trace_ids: [],
        cause: cause
      }}}
  end

  defp simplify_rules([], goal, _meta), do: {:ok, goal}
  defp simplify_rules([{:list, _list_meta, rules}], goal, meta), do: simplify_rule_list(rules, goal, meta)

  defp simplify_rules(_other, goal, meta),
    do: simplification_error(:inadmissible_rule, meta, goal, :rules_must_be_a_list)

  defp simplify_rule_list(rules, goal, meta) do
    Enum.reduce_while(rules, {:ok, goal}, fn rule, {:ok, current} ->
      case apply_simplification_rule(rule, current, meta) do
        {:ok, next} -> {:cont, {:ok, next}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp apply_simplification_rule(rule_ast, goal, meta) do
    surface_builders = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))
    proof_block = {:block, [], surface_builders ++ [rule_ast]}
    original_names = Enum.drop(goal.names, length(surface_builders))
    depth = Context.length(goal.context)

    with {:ok, proof, proof_type} <-
           Elaborator.elaborate_expr_typed(proof_block, original_names, goal.context, goal.env) do
      case generated_rule(proof, goal.env) do
        {:ok, theorem_type} ->
          simplify_generated_fixed_point(proof, theorem_type, rule_ast, goal, meta, MapSet.new(), 0)

        :ordinary ->
          with {:ok, ty_value, a_value, b_value} <- Rewrite.eq_parts(proof_type, Context.signature(goal.context)),
               ty = Kernel.normalize(goal.context, Quote.reify(ty_value, depth)),
               a = Kernel.normalize(goal.context, Quote.reify(a_value, depth)),
               b = Kernel.normalize(goal.context, Quote.reify(b_value, depth)),
               true <- simplification_measure(a) > simplification_measure(b) do
            simplify_rule_fixed_point(proof, ty, a, b, rule_ast, goal, meta, MapSet.new(), 0)
          else
            false -> simplification_error(:inadmissible_rule, meta, goal, :non_decreasing_orientation, rule_ast)
            {:error, cause} -> simplification_error(:inadmissible_rule, meta, goal, cause, rule_ast)
          end

        {:error, cause} ->
          simplification_error(:inadmissible_rule, meta, goal, cause, rule_ast)
      end
    else
      {:error, cause} -> simplification_error(:inadmissible_rule, meta, goal, cause, rule_ast)
    end
  end

  defp generated_rule({:global, theorem}, env) do
    admit_generated_rule(env, theorem)
  end

  defp generated_rule(_proof, _env), do: :ordinary

  @doc false
  def admit_generated_rule(env, theorem) do
    case Env.get_def(env, theorem) do
      %{generated_equation: true, type: type} ->
        if Env.certified?(env, theorem) and Kernel.check_def(env, theorem) == :ok,
          do: {:ok, type},
          else: {:error, :forged_generated_equation}

      _ ->
        :ordinary
    end
  end

  defp simplify_generated_fixed_point(_proof, _type, _rule, goal, meta, _visited, 256),
    do: simplification_error(:resource_guard, meta, goal, {:step_ceiling, 256})

  defp simplify_generated_fixed_point(proof, theorem_type, rule, goal, meta, visited, steps) do
    normalized = Kernel.normalize(goal.context, goal.expected)
    fingerprint = :erlang.term_to_binary(normalized)

    cond do
      MapSet.member?(visited, fingerprint) ->
        simplification_error(:resource_guard, meta, goal, :visited_state_cycle)

      true ->
        case instantiate_generated_rule(theorem_type, proof, normalized, goal) do
          {:ok, instantiated_proof, ty, left, right} ->
            case Rewrite.directed_plan(instantiated_proof, ty, left, right, normalized, :forward, 1) do
              {:ok, build, rewritten, _occurrences} ->
                next = %{
                  goal
                  | expected: rewritten,
                    builders: goal.builders ++ [{:transport, build}],
                    trace:
                      goal.trace ++
                        [%{id: "equation-#{steps + 1}", kind: :defining_equation, rule: surface_span(rule)}]
                }

                simplify_generated_fixed_point(
                  proof,
                  theorem_type,
                  rule,
                  next,
                  meta,
                  MapSet.put(visited, fingerprint),
                  steps + 1
                )

              {:error, cause} ->
                simplification_error(:inadmissible_rule, meta, goal, cause, rule)
            end

          :no_match ->
            {:ok, goal}

          {:error, cause} ->
            simplification_error(:inadmissible_rule, meta, goal, cause, rule)
        end
    end
  end

  defp instantiate_generated_rule(theorem_type, proof, goal_term, goal) do
    {telescope, proposition} = peel_pi(theorem_type, [])
    count = length(telescope)

    case proposition do
      {:data, equality, [carrier], [left, right]} ->
        if equality == Cure.Core.Inductive.builtin(Context.signature(goal.context), :eq) do
          goal_term
          |> core_subterms()
          |> Enum.find_value(:no_match, fn candidate ->
            case match_rule(left, candidate, count, %{}) do
              {:ok, bindings} ->
                case complete_rule_args(telescope, bindings, goal_term, goal) do
                  {:ok, args} ->
                    specialized_carrier = Subst.instantiate(carrier, args)
                    specialized_left = Subst.instantiate(left, args)
                    specialized_right = Subst.instantiate(right, args)
                    specialized_proof = Enum.reduce(args, proof, fn argument, call -> {:app, call, argument} end)
                    {:ok, specialized_proof, specialized_carrier, specialized_left, specialized_right}

                  :no_match ->
                    false
                end

              _ ->
                false
            end
          end)
        else
          {:error, :generated_rule_not_equality}
        end

      _ ->
        {:error, :generated_rule_not_equality}
    end
  end

  defp complete_rule_args(telescope, bindings, goal_term, goal) do
    count = length(telescope)

    telescope
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, []}, fn {{_grade, domain}, position}, {:ok, args} ->
      index = count - 1 - position

      case Map.fetch(bindings, index) do
        {:ok, argument} ->
          {:cont, {:ok, args ++ [argument]}}

        :error ->
          instantiated_domain = Subst.instantiate(domain, args)
          expected = Eval.eval(instantiated_domain, Context.env(goal.context))

          case Enum.find(core_subterms(goal_term), &(Kernel.check(goal.context, &1, expected) == :ok)) do
            nil -> {:halt, :no_match}
            argument -> {:cont, {:ok, args ++ [argument]}}
          end
      end
    end)
  end

  defp peel_pi({:pi, grade, domain, body}, acc), do: peel_pi(body, acc ++ [{grade, domain}])
  defp peel_pi(body, acc), do: {acc, body}

  defp match_rule({:var, index}, candidate, count, bindings) when index < count do
    case Map.fetch(bindings, index) do
      {:ok, ^candidate} -> {:ok, bindings}
      {:ok, _other} -> :no_match
      :error -> {:ok, Map.put(bindings, index, candidate)}
    end
  end

  defp match_rule(pattern, candidate, count, bindings)
       when is_tuple(pattern) and is_tuple(candidate) and tuple_size(pattern) == tuple_size(candidate) do
    pattern
    |> Tuple.to_list()
    |> Enum.zip(Tuple.to_list(candidate))
    |> Enum.reduce_while({:ok, bindings}, fn {left, right}, {:ok, current} ->
      case match_rule(left, right, count, current) do
        {:ok, next} -> {:cont, {:ok, next}}
        _ -> {:halt, :no_match}
      end
    end)
  end

  defp match_rule(pattern, candidate, count, bindings) when is_list(pattern) and is_list(candidate) do
    if length(pattern) == length(candidate) do
      Enum.zip(pattern, candidate)
      |> Enum.reduce_while({:ok, bindings}, fn {left, right}, {:ok, current} ->
        case match_rule(left, right, count, current) do
          {:ok, next} -> {:cont, {:ok, next}}
          _ -> {:halt, :no_match}
        end
      end)
    else
      :no_match
    end
  end

  defp match_rule(same, same, _count, bindings), do: {:ok, bindings}
  defp match_rule(_pattern, _candidate, _count, _bindings), do: :no_match

  defp core_subterms(term) when is_tuple(term),
    do: [term | term |> Tuple.to_list() |> Enum.flat_map(&core_subterms/1)]

  defp core_subterms(term) when is_list(term), do: Enum.flat_map(term, &core_subterms/1)
  defp core_subterms(_leaf), do: []

  defp simplify_rule_fixed_point(_proof, _ty, _a, _b, _rule, goal, meta, _visited, 256),
    do: simplification_error(:resource_guard, meta, goal, {:step_ceiling, 256})

  defp simplify_rule_fixed_point(proof, ty, a, b, rule, goal, meta, visited, steps) do
    fingerprint = :erlang.term_to_binary(goal.expected)

    if MapSet.member?(visited, fingerprint) do
      simplification_error(:resource_guard, meta, goal, :visited_state_cycle)
    else
      case Rewrite.directed_plan(proof, ty, a, b, Kernel.normalize(goal.context, goal.expected), :forward, 1) do
        {:ok, build, rewritten, _occurrences} ->
          next = %{
            goal
            | expected: rewritten,
              builders: goal.builders ++ [{:transport, build}],
              trace: goal.trace ++ [%{id: "explicit-#{steps + 1}", kind: :explicit_rule, rule: surface_span(rule)}]
          }

          simplify_rule_fixed_point(proof, ty, a, b, rule, next, meta, MapSet.put(visited, fingerprint), steps + 1)

        {:error, {:no_occurrence, _}} ->
          {:ok, goal}

        {:error, {:reverse_only, _}} ->
          {:ok, goal}

        {:error, cause} ->
          simplification_error(:inadmissible_rule, meta, goal, cause, rule)
      end
    end
  end

  defp simplification_measure(term), do: core_size(term)
  defp core_size(term) when is_tuple(term), do: 1 + (term |> Tuple.to_list() |> Enum.map(&core_size/1) |> Enum.sum())
  defp core_size(term) when is_list(term), do: Enum.map(term, &core_size/1) |> Enum.sum()
  defp core_size(_leaf), do: 0

  defp simplification_error(kind, meta, goal, cause, rule_ast \\ nil) do
    {:error,
     {:simplification_failed,
      %Cure.Diagnostic.SimplificationProblem{
        kind: kind,
        command: surface_span(meta),
        rule: surface_span(rule_ast),
        before_goal: goal.expected,
        after_goal: goal.expected,
        before_surface: Cure.Elab.ProofDisplay.format(goal.expected, goal.names),
        after_surface: Cure.Elab.ProofDisplay.format(goal.expected, goal.names),
        progressed_rules: [],
        trace_ids: Enum.map(goal.trace, &simplification_trace_id/1),
        cause: cause
      }}}
  end

  defp simplification_trace_id(%{id: id}), do: id
  defp simplification_trace_id(other), do: other

  defp close_with_expression(statement, goal) do
    {surface_builders, transports} = Enum.split_with(goal.builders, &match?({:assignment, _, _}, &1))
    block = {:block, [], surface_builders ++ [statement]}
    original_names = Enum.drop(goal.names, length(surface_builders))

    case Elaborator.elaborate_expr_checked(block, goal.expected, original_names, goal.context, goal.env) do
      {:ok, evidence} ->
        evidence = Enum.reduce(Enum.reverse(transports), evidence, &apply_builder/2)

        {:closed, evidence, goal.trace ++ [{:exact, surface_span(statement)}]}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp rewrite_hypothesis(proof_ast, meta, goal, name) do
    with index when is_integer(index) <- Enum.find_index(goal.names, &(&1 == name)),
         hypothesis_value when not is_nil(hypothesis_value) <- Context.lookup(goal.context, index),
         hypothesis = Kernel.normalize(goal.context, Quote.reify(hypothesis_value, Context.length(goal.context))),
         {:ok, proof, proof_type} <- Elaborator.elaborate_expr_typed(proof_ast, goal.names, goal.context, goal.env),
         {:ok, ty_value, a_value, b_value} <- Rewrite.eq_parts(proof_type, Context.signature(goal.context)),
         depth = Context.length(goal.context),
         ty = Kernel.normalize(goal.context, Quote.reify(ty_value, depth)),
         a = Kernel.normalize(goal.context, Quote.reify(a_value, depth)),
         b = Kernel.normalize(goal.context, Quote.reify(b_value, depth)),
         {:ok, transform, rewritten, occurrences} <-
           Rewrite.directed_transform(proof, ty, a, b, hypothesis, Keyword.fetch!(meta, :direction)),
         evidence = transform.({:var, index}),
         rewritten_value = Eval.eval(rewritten, Context.env(goal.context)),
         :ok <- Kernel.check(goal.context, evidence, rewritten_value) do
      {:open,
       %{
         goal
         | names: [name | goal.names],
           expected: Subst.shift(goal.expected, 1, 0),
           context: Context.extend_def(goal.context, rewritten_value, Eval.eval(evidence, Context.env(goal.context))),
           builders: goal.builders ++ [{:core_fact, rewritten, evidence}],
           trace: goal.trace ++ [{:rewrite_hypothesis, name, occurrences, surface_span(meta)}]
       }}
    else
      nil ->
        rewrite_error(:bad_target, meta, proof_ast, goal, target: name)

      {:error, {:no_occurrence, occurrences}} ->
        rewrite_error(:no_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:ambiguous_occurrence, occurrences}} ->
        rewrite_error(:ambiguous_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:reverse_only, direction}} ->
        rewrite_error(:reverse_only, meta, proof_ast, goal, direction: direction)

      {:error, cause} ->
        rewrite_error(:theorem_not_equality, meta, proof_ast, goal, cause: cause)
    end
  end

  defp apply_builder({:transport, build}, evidence), do: build.(evidence)
  defp apply_builder({:core_fact, type, value}, body), do: {:let, Grade.unrestricted(), type, value, body}

  defp rewrite_goal(proof_ast, meta, goal, occurrence) do
    surface_builders = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))
    proof_block = {:block, [], surface_builders ++ [proof_ast]}
    original_names = Enum.drop(goal.names, length(surface_builders))
    depth = Context.length(goal.context)

    with {:ok, proof, proof_type} <-
           Elaborator.elaborate_expr_typed(proof_block, original_names, goal.context, goal.env),
         {:ok, ty_value, a_value, b_value} <- Rewrite.eq_parts(proof_type, Context.signature(goal.context)),
         ty = Kernel.normalize(goal.context, Quote.reify(ty_value, depth)),
         a = Kernel.normalize(goal.context, Quote.reify(a_value, depth)),
         b = Kernel.normalize(goal.context, Quote.reify(b_value, depth)),
         expected = Kernel.normalize(goal.context, goal.expected),
         {:ok, build, rewritten, occurrences} <-
           Rewrite.directed_plan(proof, ty, a, b, expected, Keyword.fetch!(meta, :direction), occurrence) do
      {:open,
       %{
         goal
         | expected: rewritten,
           builders: goal.builders ++ [{:transport, build}],
           trace: goal.trace ++ [{:rewrite, Keyword.fetch!(meta, :direction), occurrences, surface_span(meta)}]
       }}
    else
      {:error, {:no_occurrence, occurrences}} ->
        rewrite_error(:no_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:ambiguous_occurrence, occurrences}} ->
        rewrite_error(:ambiguous_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:invalid_occurrence, selected, occurrences}} ->
        rewrite_error(:invalid_occurrence, meta, proof_ast, goal, target: selected, occurrences: occurrences)

      {:error, {:reverse_only, direction}} ->
        rewrite_error(:reverse_only, meta, proof_ast, goal, direction: direction)

      {:error, cause} ->
        rewrite_error(:theorem_not_equality, meta, proof_ast, goal, cause: cause)
    end
  end

  defp rewrite_error(kind, meta, proof_ast, goal, fields) do
    problem =
      struct!(
        RewriteProblem,
        Keyword.merge(
          [
            kind: kind,
            command: surface_span(meta),
            theorem: surface_span(proof_ast),
            goal: surface_span(goal.source),
            occurrences: [],
            target: Keyword.get(meta, :target, :goal),
            direction: Keyword.get(meta, :direction, :forward),
            direction_range: source_field_span(meta, :direction)
          ],
          fields
        )
      )

    {:error, {:rewrite_failed, problem}}
  end

  defp fact_names(builders) do
    Enum.flat_map(builders, fn
      {:assignment, _meta, [{:variable, _, name}, _rhs]} -> [name]
      _ -> []
    end)
  end

  defp surface_span(meta) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_span({_tag, meta, _children}) when is_list(meta), do: surface_span(meta)
  defp surface_span(_other), do: nil

  defp source_field_span(meta, field) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{fields: fields} when is_map(fields) -> Map.get(fields, field)
      _ -> nil
    end
  end

  defp expression_kind({kind, _meta, _children}) when is_atom(kind), do: kind
  defp expression_kind(_other), do: :expression

  defp trace_span({_kind, span}), do: span
  defp trace_span({_kind, _name, span}), do: span
  defp trace_span(%{rule: span}), do: span
  defp trace_span(_other), do: nil
end
