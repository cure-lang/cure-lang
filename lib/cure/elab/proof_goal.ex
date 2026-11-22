defmodule Cure.Elab.ProofGoal do
  @moduledoc "Typed, compile-time-only state for compositional proof commands."

  alias Cure.Core.{Context, Env, Eval, Grade, Kernel, Quote}
  alias Cure.Diagnostic.{ProofChainMismatchProblem, ProofChainSyntaxProblem, RewriteProblem}
  alias Cure.Elab.{Elaborator, Rewrite, Subst}
  alias Cure.Elab.Tactic.{Result, Script, Step}
  alias Cure.MetaAST.Metadata

  @enforce_keys [:expected, :names, :context, :env, :source, :status, :builders, :trace]
  defstruct [:expected, :names, :context, :env, :source, :status, :builders, :trace, :id, :root_expected, :root_context]

  @type status :: :open | :closed
  @type t :: %__MODULE__{
          expected: Cure.Core.Term.t(),
          id: reference() | nil,
          root_expected: Cure.Core.Term.t() | nil,
          root_context: Cure.Core.Context.t() | nil,
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
    execute(statements, new(expected, names, context, env, meta), step_index)
  end

  @doc "Construct a goal while preserving its original checking obligation."
  def new(expected, names, context, env, source \\ []) do
    %__MODULE__{
      id: make_ref(),
      root_expected: expected,
      root_context: context,
      expected: expected,
      names: names,
      context: context,
      env: env,
      source: source,
      status: :open,
      builders: [],
      trace: []
    }
  end

  @doc "Inspect the remaining target and local hypotheses without modifying the goal."
  def inspect_goal(goal) do
    depth = Context.length(goal.context)
    signature = Context.signature(goal.context)
    facts = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))
    context_names = Enum.drop(goal.names, length(facts))

    hypotheses =
      context_names
      |> Enum.with_index()
      |> Enum.flat_map(fn {name, index} ->
        case Context.lookup(goal.context, index) do
          nil -> []
          type -> [%{name: name, type: Quote.reify(type, depth, signature)}]
        end
      end)

    local_facts =
      facts
      |> Enum.with_index(1)
      |> Enum.flat_map(fn {{:assignment, _, [{:variable, _, name}, _]}, count} ->
        block = {:block, [], Enum.take(facts, count) ++ [{:variable, [], name}]}

        case Elaborator.elaborate_expr_typed(block, context_names, goal.context, goal.env) do
          {:ok, _term, type} ->
            [%{name: name, type: Quote.reify(type, depth, signature)}]

          {:error, _} ->
            [%{name: name, type: :pending}]
        end
      end)

    %{target: goal.expected, hypotheses: Enum.reverse(local_facts) ++ hypotheses, status: goal.status}
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
    case Cure.Elab.Tactic.command(statement).(goal) do
      {:ok, %Cure.Elab.Tactic.Result{goals: [next_goal]}} ->
        execute(rest, next_goal, step_index)

      {:ok, %Cure.Elab.Tactic.Result{goals: [], solutions: solutions}} when rest == [] ->
        %{evidence: evidence, trace: trace} = Map.fetch!(solutions, goal.id)
        {:ok, evidence, trace}

      {:ok, %Cure.Elab.Tactic.Result{goals: [], solutions: solutions}} ->
        %{trace: trace} = Map.fetch!(solutions, goal.id)
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

  @doc false
  def command({:assignment, meta, [{:variable, _, name}, _rhs]} = statement, goal)
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

  def command({:rewrite_command, meta, [proof_ast]}, goal) do
    case Keyword.get(meta, :target, :goal) do
      :goal -> rewrite_goal(proof_ast, meta, goal, nil)
      {:at, occurrence} -> rewrite_goal(proof_ast, meta, goal, occurrence)
      {:in, name} -> rewrite_hypothesis(proof_ast, meta, goal, name)
      # `rewrite using e all` -- rewrite EVERY occurrence. Opt-in; the default
      # stays single-occurrence (an ambiguous match is E111), which is stricter
      # than Lean's silent rewrite-all. `Rewrite.directed_plan/7` already
      # accepts `:all`, so this only routes the selector through.
      :all -> rewrite_goal(proof_ast, meta, goal, :all)
    end
  end

  def command({:proof_application, meta, [proof_ast]}, goal) do
    case Keyword.get(meta, :kind) do
      :exact -> close_with_expression(proof_ast, goal, :exact, meta)
      :apply -> apply_proof(proof_ast, meta, goal)
    end
  end

  def command({:simplify_command, meta, rules}, goal) do
    if Keyword.get(meta, :using) == :proof do
      adapt_existing_proof(hd(rules), meta, goal)
    else
      simplify_command_rules(meta, rules, goal)
    end
  end

  def command({:solver_command, meta, _arguments} = command, goal),
    do: close_with_expression(command, goal, :solver, meta)

  # A user-defined tactic (Phase 3). The expansion is SURFACE syntax that
  # `Tactic.Step` classified against the closed tactic vocabulary when the rule
  # was validated; here it is interpreted through `Tactic.Script`, which runs
  # each step as an ordinary proof command. Nothing about this path can produce
  # Core terms the kernel has not checked: every step is `Tactic.command/1`,
  # which re-checks its evidence at the ORIGINAL goal.
  #
  # A script that leaves the goal open is reported as an unfinished
  # justification with the residual goal, exactly like a `because` block that
  # ran out of commands — a tactic is a command, not a licence to skip the proof.
  def command({:tactic_script, meta, [expansion]}, goal) do
    with {:ok, step} <- Step.classify(expansion) do
      case Script.run(step, goal) do
        {:ok, %Result{goals: [], solutions: solutions}} ->
          case Map.fetch(solutions, goal.id) do
            {:ok, %{evidence: evidence, trace: trace}} ->
              {:closed, evidence, goal.trace ++ trace}

            # Closed but with no solution recorded for THIS goal. That means a
            # step closed something other than the goal it was handed, which a
            # single-goal command cannot legitimately do. Fail loudly rather
            # than fabricate evidence.
            :error ->
              tactic_not_closed(meta, goal)
          end

        {:ok, %Result{goals: [_ | _]}} ->
          tactic_not_closed(meta, goal)

        {:error, _} = error ->
          error
      end
    else
      {:error, reason} -> {:error, {:invalid_tactic_expansion, Keyword.get(meta, :keyword), reason}}
    end
  end

  def command(statement, goal), do: close_with_expression(statement, goal)

  defp simplify_command_rules(meta, rules, goal) do
    with {:ok, simplified} <- simplify_rules(rules, goal, meta),
         {:ok, simplified} <- simplify_lemma_set(simplified, meta),
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

  # Explicit simp declarations are validated up front. Legacy @lemma entries
  # remain compatible only when the same substitution-stable ordering admits them.
  defp simplify_lemma_set(goal, meta), do: simplify_lemma_set(goal, meta, 0)

  defp simplify_lemma_set(goal, meta, 256),
    do: simplification_error(:resource_guard, meta, goal, {:step_ceiling, 256})

  defp simplify_lemma_set(goal, meta, steps) do
    normalized = Kernel.normalize(goal.context, goal.expected)

    case equality_head(normalized, goal) do
      nil ->
        {:ok, goal}

      head ->
        next =
          goal.env
          |> Cure.Elab.SimpSet.entries(head)
          |> Enum.reduce(goal, fn lemma, current ->
            case apply_lemma_rule(lemma, current, meta) do
              {:ok, next} -> next
              {:error, _} -> current
            end
          end)

        if next.expected == goal.expected,
          do: {:ok, next},
          else: simplify_lemma_set(next, meta, steps + 1)
    end
  end

  defp equality_head({:data, family, [_carrier], [_left, _right]}, goal) do
    if family == Cure.Core.Inductive.builtin(Context.signature(goal.context), :eq), do: family, else: nil
  end

  defp equality_head(_other, _goal), do: nil

  defp apply_lemma_rule(%{name: name, type: type}, goal, meta) do
    with {:ok, proof} <- lemma_proof(name, goal),
         {:ok, specialized, ty, left, right} <-
           instantiate_generated_rule(type, proof, Kernel.normalize(goal.context, goal.expected), goal),
         ty = Kernel.normalize(goal.context, ty),
         left = Kernel.normalize(goal.context, left),
         right = Kernel.normalize(goal.context, right),
         true <- simplification_measure(left) > simplification_measure(right),
         {:ok, build, rewritten, _occurrences} <-
           Rewrite.directed_plan(
             specialized,
             ty,
             left,
             right,
             Kernel.normalize(goal.context, goal.expected),
             :forward,
             1
           ) do
      {:ok,
       %{
         goal
         | expected: rewritten,
           builders: goal.builders ++ [{:transport, build}],
           trace: goal.trace ++ [%{id: "lemma-#{length(goal.trace) + 1}", kind: :lemma, rule: surface_span(meta)}]
       }}
    else
      _ -> {:error, :not_applicable}
    end
  end

  defp lemma_proof(name, goal) do
    if Env.certified?(goal.env, name) and Kernel.check_def(goal.env, name) == :ok,
      do: {:ok, {:global, name}},
      else: {:error, :uncertified_lemma}
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
               simp_equality_parts(proof_type, goal) do
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
          with {:ok, ty_value, a_value, b_value} <- simp_equality_parts(proof_type, goal),
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
                    specialized_type = Rewrite.mk_eq(specialized_carrier, specialized_left, specialized_right)

                    if Kernel.check(goal.context, specialized_proof, simp_type_value(specialized_type, goal)) == :ok do
                      {:ok, specialized_proof, specialized_carrier, specialized_left, specialized_right}
                    else
                      false
                    end

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

  defp simp_type_value(type, goal) do
    type
    |> then(&Kernel.normalize(goal.context, &1))
    |> Eval.eval(Context.env(goal.context))
  end

  defp simp_equality_parts(type, goal),
    do: Rewrite.eq_parts(type, Context.signature(goal.context))

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
          expected = simp_type_value(instantiated_domain, goal)

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

  defp close_with_expression(statement, goal, trace_kind \\ :exact, trace_meta \\ nil) do
    {surface_builders, transports} = Enum.split_with(goal.builders, &match?({:assignment, _, _}, &1))
    block = {:block, [], surface_builders ++ [statement]}
    original_names = Enum.drop(goal.names, length(surface_builders))

    case Elaborator.elaborate_expr_checked(block, goal.expected, original_names, goal.context, goal.env) do
      {:ok, evidence} ->
        evidence = Enum.reduce(Enum.reverse(transports), evidence, &apply_builder/2)
        {:closed, evidence, goal.trace ++ [{trace_kind, surface_span(trace_meta || statement)}]}

      {:error, reason} ->
        {:error, reason}
    end
  end

  # Backward reasoning: close the goal with `proof`, or report why it does not fit.
  #
  # `apply` is the backward-reasoning counterpart of writing the evidence term
  # directly. The proof is elaborated and then checked against the goal's
  # expected type, so a proof whose conclusion unifies with the goal closes it,
  # and one that does not is rejected with the goal and the supplied proposition
  # both surfaced. Nothing is trusted: the kernel re-checks the result.
  defp apply_proof(proof_ast, meta, goal) do
    case close_with_expression(proof_ast, goal, :apply, meta) do
      {:closed, evidence, trace} ->
        {:closed, evidence, trace}

      {:error, _reason} ->
        {:error,
         {:proof_chain_mismatch,
          %ProofChainMismatchProblem{
            kind: :unfinished_justification,
            step_index: 0,
            justification: surface_span(meta),
            residual_goal: goal.expected,
            cause: {:apply_does_not_close, surface_span(proof_ast)}
          }}}
    end
  end

  defp rewrite_hypothesis(proof_ast, meta, goal, name) do
    with {:ok, goal} <- materialize_facts(goal) do
      rewrite_checked_hypothesis(proof_ast, meta, goal, name)
    end
  end

  # A hypothesis rewrite adds a real Core binder. Flush deferred surface facts
  # first so all names below that binder have matching kernel-context entries.
  defp materialize_facts(goal) do
    facts = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))

    case List.last(facts) do
      nil ->
        {:ok, goal}

      {:assignment, _, [{:variable, _, name}, _]} ->
        names = Enum.drop(goal.names, length(facts))
        block = {:block, [], facts ++ [{:variable, [], name}]}

        with {:ok, term, _type} <- Elaborator.elaborate_expr_typed(block, names, goal.context, goal.env) do
          {context, replacements} = materialized_facts(facts, term, goal.context, [])

          builders = Enum.reject(goal.builders, &match?({:assignment, _, _}, &1)) ++ replacements

          {:ok, %{goal | context: context, expected: Subst.shift(goal.expected, length(facts), 0), builders: builders}}
        end
    end
  end

  defp materialized_facts([], _term, context, acc), do: {context, Enum.reverse(acc)}

  defp materialized_facts(
         [{:assignment, _, [{:variable, _, name}, _]} | rest],
         {:let, grade, type, value, body},
         context,
         acc
       ) do
    next = Context.extend_def(context, Eval.eval(type, Context.env(context)), Eval.eval(value, Context.env(context)))
    materialized_facts(rest, body, next, [{:named_fact, name, grade, type, value} | acc])
  end

  defp rewrite_checked_hypothesis(proof_ast, meta, goal, name) do
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
  defp apply_builder({:named_fact, _name, grade, type, value}, body), do: {:let, grade, type, value, body}

  defp rewrite_goal(proof_ast, meta, goal, occurrence) do
    surface_builders = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))
    proof_block = {:block, [], surface_builders ++ [proof_ast]}
    original_names = Enum.drop(goal.names, length(surface_builders))
    depth = Context.length(goal.context)

    with {:ok, proof, proof_type} <-
           Elaborator.elaborate_expr_typed(proof_block, original_names, goal.context, goal.env),
         {:ok, ty_value, a_value, b_value} <-
           Rewrite.eq_parts(proof_type, Context.signature(goal.context)),
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

  # A tactic that ran to completion without closing the goal. Reported as an
  # unfinished justification so the author sees WHICH goal survived, mirroring
  # the diagnostic a `because` block gets when its last statement leaves the
  # goal open (Phase 1's G1 surface).
  defp tactic_not_closed(meta, goal) do
    info = Metadata.source_info(meta)

    {:error,
     {:proof_chain_mismatch,
      %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: 0,
        justification: info && info.whole,
        residual_goal: goal.expected,
        cause: {:tactic_did_not_close, Keyword.get(meta, :keyword)}
      }}}
  end

  defp fact_names(builders) do
    Enum.flat_map(builders, fn
      {:assignment, _meta, [{:variable, _, name}, _rhs]} -> [name]
      {:named_fact, name, _grade, _type, _value} -> [name]
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
