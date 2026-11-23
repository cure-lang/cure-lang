defmodule Cure.Elab.Tactic.Apply do
  @moduledoc """
  Untrusted, ephemeral backward-application sessions. Only concrete typed
  premises leave this module; completed applications are checked twice.
  """
  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.{Elaborator, MetaCtx, ProofGoal, Subst, Unify}
  alias Cure.Elab.Tactic.Result

  def start(ast, meta, original) do
    with {:ok, goal} <- ProofGoal.materialize_facts(original),
         {:ok, plan} <- Elaborator.application_head(ast, goal.names, goal.context, goal.env),
         {slots, conclusion, mctx} <- telescope(plan.type, plan.plicities, [], MetaCtx.new()),
         {:ok, mctx} <- unify(conclusion, goal.expected, mctx, goal),
         {:ok, mctx} <- supplied(slots, plan.supplied, mctx, goal) do
      frame = %{goal: goal, plan: plan, slots: slots, mctx: mctx, children: %{}, premise_trace: [], meta: meta}

      with {:ok, frame, goals, solution} <- advance(frame, %{}) do
        if solution do
          {:result, %Result{solutions: %{goal.id => solution}}}
        else
          {:result, %Result{goals: goals, pending: %{goal.id => frame}}}
        end
      end
    end
  end

  defp telescope({:pi, grade, domain, body}, plicities, slots, mctx) do
    prefix = Enum.map(slots, & &1.meta)
    {mctx, id} = MetaCtx.fresh(mctx, Subst.instantiate(domain, prefix))

    slot = %{
      meta: {:meta, id},
      domain: domain,
      prefix: prefix,
      grade: grade,
      plicity: Enum.at(plicities, length(slots), :explicit)
    }

    telescope(body, plicities, slots ++ [slot], mctx)
  end

  defp telescope(conclusion, _plicities, slots, mctx),
    do: {slots, Subst.instantiate(conclusion, Enum.map(slots, & &1.meta)), mctx}

  defp supplied(_slots, [], mctx, _goal), do: {:ok, mctx}
  defp supplied([], _args, _mctx, _goal), do: {:error, :too_many_arguments}

  defp supplied([%{plicity: :implicit} | slots], args, mctx, goal),
    do: supplied(slots, args, mctx, goal)

  defp supplied([slot | slots], [ast | args], mctx, goal) do
    domain = Subst.instantiate(slot.domain, Enum.map(slot.prefix, &Unify.zonk(&1, mctx)))

    inferred =
      if Unify.has_meta?(domain) do
        Elaborator.elaborate_expr_typed(ast, goal.names, goal.context, goal.env)
      else
        case Elaborator.elaborate_expr_checked(ast, domain, goal.names, goal.context, goal.env) do
          {:ok, term} -> {:ok, term, Eval.eval(domain, Context.env(goal.context))}
          error -> error
        end
      end

    case inferred do
      {:ok, term, type} ->
        type = Cure.Core.Quote.reify(type, Context.length(goal.context), Context.signature(goal.context))

        with :ok <- concrete(term),
             {:ok, mctx} <- unify(domain, type, mctx, goal),
             {:ok, mctx} <- unify(slot.meta, term, mctx, goal),
             do: supplied(slots, args, mctx, goal)

      {:error, _} = error ->
        error
    end
  end

  def advance(frame, solutions) do
    with {:ok, frame} <- consume(frame, solutions),
         {:ok, frame, goals} <- stage(frame) do
      if Enum.all?(frame.slots, &(not Unify.has_meta?(Unify.zonk(&1.meta, frame.mctx)))) do
        finish(frame)
      else
        {:ok, frame, goals, nil}
      end
    end
  end

  defp consume(frame, solutions) do
    # Separate source steps append in actual settlement order. A host broadcast
    # can deliver several solutions together; break that tie in telescope order,
    # never by the fresh-reference keys of the children map.
    frame.children
    |> Enum.sort_by(fn {_id, %{slot: slot}} -> elem(slot.meta, 1) end)
    |> Enum.reduce_while({:ok, frame}, fn {id, %{slot: slot, goal: child}}, {:ok, current} ->
      case Map.fetch(solutions, id) do
        :error ->
          {:cont, {:ok, current}}

        {:ok, %{evidence: evidence, trace: trace}} ->
          with :ok <- concrete(evidence),
               :ok <-
                 Kernel.check(
                   child.root_context,
                   evidence,
                   Eval.eval(child.root_expected, Context.env(child.root_context))
                 ),
               {:ok, mctx} <- unify(slot.meta, evidence, current.mctx, current.goal) do
            {:cont,
             {:ok,
              %{
                current
                | mctx: mctx,
                  children: Map.delete(current.children, id),
                  premise_trace: current.premise_trace ++ trace
              }}}
          else
            {:error, _} = error -> {:halt, error}
          end
      end
    end)
  end

  defp stage(frame) do
    frame.slots
    |> Enum.reduce_while({:ok, frame, [], []}, fn slot, {:ok, current, prefix, goals} ->
      argument = Unify.zonk(slot.meta, current.mctx)
      domain = Subst.instantiate(slot.domain, Enum.map(prefix, &Unify.zonk(&1, current.mctx)))

      existing =
        Enum.find_value(current.children, fn {_id, child} ->
          if child.slot.meta == slot.meta, do: child.goal
        end)

      cond do
        existing ->
          {:cont, {:ok, current, prefix ++ [argument], goals ++ [existing]}}

        Unify.has_meta?(domain) ->
          # Do not publish later premises ahead of a blocked dependency.
          {:halt, {:ok, current, prefix, goals}}

        Unify.has_meta?(argument) ->
          case Kernel.infer(current.goal.context, domain) do
            {:ok, {:vtype, _}} ->
              child = %{
                current.goal
                | id: make_ref(),
                  expected: domain,
                  root_expected: domain,
                  root_context: current.goal.context,
                  builders: [],
                  trace: []
              }

              current = %{current | children: Map.put(current.children, child.id, %{slot: slot, goal: child})}
              {:cont, {:ok, current, prefix ++ [argument], goals ++ [child]}}

            {:error, _} = error ->
              {:halt, error}

            {:ok, _} ->
              {:halt, {:error, :application_domain_not_type}}
          end

        true ->
          with :ok <- concrete(argument),
               false <- Unify.has_meta?(domain),
               :ok <- Kernel.check(current.goal.context, argument, Eval.eval(domain, Context.env(current.goal.context))) do
            {:cont, {:ok, current, prefix ++ [argument], goals}}
          else
            true -> {:halt, {:error, :blocked_application_domain}}
            {:error, _} = error -> {:halt, error}
          end
      end
    end)
    |> case do
      {:ok, frame, _prefix, goals} -> {:ok, frame, goals}
      error -> error
    end
  end

  defp finish(frame) do
    args = Enum.map(frame.slots, &Unify.zonk(&1.meta, frame.mctx))

    term =
      case frame.plan.constructor do
        nil -> Enum.reduce(args, frame.plan.head, fn arg, head -> {:app, head, arg} end)
        {name, pc} -> {:ctor, name, Enum.drop(args, pc)}
      end

    with :ok <- concrete(term),
         :ok <- Kernel.check(frame.goal.context, term, Eval.eval(frame.goal.expected, Context.env(frame.goal.context))),
         {:closed, evidence, trace} <- ProofGoal.finish_application(term, frame.meta, frame.goal),
         :ok <- concrete(evidence),
         :ok <-
           Kernel.check(
             frame.goal.root_context,
             evidence,
             Eval.eval(frame.goal.root_expected, Context.env(frame.goal.root_context))
           ) do
      {:ok, frame, [], %{evidence: evidence, trace: trace ++ frame.premise_trace}}
    end
  end

  defp unify(left, right, mctx, goal),
    do: Elaborator.application_unify(left, right, mctx, goal.context, goal.env)

  @doc false
  def concrete(term) do
    if Cure.Core.Term.term?(term) and clean?(term), do: :ok, else: {:error, :internal_application_hole}
  end

  defp clean?({tag, _}) when tag in [:hole, :meta], do: false
  defp clean?(term) when is_tuple(term), do: term |> Tuple.to_list() |> Enum.all?(&clean?/1)
  defp clean?(terms) when is_list(terms), do: Enum.all?(terms, &clean?/1)

  defp clean?(_term), do: true
end
