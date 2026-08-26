defmodule Cure.Elab.ProofChain do
  @moduledoc "Elaborates equational chains into certified `Std.Equivalent.trans` applications."

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Quote}
  alias Cure.Elab.Elaborator
  alias Cure.Diagnostic.ProofChainMismatchProblem
  alias Cure.MetaAST.Metadata

  def elaborate({:proof_chain, _meta, [first | steps]}, names, ctx, env) when steps != [] do
    with {:ok, first_term, carrier_value} <- Elaborator.elaborate_expr_typed(first, names, ctx, env) do
      signature = Context.signature(ctx)
      carrier = Quote.reify(carrier_value, Context.length(ctx), signature)

      state = %{
        carrier: carrier,
        first: first_term,
        left: first_term,
        accumulated: nil,
        index: 0,
        previous_span: surface_span(first)
      }

      with {:ok, finished} <- elaborate_steps(steps, state, names, ctx, env),
           result_type = equivalent_type(signature, carrier, first_term, finished.left),
           :ok <- Kernel.check(ctx, finished.accumulated, Eval.eval(result_type, Context.env(ctx))) do
        {:ok, finished.accumulated, Eval.eval(result_type, Context.env(ctx))}
      end
    end
  end

  def elaborate({:proof_chain, meta, _children}, _names, _ctx, _env),
    do: {:error, {:proof_chain_syntax, :empty_chain, meta}}

  defp elaborate_steps([], state, _names, _ctx, _env), do: {:ok, state}

  defp elaborate_steps(
         [{:proof_step, meta, [_marker, right, justification]} | rest],
         state,
         names,
         ctx,
         env
       ) do
    with {:ok, right_term} <- check_endpoint(right, state, meta, names, ctx, env),
         step_type = equivalent_type(Context.signature(ctx), state.carrier, state.left, right_term),
         {:ok, proof_term} <- check_justification(justification, step_type, state.index, meta, names, ctx, env) do
      accumulated =
        case state.accumulated do
          nil -> proof_term
          prior -> trans_application(env, state.carrier, state.first, state.left, right_term, prior, proof_term)
        end

      elaborate_steps(
        rest,
        %{
          state
          | left: right_term,
            accumulated: accumulated,
            index: state.index + 1,
            previous_span: surface_span(right)
        },
        names,
        ctx,
        env
      )
    end
  end

  defp elaborate_steps([other | _], state, _names, _ctx, _env),
    do: {:error, {:proof_chain_syntax, :malformed_step, state.index, other}}

  defp check_justification(justification, expected, index, meta, names, ctx, env) do
    result =
      case justification do
        {:proof_justification, _just_meta, _statements} ->
          case Cure.Elab.ProofGoal.run(justification, expected, names, ctx, env, index) do
            {:ok, proof, _trace} -> {:ok, proof}
            {:error, _} = error -> error
          end

        {:simplify_command, command_meta, _rules} = command ->
          block = {:proof_justification, command_meta, [command]}

          case Cure.Elab.ProofGoal.run(block, expected, names, ctx, env, index) do
            {:ok, proof, _trace} -> {:ok, proof}
            {:error, _} = error -> error
          end

        _ ->
          Elaborator.elaborate_expr_checked(justification, expected, names, ctx, env)
      end

    case result do
      {:ok, proof} ->
        {:ok, proof}

      {:error, {:proof_chain_mismatch, _} = reason} ->
        {:error, reason}

      {:error, {:proof_chain_syntax, _} = reason} ->
        {:error, reason}

      {:error, {:rewrite_failed, _} = reason} ->
        {:error, reason}

      {:error, {:simplification_failed, _} = reason} ->
        {:error, reason}

      {:error, reason} ->
        info = Metadata.source_info(meta)

        problem = %ProofChainMismatchProblem{
          kind: :wrong_justification,
          step_index: index,
          current_step: info && info.whole,
          justification: info && info.body,
          expected: expected,
          cause: reason
        }

        {:error, {:proof_chain_mismatch, problem}}
    end
  end

  defp check_endpoint(right, state, meta, names, ctx, env) do
    case Elaborator.elaborate_expr_checked(right, state.carrier, names, ctx, env) do
      {:ok, term} ->
        {:ok, term}

      {:error, reason} ->
        info = Metadata.source_info(meta)

        problem = %ProofChainMismatchProblem{
          kind: :adjacent_endpoints,
          step_index: state.index,
          previous_step: state.previous_span,
          current_step: surface_span(right) || (info && info.whole),
          cause: reason
        }

        {:error, {:proof_chain_mismatch, problem}}
    end
  end

  defp surface_span({_tag, meta, _children}) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_span(_node), do: nil

  defp equivalent_type(signature, carrier, left, right) do
    family = Inductive.builtin(signature, :eq) || :"Std.Equivalent#Equivalent"
    {:data, family, [carrier], [left, right]}
  end

  defp trans_application(env, carrier, first, middle, last, prior, proof) do
    trans = Env.resolve_key(env, env.defs, :"Std.Equivalent#trans")

    Enum.reduce([carrier, first, middle, last, prior, proof], {:global, trans}, fn argument, function ->
      {:app, function, argument}
    end)
  end
end
