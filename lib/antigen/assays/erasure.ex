defmodule Antigen.Assays.Erasure do
  @moduledoc """
  Property tests for the untrusted {0,ω} erasure/relevance machinery
  `Cure.Elab.Erase` / `Cure.Elab.Relevance` (spec: antigen-erasure-relevance).

    * erasure/idempotent — `erase∘erase == erase` + hole preservation (V4a).
    * erasure/selective  — erase keeps exactly the :unrestricted positions (ctor + app-head).
    * erasure/wellformed — `term?(t) ⟹ term?(erase t)`.
    * relevance/soundness — an :erased binder used relevantly must be rejected.

  Machinery ops go through an injectable @real map (run/2); negative controls
  weaken the code-under-test without touching `Cure.Elab`/`Cure.Core` or :meck.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Erase, Relevance}
  alias Cure.Core.{Inductive, Env, Term}

  @real %{
    erase: &Erase.erase/2,
    has_hole?: &Erase.has_hole?/1,
    ctor_quantities: &Inductive.ctor_quantities/2,
    get_def: &Env.get_def/2,
    term?: &Term.term?/1,
    relevance_check: &Relevance.check/4
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :erasure_term} = c), do: run(c, @real)

  def run(%Challenge{kind: :erasure_term, assay: "erasure/idempotent", payload: %{env: env, term: t}}, k) do
    once = k.erase.(env, t)
    twice = k.erase.(env, once)

    cond do
      k.has_hole?.(t) == false and k.has_hole?.(once) == true -> {:violation, {:hole_introduced, t}}
      twice != once -> {:violation, {:erase_not_idempotent, t}}
      true -> :ok
    end
  end

  def run(
        %Challenge{
          kind: :erasure_term,
          assay: "erasure/selective",
          payload: %{env: env, term: {:ctor, c, args} = t, surface: :ctor}
        },
        k
      ) do
    qs = k.ctor_quantities.(env, c) || List.duplicate(:unrestricted, length(args))
    expected = present_args(args, qs)

    case k.erase.(env, t) do
      {:ctor, ^c, kept} when kept == expected -> :ok
      _ -> {:violation, {:wrong_positions_kept, c}}
    end
  end

  def run(%Challenge{kind: :erasure_term, assay: "erasure/selective", payload: %{env: env, term: t, surface: :app}}, k) do
    {head, args} = app_spine(t, [])
    {:global, name} = head

    qs =
      case k.get_def.(env, name) do
        %{quantities: q} when is_list(q) -> q
        _ -> List.duplicate(:unrestricted, length(args))
      end

    padded = qs ++ List.duplicate(:unrestricted, max(0, length(args) - length(qs)))
    expected = present_args(args, padded)
    {_h, kept} = app_spine(k.erase.(env, t), [])
    if kept == expected, do: :ok, else: {:violation, {:wrong_positions_kept, name}}
  end

  def run(%Challenge{kind: :erasure_term, assay: "erasure/wellformed", payload: %{env: env, term: t}}, k) do
    # only meaningful on inputs that are themselves well-formed
    if k.term?.(t) and not k.term?.(k.erase.(env, t)) do
      {:violation, {:erase_ill_formed, t}}
    else
      :ok
    end
  end

  def run(
        %Challenge{
          kind: :erasure_term,
          assay: "relevance/soundness",
          payload: %{env: env, name: n, quantities: qs, body: body, site: nil}
        },
        k
      ) do
    case k.relevance_check.(env, n, qs, body) do
      :ok -> :ok
      {:error, _} -> {:violation, {:clean_body_rejected, n}}
    end
  end

  def run(
        %Challenge{
          kind: :erasure_term,
          assay: "relevance/soundness",
          payload: %{env: env, name: n, quantities: qs, body: body, site: site}
        },
        k
      ) do
    case k.relevance_check.(env, n, qs, body) do
      {:error, {:erased_used_relevantly, %{site: ^site}}} -> :ok
      {:error, {:erased_used_relevantly, %{site: other}}} -> {:violation, {:relevance_wrong_site, site, other}}
      :ok -> {:violation, {:relevance_unsound, site}}
    end
  end

  defp present_args(args, qs) do
    args |> Enum.zip(qs) |> Enum.filter(fn {_a, q} -> q == :unrestricted end) |> Enum.map(fn {a, _q} -> a end)
  end

  # collect an application spine head + args (left-to-right), mirroring Erase.spine/2
  defp app_spine({:app, f, x}, acc), do: app_spine(f, [x | acc])
  defp app_spine(head, acc), do: {head, acc}
end
