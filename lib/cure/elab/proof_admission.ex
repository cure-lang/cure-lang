defmodule Cure.Elab.ProofAdmission do
  @moduledoc """
  Frontend admission requirements for explicit and automatically discovered proofs.

  Kernel typing checks an application, not its termination. A completed proof
  script or successful implicit search must therefore use the existing
  required-total mechanism before its enclosing declaration can be admitted.
  Successful search effects are scoped to one declaration; failed overload
  candidates do not commit them. Ordinary partial runtime functions
  remain legal. Development holes remain checkable and are still refused by
  the release hole firewall.

  This module neither manufactures certificates nor extends trusted Core.
  """

  alias Cure.Core.Env
  alias Cure.Elab.{Erase, Name}

  @used_key {__MODULE__, :proof_search_used}

  @proof_forms [
    :proof_chain,
    :proof_justification,
    :proof_application,
    :simplify_command,
    :rewrite_command,
    :rewrite_expr,
    :solver_command,
    :tactic_script,
    :tactic_computed_use,
    :induction,
    :induction_branch
  ]

  @doc false
  def capture(operation) do
    previous = Process.get(@used_key, :inactive)
    Process.put(@used_key, false)

    try do
      result = operation.()
      {result, Process.get(@used_key)}
    after
      if previous == :inactive,
        do: Process.delete(@used_key),
        else: Process.put(@used_key, previous)
    end
  end

  @doc false
  def speculate(operation) do
    if Process.get(@used_key, :inactive) == :inactive,
      do: {operation.(), false},
      else: capture(operation)
  end

  @doc false
  def commit(true) do
    if Process.get(@used_key, :inactive) != :inactive, do: Process.put(@used_key, true)
    :ok
  end

  def commit(false), do: :ok

  @doc false
  def observe_result({:ok, _evidence} = result) do
    commit(true)
    result
  end

  def observe_result(result), do: result

  @spec require_total(Env.t(), atom(), term(), term(), boolean()) :: Env.t()
  def require_total(env, name, surface, body, search_used? \\ false) do
    if (execution?(surface) or search_used?) and not Erase.has_hole?(body),
      do: Env.require_total(env, name),
      else: env
  end

  @doc false
  def execution?({:quoted_syntax, _meta, _children}), do: false
  def execution?({tag, _meta, _children}) when tag in @proof_forms, do: true

  def execution?({_tag, meta, children}) when is_list(meta) do
    Keyword.get(meta, :induction, false) or Keyword.get(meta, :generated_induction_call, false) or
      execution?(children)
  end

  def execution?(terms) when is_list(terms), do: Enum.any?(terms, &execution?/1)
  def execution?(_term), do: false

  @doc false
  def explicit_total?({:quoted_syntax, _meta, _children}, _name), do: false

  def explicit_total?({:function_def, meta, _body}, name) when is_list(meta) do
    same_name? = Name.overload_base(Keyword.get(meta, :name, "")) == Name.overload_base(name)

    case Keyword.get(meta, :decorator) do
      {:decorator, decorator, [{:literal, _, true}]} when is_list(decorator) ->
        same_name? and Keyword.get(decorator, :name) == :total

      _ ->
        false
    end
  end

  def explicit_total?({_tag, _meta, children}, name) when is_list(children),
    do: explicit_total?(children, name)

  def explicit_total?(terms, name) when is_list(terms), do: Enum.any?(terms, &explicit_total?(&1, name))
  def explicit_total?(_term, _name), do: false
end
