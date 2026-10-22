defmodule Cure.Core.ProofContext do
  @moduledoc """
  Observe a closure-free semantic context for independent proof comparison.

  Supported values are universe sorts, Atom type/literals and neutral
  variables whose levels are strictly below the context depth. Closures,
  applications, cases, data/constructor/effect values and other primitives
  are explicit exclusions. This is not semantic context validity, native
  typing, arbitrary readback refinement or a release gate.

  The complete parallel field lengths, grades and value shapes are checked
  before calling `Quote.reify`. Out-of-scope levels are rejected rather than
  relying on either negative Elixir indices or saturating natural subtraction.
  The signature is audited by `ProofSnapshot`; observations use actual
  `Context.lookup`, `grade`, `env` and `length` operations. Readback terms are
  encoded with `ProofWire`, not trusted as native proofs.
  """
  alias Cure.Core.{Context, Grade, ProofSnapshot, ProofWire, Quote}

  @spec capture(Context.t(), ProofWire.table()) :: {:ok, map()} | {:error, term()}
  def capture(%Context{} = ctx, table) do
    with :ok <- shape(ctx),
         :ok <- validate_table(table),
         {:ok, signature} <- ProofSnapshot.capture(Context.signature(ctx)),
         {:ok, types} <- values(Enum.map(indices(ctx.length), &Context.lookup(ctx, &1)), ctx.length),
         {:ok, environment} <- values(Context.env(ctx), ctx.length),
         {:ok, type_characters} <- readbacks(ctx.types, ctx, table),
         {:ok, environment_characters} <- readbacks(Context.env(ctx), ctx, table) do
      {:ok,
       %{
         size: Context.length(ctx),
         types: types,
         grades: Enum.map(indices(ctx.length), &Context.grade(ctx, &1)),
         environment: environment,
         type_characters: type_characters,
         environment_characters: environment_characters,
         signature: signature
       }}
    end
  end

  def capture(_ctx, _table), do: {:error, :malformed_context}

  @doc "Reflect one supported semantic value without invoking evaluation."
  @spec value(term(), non_neg_integer()) :: {:ok, term()} | {:error, term()}
  def value({:vtype, level}, depth)
      when is_integer(depth) and depth >= 0 and is_integer(level) and level in 0..2,
      do: {:ok, {:sort, level}}

  def value({:vatom_type}, depth) when is_integer(depth) and depth >= 0, do: {:ok, :atom_type}

  def value({:vatom, name}, depth) when is_integer(depth) and depth >= 0 and is_atom(name),
    do: {:ok, {:atom, Atom.to_string(name)}}

  def value({:vneutral, {:nvar, level}} = value, depth)
      when is_integer(depth) and depth >= 0 and is_integer(level) and level >= 0 do
    if level < depth, do: {:ok, {:neutral, level}}, else: {:error, {:escaped_level, value, depth}}
  end

  def value(value, _depth), do: {:error, {:unsupported_context_value, value}}

  defp shape(ctx) do
    if is_integer(ctx.length) and ctx.length >= 0 and sized?(ctx.types, ctx.length) and
         sized?(ctx.grades, ctx.length) and sized?(ctx.env, ctx.length) and
         Enum.all?(ctx.grades, &valid_grade?/1),
       do: :ok,
       else: {:error, :malformed_context}
  end

  defp sized?([], 0), do: true
  defp sized?([_head | tail], size) when size > 0, do: sized?(tail, size - 1)
  defp sized?(_values, _size), do: false
  defp indices(0), do: []
  defp indices(size), do: Enum.to_list(0..(size - 1))

  defp values([], _depth), do: {:ok, []}

  defp values([head | tail], depth) do
    with {:ok, reflected} <- value(head, depth), {:ok, rest} <- values(tail, depth) do
      {:ok, [reflected | rest]}
    end
  end

  defp readbacks([], _ctx, _table), do: {:ok, []}

  defp readbacks([value | values], ctx, table) do
    with {:ok, characters} <- ProofWire.encode_term(Quote.reify(value, ctx.length, ctx.signature), table),
         {:ok, rest} <- readbacks(values, ctx, table) do
      {:ok, [characters | rest]}
    end
  end

  defp validate_table(table) do
    if valid_table?(table), do: :ok, else: {:error, {:malformed_table, table}}
  end

  defp valid_table?([]), do: true
  defp valid_table?([name | rest]), do: valid_name?(name) and valid_table?(rest)
  defp valid_table?(_table), do: false
  defp valid_name?(name) when is_atom(name), do: true
  defp valid_name?(name) when is_binary(name), do: String.valid?(name)
  defp valid_name?(_name), do: false

  defp valid_grade?(grade),
    do: grade in [Grade.zero(), Grade.one(), Grade.affine(), Grade.unrestricted()]
end
