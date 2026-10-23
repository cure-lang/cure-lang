defmodule Cure.Core.ProofRecipe do
  @moduledoc """
  Produce the character format of `Core.WireConversion`, `Core.WireRecipe`
  and `Core.WireCertificate` from explicitly supplied, untrusted recipes.

  This module does NOT search for recipes, run kernel admission, certify an
  environment or construct native proofs. Only independent semantic replay
  can establish typing. Concrete generated artifacts are not a universal
  theorem about this Elixir implementation.

  ## Data grammar

  Leaves are atoms (`:r_leaf`, `:c_refl`, `:c_beta`, `:c_zeta`,
  `:c_nat_zero`, `:c_bounded_zero`, `:c_nat_suc`, `:c_bounded_suc`).
  Other constructors are exact tuples mirroring the Agda constructor:
  `{:r_pi, domain, codomain}`, `{:c_trans, term, left, right}`, etc.
  Hyphens in Agda names become underscores; arguments retain their order.
  Levels are integers 0, 1 or 2. Terms use `Cure.Core.ProofWire`'s grammar.

  A case is `{:r_case, scrutinee, parameters, indices, level, kind, motive,
  branches}`, with each branch exactly `{field_kind_recipes, body_recipe}`.
  All vectors are proper lists; constructor parameter witnesses are TERMS.

  Containers are `{:packet, kind_recipe, body_recipe_or_nil}`,
  `{:constructor_recipe, parameters, fields, result_parameters, result_indices}`,
  `{:family_recipe, parameters, indices, constructors}` and
  `{:certificate, families, packets}`. `nil` means an absent raw body, not an
  omitted hidden body. A present body is an ordinary recipe, not a list.

  Every entry point validates the complete supplied UTF-8 atom/string name
  table. Names are interned by the existing term producer; no atoms are minted.
  Unknown names, malformed tuples/lists/levels and unsupported term payloads
  return structured errors. Name tables are inputs, not authenticated sources.
  """

  alias Cure.Core.ProofWire

  @type result :: {:ok, String.t()} | {:error, ProofWire.error() | {:malformed_recipe, term(), term()}}

  @doc "Encode a conversion recipe as characters; this does not establish conversion."
  @spec encode_conversion(term(), ProofWire.table()) :: result()
  def encode_conversion(value, table), do: encode(:conversion, value, table)

  @doc "Encode an ordinary recipe as characters; this does not establish typing."
  @spec encode_recipe(term(), ProofWire.table()) :: result()
  def encode_recipe(value, table), do: encode(:recipe, value, table)

  @doc "Encode a kind/optional-raw-body packet."
  @spec encode_packet(term(), ProofWire.table()) :: result()
  def encode_packet(value, table), do: encode(:packet, value, table)

  @doc "Encode all four constructor declaration recipe vectors."
  @spec encode_constructor(term(), ProofWire.table()) :: result()
  def encode_constructor(value, table), do: encode(:constructor, value, table)

  @doc "Encode parameter/index recipes and the ordered constructor recipes."
  @spec encode_family(term(), ProofWire.table()) :: result()
  def encode_family(value, table), do: encode(:family, value, table)

  @doc "Encode a complete data-only certificate envelope, not native evidence."
  @spec encode_certificate(term(), ProofWire.table()) :: result()
  def encode_certificate(value, table), do: encode(:certificate, value, table)

  @doc """
  Encode a dependent caller request for `Core.WireCaller`.

  The tuple is `{:caller, telescope, kind_recipes, closed_arguments,
  argument_recipes, subject, goal, subject_recipe, goal_recipe}`. Telescope
  entries are `{name, type_term}` in declaration order. This renders data;
  context well-formedness, dependent argument typing and closure are checked
  independently. It does not capture semantic `Context.env` values.
  """
  @spec encode_caller(term(), ProofWire.table()) :: result()
  def encode_caller(value, table), do: encode(:caller, value, table)

  @doc """
  Encode `{:checking, subject, subject_recipe, inferred_kind_recipe, goal,
  goal_kind_recipe}` for `Core.WireChecking`. No conversion recipe is a
  field: independent replay checks inference/kinds and derives conversion
  from exact syntax or bounded normalized equality. This only renders data.
  """
  @spec encode_checking(term(), ProofWire.table()) :: result()
  def encode_checking(value, table), do: encode(:checking, value, table)

  defp encode(kind, value, table) do
    if valid_table?(table) do
      with {:ok, node} <- node(kind, value, table), do: {:ok, IO.iodata_to_binary(render(node))}
    else
      {:error, {:malformed_table, table}}
    end
  end

  defp node(:checking, {:checking, subject, recipe, kind, goal, goal_kind}, table) do
    with {:ok, nodes} <- children([term: subject, recipe: recipe, recipe: kind, term: goal, recipe: goal_kind], table),
         do: {:ok, [20, nested(nodes)]}
  end

  defp node(:conversion, :c_refl, _table), do: {:ok, [0]}
  defp node(:conversion, {:c_sym, child}, table), do: build(1, [conversion: child], table)

  defp node(:conversion, {:c_trans, middle, left, right}, table),
    do: build(2, [term: middle, conversion: left, conversion: right], table)

  defp node(:conversion, {:c_pi, left, right}, table),
    do: build(3, [conversion: left, conversion: right], table)

  defp node(:conversion, {:c_app, left, right}, table),
    do: build(4, [conversion: left, conversion: right], table)

  defp node(:conversion, {:c_data, ps, is}, table),
    do: build(5, [{{:vector, :conversion}, ps}, {{:vector, :conversion}, is}], table)

  defp node(:conversion, {:c_ctor, children}, table),
    do: build(6, [{{:vector, :conversion}, children}], table)

  defp node(:conversion, {:c_effect_type, child}, table), do: build(7, [conversion: child], table)
  defp node(:conversion, {:c_effect_pure, child}, table), do: build(8, [conversion: child], table)

  defp node(:conversion, {:c_effect_bind, left, right}, table),
    do: build(9, [conversion: left, conversion: right], table)

  defp node(:conversion, :c_beta, _table), do: {:ok, [10]}
  defp node(:conversion, :c_zeta, _table), do: {:ok, [11]}

  defp node(:conversion, {:c_delta, name} = value, table) do
    if valid_name?(name) do
      case ProofWire.index_of(name, table) do
        {:ok, index} -> {:ok, [12, index]}
        :error -> {:error, {:unknown_name, name}}
      end
    else
      malformed(:conversion, value)
    end
  end

  defp node(:conversion, :c_nat_zero, _table), do: {:ok, [13]}
  defp node(:conversion, :c_bounded_zero, _table), do: {:ok, [14]}
  defp node(:conversion, :c_nat_suc, _table), do: {:ok, [15]}
  defp node(:conversion, :c_bounded_suc, _table), do: {:ok, [16]}
  defp node(:recipe, :r_leaf, _table), do: {:ok, [0]}
  defp node(:recipe, {:r_pi, a, b}, table), do: build(1, [recipe: a, recipe: b], table)
  defp node(:recipe, {:r_lam, a, b}, table), do: build(2, [recipe: a, recipe: b], table)
  defp node(:recipe, {:r_app, a, b}, table), do: build(3, [recipe: a, recipe: b], table)
  defp node(:recipe, {:r_let, a, b, c}, table), do: build(4, [recipe: a, recipe: b, recipe: c], table)

  defp node(:recipe, {:r_data, ps, is}, table),
    do: build(5, [{{:vector, :recipe}, ps}, {{:vector, :recipe}, is}], table)

  defp node(:recipe, {:r_ctor, ps, prs, ars}, table),
    do: build(6, [{{:vector, :term}, ps}, {{:vector, :recipe}, prs}, {{:vector, :recipe}, ars}], table)

  defp node(:recipe, {:r_claim, term, child}, table), do: build(7, [term: term, recipe: child], table)
  defp node(:recipe, {:r_cumul, level, child}, table), do: build(8, [level: level, recipe: child], table)

  defp node(:recipe, {:r_convert, term, conversion, child}, table),
    do: build(9, [term: term, conversion: conversion, recipe: child], table)

  defp node(:recipe, {:r_case, scrutinee, ps, is, level, kind, motive, branches}, table) do
    build(
      10,
      [
        {:recipe, scrutinee},
        {{:vector, :recipe}, ps},
        {{:vector, :recipe}, is},
        {:level, level},
        {:recipe, kind},
        {:recipe, motive},
        {{:vector, :branch}, branches}
      ],
      table
    )
  end

  defp node(:packet, {:packet, kind, body}, table), do: build(11, [recipe: kind, body: body], table)

  defp node(:constructor, {:constructor_recipe, ps, fs, rps, ris}, table),
    do:
      build(
        12,
        [
          {{:vector, :recipe}, ps},
          {{:vector, :recipe}, fs},
          {{:vector, :recipe}, rps},
          {{:vector, :recipe}, ris}
        ],
        table
      )

  defp node(:family, {:family_recipe, ps, is, cs}, table),
    do: build(13, [{{:vector, :recipe}, ps}, {{:vector, :recipe}, is}, {{:vector, :constructor}, cs}], table)

  defp node(:certificate, {:certificate, fs, ps}, table),
    do: build(14, [{{:vector, :family}, fs}, {{:vector, :packet}, ps}], table)

  defp node(:caller, {:caller, tele, kinds, args, arg_recipes, subject, goal, body, kind}, table) do
    fields = [
      {{:vector, :binder}, tele},
      {{:vector, :recipe}, kinds},
      {{:vector, :term}, args},
      {{:vector, :recipe}, arg_recipes},
      {:term, subject},
      {:term, goal},
      {:recipe, body},
      {:recipe, kind}
    ]

    with {:ok, nodes} <- children(fields, table), do: {:ok, [19, nested(nodes)]}
  end

  defp node(:binder, {name, type}, table) do
    with {:ok, index} <- node(:name, name, table), {:ok, term} <- node(:term, type, table) do
      {:ok, [index, term]}
    end
  end

  defp node(:name, name, table) do
    if valid_name?(name) do
      case ProofWire.index_of(name, table) do
        {:ok, index} -> {:ok, index}
        :error -> {:error, {:unknown_name, name}}
      end
    else
      malformed(:name, name)
    end
  end

  defp node(:level, level, _table) when is_integer(level) and level in 0..2, do: {:ok, level}
  defp node(:body, nil, _table), do: {:ok, []}

  defp node(:body, recipe, table) do
    with {:ok, body} <- node(:recipe, recipe, table), do: {:ok, [body]}
  end

  defp node(:branch, {kinds, body}, table) do
    with {:ok, ks} <- node({:vector, :recipe}, kinds, table),
         {:ok, b} <- node(:recipe, body, table) do
      {:ok, [ks, b]}
    end
  end

  defp node({:vector, _kind}, [], _table), do: {:ok, []}

  defp node({:vector, kind}, [value | rest], table) do
    with {:ok, head} <- node(kind, value, table),
         {:ok, tail} <- node({:vector, kind}, rest, table) do
      {:ok, [head | tail]}
    end
  end

  defp node(:term, term, table) do
    with {:ok, code} <- ProofWire.code(term), {:ok, interned} <- ProofWire.intern(code, table) do
      {:ok, reflected_node(interned)}
    end
  end

  defp node(kind, other, _table), do: malformed(kind, other)

  defp build(tag, arguments, table) do
    with {:ok, children} <- children(arguments, table), do: {:ok, [tag | children]}
  end

  defp children([], _table), do: {:ok, []}

  defp children([{kind, value} | rest], table) do
    with {:ok, child} <- node(kind, value, table), {:ok, tail} <- children(rest, table) do
      {:ok, [child | tail]}
    end
  end

  # Only checked ProofWire.code/intern results reach this conversion.
  defp reflected_node({:node, tag, index, number, children}),
    do: [tag, index, number | Enum.map(children, &reflected_node/1)]

  defp render(number) when is_integer(number), do: [String.duplicate("1", number), ";"]
  defp render(children) when is_list(children), do: ["(", Enum.map(children, &render/1), ")"]
  defp malformed(kind, value), do: {:error, {:malformed_recipe, kind, value}}
  defp nested([last]), do: last
  defp nested([first | rest]), do: [first, nested(rest)]

  defp valid_table?([]), do: true
  defp valid_table?([name | rest]), do: valid_name?(name) and valid_table?(rest)
  defp valid_table?(_table), do: false
  defp valid_name?(name) when is_atom(name), do: true
  defp valid_name?(name) when is_binary(name), do: String.valid?(name)
  defp valid_name?(_name), do: false
end
