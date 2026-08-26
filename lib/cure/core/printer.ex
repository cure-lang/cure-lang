defmodule Cure.Core.Printer do
  @moduledoc """
  Render a `Cure.Core.Term` to readable text.

  **Untrusted.** This module is outside the TCB: it reads terms and produces
  strings. It cannot influence checking, and a bug here yields an ugly or wrong
  message, never an unsound program.

  Nothing else in the tree does this — `Quote.reify/2` returns a term and error
  sites hand it to `inspect/1`. Every dependent-pipeline type error that mentions
  a type therefore prints a raw Elixir tuple today.

  Global identities (defs, families, constructors) are stored canonically as
  `Owner#Base` atoms. Display strips the owner and shows the base name — the
  Idris/Agda convention of qualified identity, unqualified rendering. The
  `Owner#Base` spelling is owned by `Cure.Elab.Name`, so base extraction routes
  through it rather than re-parsing the separator here.
  """

  alias Cure.Elab.Name

  @letters ~w(a b c d e f g h i j k l m n o p q r s t u v w x y z)

  @spec print(Cure.Core.Term.t()) :: String.t()
  def print(term), do: print(term, [])

  @spec print(Cure.Core.Term.t(), [String.t()]) :: String.t()
  def print({:type, 0}, _names), do: "Type"
  def print({:type, level}, _names), do: "Type#{level}"
  def print({:var, k}, names), do: Enum.at(names, k) || "?#{k}"
  # NOTE(int-facade): kept so printing stays total on a legacy/deserialized
  # `{:int_type}` node, even though fresh elaboration never produces one
  # (spec 2026-07-18 §3a).
  def print({:int_type}, _names), do: "Int"
  def print({:int_lit, n}, _names), do: Integer.to_string(n)
  def print({:nat_lit, n}, _names), do: Integer.to_string(n)
  def print({:bounded_lit, n}, _names), do: Integer.to_string(n)
  def print({:effect_type, type}, names), do: "Effect(" <> print(type, names) <> ")"
  def print({:float_type}, _names), do: "Float"
  def print({:float_lit, f}, _names), do: Float.to_string(f)
  def print({:binary_type}, _names), do: "Binary"
  def print({:atom_type}, _names), do: "Atom"
  def print({:atom_lit, a}, _names), do: ":" <> Atom.to_string(a)
  def print({:global, name}, _names), do: Name.base(name)
  def print({:hole, name}, _names), do: "?" <> name
  def print({:absurd}, _names), do: "absurd"

  # `:pi`/`:lam`/`:let` carry a QTT grade after the tag; it does not affect the
  # rendered type, so it is ignored here.
  def print({:pi, _g, {:type, _} = dom, cod}, names) do
    if uses_var0?(cod) do
      name = fresh(names)
      "∀ {#{name}}. #{print(cod, [name | names])}"
    else
      non_dependent_arrow(dom, cod, names)
    end
  end

  def print({:pi, _g, dom, cod}, names) do
    if uses_var0?(cod) do
      name = fresh(names)
      "(#{name} : #{print(dom, names)}) -> #{print(cod, [name | names])}"
    else
      non_dependent_arrow(dom, cod, names)
    end
  end

  def print({:lam, _g, _dom, body}, names) do
    name = fresh(names)
    "\\#{name}. #{print(body, [name | names])}"
  end

  def print({:let, _g, ty, val, body}, names) do
    name = fresh(names)
    "let #{name} : #{print(ty, names)} = #{print(val, names)} in #{print(body, [name | names])}"
  end

  def print({:app, _, _} = t, names) do
    {head, args} = unspine(t, [])
    Enum.map_join([head | args], " ", &atomic(&1, names))
  end

  def print({:data, name, params, indices}, names),
    do: applied(Name.base(name), params ++ indices, names)

  def print({:ctor, name, args}, names),
    do: applied(Name.base(name), args, names)

  def print({:case, scrut, _motive, branches}, names) do
    arms =
      Enum.map_join(branches, "; ", fn {ctor, arity, body} ->
        # Fresh names that avoid `names` (and each other), so a case nested in a
        # case does not print the inner branch's binders with the outer's labels.
        binders = fresh_n(names, arity)
        head = Enum.join([Atom.to_string(ctor) | binders], " ")
        "#{head} -> #{print(body, Enum.reverse(binders) ++ names)}"
      end)

    "case #{print(scrut, names)} of #{arms}"
  end

  def print(other, _names) do
    raise ArgumentError, "unknown Core term in printer: #{inspect(other)}"
  end

  # -- helpers ---------------------------------------------------------------

  defp non_dependent_arrow(dom, cod, names) do
    # `cod` was built under a binder that it does not use. No `{:var, 0}` occurs,
    # but indices above 0 are still counted from inside that binder, so push a
    # placeholder to keep `Enum.at/2` aligned for the binders further out.
    "#{atomic(dom, names)} -> #{print(cod, ["_" | names])}"
  end

  defp applied(head, [], _names), do: head
  defp applied(head, args, names), do: "#{head}(#{Enum.map_join(args, ", ", &print(&1, names))})"

  defp unspine({:app, f, a}, acc), do: unspine(f, [a | acc])
  defp unspine(head, acc), do: {head, acc}

  # Parenthesise anything whose rendering could bind looser than application.
  defp atomic({:app, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:pi, _, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:lam, _, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:let, _, _, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic({:case, _, _, _} = t, names), do: "(" <> print(t, names) <> ")"
  defp atomic(t, names), do: print(t, names)

  defp fresh(names) do
    taken = MapSet.new(names)

    Stream.concat([
      @letters,
      Stream.flat_map(1..1000, fn i -> Enum.map(@letters, &"#{&1}#{i}") end)
    ])
    |> Enum.find(fn c -> not MapSet.member?(taken, c) end)
  end

  # `arity` distinct names, each avoiding `names` and the ones already chosen.
  defp fresh_n(names, arity) do
    Enum.reduce(1..arity//1, {[], names}, fn _, {acc, scope} ->
      name = fresh(scope)
      {[name | acc], [name | scope]}
    end)
    |> elem(0)
    |> Enum.reverse()
  end

  # Does the term mention de Bruijn index 0 at its own binding depth?
  defp uses_var0?(term), do: uses_var?(term, 0)

  defp uses_var?({:var, k}, depth), do: k == depth
  defp uses_var?({:pi, _g, d, c}, depth), do: uses_var?(d, depth) or uses_var?(c, depth + 1)
  defp uses_var?({:lam, _g, d, b}, depth), do: uses_var?(d, depth) or uses_var?(b, depth + 1)

  defp uses_var?({:let, _g, t, v, b}, depth),
    do: uses_var?(t, depth) or uses_var?(v, depth) or uses_var?(b, depth + 1)

  defp uses_var?({:app, f, a}, depth), do: uses_var?(f, depth) or uses_var?(a, depth)

  defp uses_var?({:data, _n, ps, is}, depth),
    do: Enum.any?(ps ++ is, &uses_var?(&1, depth))

  defp uses_var?({:ctor, _n, args}, depth), do: Enum.any?(args, &uses_var?(&1, depth))

  defp uses_var?({:case, s, m, brs}, depth) do
    uses_var?(s, depth) or uses_var?(m, depth) or
      Enum.any?(brs, fn {_c, arity, body} -> uses_var?(body, depth + arity) end)
  end

  defp uses_var?(_leaf, _depth), do: false
end
