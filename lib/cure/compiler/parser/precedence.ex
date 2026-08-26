defmodule Cure.Compiler.Parser.Precedence do
  @moduledoc """
  Operator token-symbol and category mappings for Cure's parser and elaborator.

  This module no longer carries binding powers. Operator precedence and
  associativity are now decided entirely by the declaration-driven
  `Cure.Compiler.Parser.FixityTable` (seeded from `Std.Operators` via
  `Cure.Compiler.Parser.BuiltinFixity`); the former static `infix_bp/1`,
  `prefix_bp/1`, and `non_assoc?/1` tables have been retired.

  What remains are two pure token-to-metadata lookups that are *not* precedence:

  - `operator_symbol/1` — maps an operator token type to its display atom
    (e.g. `:plus` → `:+`), used when building AST nodes and surface messages.
  - `operator_category/1` — maps an operator token type to a semantic category
    (e.g. `:arithmetic`, `:comparison`, `:bitwise`).
  """

  @doc "Returns the operator category for a given token type."
  @spec operator_category(atom()) :: atom()
  def operator_category(type) when type in [:plus, :minus, :star, :slash, :percent], do: :arithmetic

  def operator_category(type)
      when type in [:band_op, :bor_op, :bxor_op, :bsl_op, :bsr_op, :bnot_op],
      do: :bitwise

  def operator_category(type) when type in [:eq, :neq, :lt, :gt, :lte, :gte], do: :comparison
  def operator_category(type) when type in [:and_op, :or_op], do: :boolean
  def operator_category(:string_concat), do: :string
  def operator_category(type) when type in [:range, :range_inclusive], do: :range
  def operator_category(:pipe), do: :pipe
  def operator_category(:dot), do: :access
  def operator_category(:melquiades), do: :send
  def operator_category(_), do: :unknown

  @doc "Returns the operator atom for a given token type."
  @spec operator_symbol(atom()) :: atom()
  def operator_symbol(:plus), do: :+
  def operator_symbol(:minus), do: :-
  def operator_symbol(:star), do: :*
  def operator_symbol(:slash), do: :/
  def operator_symbol(:percent), do: :rem
  def operator_symbol(:eq), do: :==
  def operator_symbol(:neq), do: :!=
  def operator_symbol(:lt), do: :<
  def operator_symbol(:gt), do: :>
  def operator_symbol(:lte), do: :<=
  def operator_symbol(:gte), do: :>=
  def operator_symbol(:and_op), do: :and
  def operator_symbol(:or_op), do: :or
  def operator_symbol(:not_op), do: :not
  def operator_symbol(:band_op), do: :band
  def operator_symbol(:bor_op), do: :bor
  def operator_symbol(:bxor_op), do: :bxor
  def operator_symbol(:bsl_op), do: :bsl
  def operator_symbol(:bsr_op), do: :bsr
  def operator_symbol(:bnot_op), do: :bnot
  def operator_symbol(:string_concat), do: :<>
  def operator_symbol(:range), do: :..
  def operator_symbol(:range_inclusive), do: :"..="
  def operator_symbol(:pipe), do: :|>
  def operator_symbol(:dot), do: :.
  def operator_symbol(:melquiades), do: :"<-|"
  def operator_symbol(:assign), do: :=
  def operator_symbol(other), do: other
end
