defmodule Cure.Test.ProofContextFixture do
  @moduledoc false

  alias Cure.Core.{Context, Grade, ProofContext, ProofSnapshot}
  alias Cure.Test.{ProofBundleFixture, ProofSnapshotFixture}

  def profile do
    signature = ProofSnapshotFixture.environment()
    a = Context.extend(Context.empty(signature), {:vtype, 0}, Grade.unrestricted())
    [a_value] = Context.env(a)
    x = Context.extend(a, a_value, Grade.one())
    [x_value, _a_value] = Context.env(x)
    y = Context.extend_def(x, a_value, x_value)
    z = Context.extend(y, a_value, Grade.affine())
    literal = Context.extend_def(z, {:vatom_type}, {:vatom, :payload})
    last = Context.extend(literal, {:vatom_type}, Grade.zero())

    operations = [
      {:opaque, {:vtype, 0}, Grade.unrestricted()},
      {:opaque, a_value, Grade.one()},
      {:defined, a_value, x_value},
      {:opaque, a_value, Grade.affine()},
      {:defined, {:vatom_type}, {:vatom, :payload}},
      {:opaque, {:vatom_type}, Grade.zero()}
    ]

    {operations, last}
  end

  def to_agda do
    {operations, ctx} = profile()
    table = ProofBundleFixture.table()

    with {:ok, captured} <- ProofContext.capture(ctx, table),
         {:ok, signature} <- ProofSnapshot.capture(ProofSnapshotFixture.environment()) do
      if captured.signature != signature, do: raise("context signature drifted from the audited source")
      6 = captured.size
      ops = vector(operations, &operation/1)
      types = vector(captured.types, &flat/1)
      grades = vector(captured.grades, &Atom.to_string/1)
      env = vector(captured.environment, &flat/1)
      type_chars = vector(captured.type_characters, &~s(toList "#{&1}"))
      env_chars = vector(captured.environment_characters, &~s(toList "#{&1}"))

      {:ok,
       """
       {-# OPTIONS --guardedness #-}
       -- Generated from actual Context/Quote observations; bounded artifact only.
       module Fixtures.ExecutableContext where
       open import Data.Char using (Char)
       open import Data.List using (List; []; _∷_)
       open import Data.Vec using (Vec; []; _∷_)
       open import Data.String.Base using (toList)
       open import Core.Grade using (erased; linear; affine; unrestricted)
       open import Core.Universe using (l0; l1; l2)
       open import Core.FlatContext
       open import Core.FlatContextTyping using (Operation; bind-opaque; bind-defined)
       import Fixtures.ExecutableSnapshot as Source

       operations : List Operation
       operations = #{ops}
       observed : Store Source.source 6
       observed = store #{types} #{grades} #{env}
       type-characters : Vec (List Char) 6
       type-characters = #{type_chars}
       environment-characters : Vec (List Char) 6
       environment-characters = #{env_chars}
       """}
    end
  end

  defp operation({:opaque, type, grade}) do
    {:ok, reflected} = ProofContext.value(type, 6)
    "(bind-opaque #{flat(reflected)} #{grade})"
  end

  defp operation({:defined, type, value}) do
    {:ok, reflected_type} = ProofContext.value(type, 6)
    {:ok, reflected_value} = ProofContext.value(value, 6)
    "(bind-defined #{flat(reflected_type)} #{flat(reflected_value)})"
  end

  defp flat({:sort, level}), do: "(sort l#{level})"
  defp flat(:atom_type), do: "atom-type"
  defp flat({:atom, name}), do: "(atom #{inspect(name)})"
  defp flat({:neutral, level}), do: "(neutral #{level})"
  defp vector([], _render), do: "[]"
  defp vector(values, render), do: "(" <> Enum.map_join(values, " ∷ ", render) <> " ∷ [])"
end
