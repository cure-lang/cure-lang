defmodule Cure.Test.ProofCheckingFixture do
  @moduledoc false

  alias Cure.Core.{Grade, ProofRecipe}
  alias Cure.Test.ProofBundleFixture

  def request do
    beta_type = {:app, {:lam, Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:atom_type}}

    {:checking, {:atom_lit, :payload}, :r_leaf, :r_leaf, beta_type, {:r_app, {:r_lam, :r_leaf, :r_leaf}, :r_leaf}}
  end

  def to_agda do
    with {:ok, characters} <- ProofRecipe.encode_checking(request(), ProofBundleFixture.table()) do
      {:ok,
       """
       -- Generated data-only expected-goal checking request, not kernel acceptance.
       module Fixtures.ExecutableChecking where
       open import Data.Char using (Char)
       open import Data.List using (List)
       open import Data.String.Base using (toList)

       characters : List Char
       characters = toList "#{characters}"
       """}
    end
  end
end
