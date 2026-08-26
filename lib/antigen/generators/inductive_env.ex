defmodule Antigen.Generators.InductiveEnv do
  @moduledoc """
  Drives `Cure.Core.Inductive`'s Env-registration/accessor API directly — the
  seam every other family-shaped generator (`IndexedDecl`, `Universes`) bypasses
  by declaring straight into the kernel and never reading the declaration back
  through `family?/2`, `ctor_result_indices/2`, `arg_telescope/2`,
  `field_count/2`, `ctor_quantities/2`, `index_telescope/2`,
  `param_telescope/2`, `ctor_result_params/2`. Those accessors are the ONLY
  route production code (the elaborator, erasure, relevance, `Conv`) uses to
  read a declared family's metadata back out of the `Env` — but none of the
  modules Antigen's coverage tracks exercise most of them on the shapes the
  existing generators produce, so a whole bucket of Env-accessor lines sits
  cold (`docs` coverage-plateau bucket, `lib/cure/core/inductive.ex`).

  Emits `:family` challenges (assay `"inductive/env_roundtrip"`) — reusing the
  EXISTING `:family` challenge kind and its `to_pieces`/`from_pieces`
  (`Antigen.Challenge`) rather than adding a new challenge kind, per the
  "prefer extending" guidance: a new kind would need its own serialization
  clauses and widen the corpus merge surface for no real gain, since `:family`
  already carries exactly `%{family:, ctors:}`.

  Shape: a parameterized, Int-indexed family
  `AntigenEnv : (a:Type0) -> (n:Int) -> Type0` with a single two-field,
  MIXED-quantity ctor `antigenA : (x:a) -> (y:a) -> AntigenEnv a <lit>`
  (`quantities = [:erased, :unrestricted]`, uniform `result_params = [a]`) — the
  same proven-working "parameterized uniform" shape `IndexedDecl.param/2`
  uses, extended to two fields so every accessor's "found" branch reads back
  non-trivial, multi-element data (a length-2 arg telescope, a length-2
  quantities list, a non-empty result-param list). Always `:well_typed` (the
  shape is well-typed by construction — the ONLY thing the literal index `n`
  varies is the result-index value, never the typing outcome); the interesting
  content here is the accessor-roundtrip and registration-invariant properties
  the assay (`Antigen.Assays.InductiveEnv`) checks, not typing-decision
  diversity (that is `Universes`/`IndexedDecl`'s job).
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Inductive

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.int(-9, 9), fn n ->
      fam = Inductive.family(:AntigenEnv, [{:a, {:type, 0}}], [{:n, {:data, :Int, [], []}}], 0)

      ctor =
        Inductive.ctor(
          :antigenA,
          [{:x, {:var, 0}}, {:y, {:var, 1}}],
          [{:int_lit, n}],
          [:erased, :unrestricted],
          [{:var, 2}]
        )

      Gen.return(
        Challenge.new(
          kind: :family,
          assay: "inductive/env_roundtrip",
          label: :well_typed,
          payload: %{family: fam, ctors: [ctor]},
          note: "Env-accessor roundtrip probe (AntigenEnv/antigenA, n=#{n})"
        )
      )
    end)
  end
end
