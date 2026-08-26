defmodule Antigen.Generators.ElabLiteralTyping do
  @moduledoc """
  Elaborator-driven literal-typing catalog (compact-Nat coverage batch, spec
  2026-07-09 TCB change). `Kernel.bool_type_value/1` and `Kernel.nat_type_value/1`
  are the SINGLE closed-form source for the `Bool`/`Nat` type value the
  elaborator's literal lowering and the `{:nat_lit, _}` inference rule both share
  (kernel.ex ~1256-1269) — but neither is reachable from a bare `:typed_term`
  Core-level challenge without the REAL prelude (`Cure.Elab.Program`'s
  `@prelude` providers seed `Std.Bool`/`Std.Nat`, registering the builtins these
  functions read via `Inductive.builtin(sig, :bool | :nat)`). So this vertical
  goes through the full elaborator on tiny self-contained modules — no preamble
  needed, Bool and Nat are auto-imported into every elaborated program.

  Two catalog entries:

    * `fn flag() -> Bool = true` — a boolean literal in INFERENCE position
      (`elaborate_expr_typed`'s `:boolean` clause, elaborator.ex:445-449) calls
      `Kernel.bool_type_value/1` directly during `elab/completeness`.
    * `fn five() -> Nat = 5` — the CHECKED-literal fast path
      (elaborator.ex:1100-1107) lowers straight to `{:nat_lit, 5}` without
      calling `nat_type_value` at elaboration time; `elab/soundness`'s
      `check_one` independently re-infers the emitted body
      (`Kernel.infer(ctx, {:nat_lit,5})`), which resolves the literal's type via
      `nat_type_value/1` — over the REAL prelude env, not the hand-seeded `:v1`
      Antigen signature.

  Both entries are wired to BOTH `elab/completeness` and `elab/soundness`
  (already-registered assays — no runner changes needed), reusing the existing
  `:elab_program` challenge kind (payload is just `%{id, src}`, no atom-
  portability concerns for the corpus).
  """
  alias Antigen.{Challenge, Gen}

  @catalog [
    {"lit_typing/bool_infer", :bool_infer, "boolean literal in inference position — Kernel.bool_type_value/1",
     "mod P\n  fn flag() -> Bool = true\nend\n"},
    {"lit_typing/nat_checked", :nat_checked,
     "Nat-checked integer literal — Kernel.nat_type_value/1 (via elab/soundness re-check)",
     "mod P\n  fn five() -> Nat = 5\nend\n"}
  ]

  @doc "Coverage-manifest cells: each catalog id under both assays."
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for assay <- ["elab/completeness", "elab/soundness"], {_id, cell, _note, _src} <- @catalog, do: {assay, cell}
  end

  @doc "Sampleable generator over every declared challenge (coverage-manifest gate)."
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []), do: Gen.member_of(challenges())

  @doc "All challenges (completeness + soundness) as `%Challenge{}` structs."
  @spec challenges() :: [Challenge.t()]
  def challenges do
    for {id, cell, note, src} <- @catalog,
        assay <- ["elab/completeness", "elab/soundness"] do
      Challenge.new(
        kind: :elab_program,
        assay: assay,
        label: :well_typed,
        payload: %{id: id, src: src},
        note: note,
        cover_tag: cell
      )
    end
  end
end
