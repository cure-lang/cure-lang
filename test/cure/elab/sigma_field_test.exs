defmodule Cure.Elab.SigmaFieldTest do
  @moduledoc """
  Parity row #4 (non-constructor patterns) — Σ/pair-typed constructor fields.
  `type W = MkW(Sigma(a: Nat, Nat))` was rejected at the type-definition level
  (`:unsupported_field_type`) because the field-type mapper `type_to_core` had no
  `{:sigma_type}` clause. Constructor field telescopes are non-dependent here, so
  a Σ field's codomain carries no free binder and maps straight to the inductive
  Core former `{:data, :Sigma, [dom, {:lam, Cure.Core.Grade.unrestricted(), dom, body}], []}` (D2), validated by
  the kernel's `check_family`. This composes
  with pair construction (`%[…]`) and projection (`.2`) for a full
  build-a-record / read-a-field round trip. Oracle `match/mt15_sigma_field` pins
  accept/accept parity.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a constructor may carry a Σ/pair field" do
    src = @nat <> "  type W = MkW(Sigma(a: Nat, Nat)) | NoW\n  fn id(w: W) -> W = w\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "build a Σ-field record and read a projection back end-to-end" do
    src =
      @nat <>
        "  type W = MkW(Sigma(a: Nat, Nat)) | NoW\n" <>
        "  fn second(w: W) -> Nat = match w\n    MkW(p) -> p.2\n    NoW() -> Z()\n" <>
        "  fn g() -> Nat = second(MkW(%[Z(), S(Z())]))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.SigmaFieldE2E", functions: [:second, :g])

    # g builds MkW(%[Z, S(Z)]); second reads the pair's 2nd component.
    assert apply(mod, :g, []) == {:S, :Z}
  end
end
