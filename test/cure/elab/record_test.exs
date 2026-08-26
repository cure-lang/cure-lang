defmodule Cure.Elab.RecordTest do
  @moduledoc """
  Records (Idris parity), declaration + construction. A record `rec Point\n  x: T
  \n  y: U` is elaborated as a single-constructor family whose constructor shares
  the family name and whose argument telescope is *named by the fields* — the
  field names live on the constructor telescope, so no separate registry is needed
  and the kernel treats the names as plain labels.

  Because the constructor and the family share a name, `resolve_index_name` (which
  runs only in type positions) resolves the shared name to the *family*, so
  `p: Point` / `-> Point` are types while `Point(..)` / `Point{..}` are values.

  Record construction `Point{x: .., y: ..}` desugars to the positional constructor
  `Point(.., ..)`, ordering the field values by the constructor telescope, so field
  order is free and a missing/extra field is rejected. Fields are read back by
  pattern matching (`match p | Point(a, b) -> a`); the `p.x` projection sugar is a
  separate step. Oracle `record/rc01_construct_match` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @pt "mod M\n  type Nat = Z | S(Nat)\n  rec Point\n    x: Nat\n    y: Nat\n"

  test "a record constructs positionally and is read by pattern matching" do
    src =
      @pt <>
        "  fn getx(p: Point) -> Nat = match p\n    Point(a, b) -> a\n" <>
        "  fn g() -> Nat = getx(Point(S(Z()), Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecPos", functions: [:getx, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a same-named record family wins over its constructor in a Type-valued branch" do
    src = """
    mod RecordTypeBranch
      type Shape = RecordShape | IntShape

      rec Payload
        value: Int

      fn Sem(shape: Shape) -> Type = match shape
        RecordShape -> Payload
        IntShape -> Int

      fn keep(value: Sem(RecordShape)) -> Payload = value
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "brace construction with fields in declaration order" do
    src =
      @pt <>
        "  fn getx(p: Point) -> Nat = match p\n    Point(a, b) -> a\n" <>
        "  fn g() -> Nat = getx(Point{x: S(Z()), y: Z()})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecBrace", functions: [:getx, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "brace construction is order-independent" do
    src =
      @pt <>
        "  fn gety(p: Point) -> Nat = match p\n    Point(a, b) -> b\n" <>
        "  fn g() -> Nat = gety(Point{y: S(Z()), x: Z()})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecReorder", functions: [:gety, :g])

    # y = S(Z) even though it was written first.
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "field projection p.x reads the first field" do
    src =
      @pt <>
        "  fn getx(p: Point) -> Nat = p.x\n  fn g() -> Nat = getx(Point{x: S(Z()), y: Z()})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecProjX", functions: [:getx, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "field projection p.y reads a later field" do
    src =
      @pt <>
        "  fn gety(p: Point) -> Nat = p.y\n  fn g() -> Nat = gety(Point{x: Z(), y: S(S(Z()))})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecProjY", functions: [:gety, :g])

    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "projecting an unknown field is rejected" do
    assert {:error, {:source_context, {:unknown_field, :"M#Point", "z", [:x, :y]}, _}} =
             Program.elaborate(@pt <> "  fn f(p: Point) -> Nat = p.z\nend\n")
  end

  test "a parameterized record constructs, matches, and projects" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n  rec Box(a)\n    val: a\n" <>
        "  fn unbox(b: Box(Nat)) -> Nat = b.val\n  fn g() -> Nat = unbox(Box{val: S(Z())})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecBox", functions: [:unbox, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a two-parameter record projects the correct field by position" do
    # `snd` is field index 1; its type `b` must resolve through the parameter
    # substitution, exercising the de-Bruijn-correct projected type.
    src =
      "mod M\n  type Nat = Z | S(Nat)\n  rec Pair(a, b)\n    fst: a\n    snd: b\n" <>
        "  fn gs(p: Pair(Nat, Nat)) -> Nat = p.snd\n" <>
        "  fn g() -> Nat = gs(Pair{fst: Z(), snd: S(S(Z()))})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecPair", functions: [:gs, :g])

    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "record update overrides one field and preserves the rest" do
    src =
      @pt <>
        "  fn getx(p: Point) -> Nat = p.x\n  fn gety(p: Point) -> Nat = p.y\n" <>
        "  fn bump(p: Point) -> Point = Point{p | x: S(Z())}\n" <>
        "  fn newx() -> Nat = getx(bump(Point{x: Z(), y: S(S(Z()))}))\n" <>
        "  fn kepty() -> Nat = gety(bump(Point{x: Z(), y: S(S(Z()))}))\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.RecUpdate", functions: [:getx, :gety, :bump, :newx, :kepty])

    assert apply(mod, :newx, []) == {:S, :Z}
    assert apply(mod, :kepty, []) == {:S, {:S, :Z}}
  end

  test "multiline record update accepts layout and multiple overrides" do
    src =
      @pt <>
        "  fn bump(p: Point) -> Point = Point{\n" <>
        "    p |\n" <>
        "    x: S(Z()),\n" <>
        "    y: Z()\n" <>
        "  }\n" <>
        "  fn result() -> Point = bump(Point{x: Z(), y: S(Z())})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.MultilineRecUpdate", functions: [:bump, :result])
    assert apply(mod, :result, []) == {:Point, {:S, :Z}, :Z}
  end

  test "updating a non-field is rejected" do
    assert {:error, {:source_context, {:record_field_mismatch, %{record: :Point, unknown: [:z], missing: []}}, _}} =
             Program.elaborate(@pt <> "  fn f(p: Point) -> Point = Point{p | z: Z()}\nend\n")
  end

  test "a missing record field is rejected" do
    assert {:error, {:source_context, {:record_field_mismatch, %{record: :Point, unknown: [], missing: [:y]}}, _}} =
             Program.elaborate(@pt <> "  fn g() -> Point = Point{x: S(Z())}\nend\n")
  end

  test "an unknown record field is rejected" do
    assert {:error, {:source_context, {:record_field_mismatch, %{record: :Point, unknown: [:z], missing: [:y]}}, _}} =
             Program.elaborate(@pt <> "  fn g() -> Point = Point{x: S(Z()), z: Z()}\nend\n")
  end
end
