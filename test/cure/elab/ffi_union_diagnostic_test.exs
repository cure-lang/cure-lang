defmodule Cure.Elab.FFIUnionDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a nested union labels the complete return type and the foreign declaration" do
    source =
      "mod NestedExt\n  @extern(:erlang, :hd, 1)\n  fn head(xs: List(List(Int | Bool))) -> List(Int | Bool)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "nested_extern.cure")

    assert {:extern_returns_union, :head, _codomain} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EXTERN `HEAD` NESTS A UNION IN ITS RETURN TYPE [E093] ---- nested_extern.cure

             The return type contains `Bool | Int` inside another type. Erlang returns one
             raw value, and Cure can only identify and tag a union when that union is the
             outermost return type.

             at nested_extern.cure:3:42
             2 |   @extern(:erlang, :hd, 1)
               |   ------------------------ this declaration crosses an Erlang boundary
             3 |   fn head(xs: List(List(Int | Bool))) -> List(Int | Bool)
               |                                          ^^^^^^^^^^^^^^^^ this return type nests a union across the foreign boundary

             Hint: Return the union directly, or tag the nested value in the foreign function
             """)

    assert_lsp(diagnostic, registry, range(2, 41, 57), range(1, 2, 26), %{
      "conflict" => nil,
      "kind" => "extern_returns_union",
      "name" => "head",
      "union_member_ids" => ["Std.Bool#Bool", "Std.Int#Int"],
      "union_members" => ["Bool", "Int"]
    })

    fixed = String.replace(source, "List(Int | Bool)\nend", "Int | Bool\nend")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "nested_extern_fixed.cure")
  end

  test "members with the same runtime shape name both alternatives" do
    source =
      "mod LX\n  @extern(:erlang, :hd, 1)\n  fn raw(xs: List(Int)) -> Int | Nat\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "indistinct_extern.cure")

    assert {:extern_union_indistinct, :raw, {:same_runtime_shape, [{"Std.Int#Int", "Std.Nat#Nat", :integer}]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EXTERN `RAW` RETURNS AN INDISTINGUISHABLE UNION [E093] -- indistinct_extern.cure

             `Int` and `Nat` both arrive as BEAM integer values. Cure cannot tell which union
             alternative the foreign result belongs to.

             at indistinct_extern.cure:3:28
             2 |   @extern(:erlang, :hd, 1)
               |   ------------------------ this declaration crosses an Erlang boundary
             3 |   fn raw(xs: List(Int)) -> Int | Nat
               |                            ^^^^^^^^^ these union members have indistinguishable BEAM representations

             Hint: Return a tagged record or data type, or choose members with distinct BEAM shapes
             """)

    assert_lsp(diagnostic, registry, range(2, 27, 36), range(1, 2, 26), %{
      "conflict" => %{
        "kind" => "same_runtime_shape",
        "pairs" => [%{"left" => "Int", "right" => "Nat", "runtime_shape" => "integer"}]
      },
      "kind" => "extern_union_indistinct",
      "name" => "raw",
      "union_member_ids" => ["Std.Int#Int", "Std.Nat#Nat"],
      "union_members" => ["Int", "Nat"]
    })

    fixed = String.replace(source, "Int | Nat", "Int | Binary")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "indistinct_extern_fixed.cure")
  end

  test "literals that erase alike retain their authored spellings" do
    source =
      "mod LX\n  @extern(:erlang, :hd, 1)\n  fn raw(xs: List(Int)) -> true | :true\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "literal_extern.cure")

    assert {:extern_union_indistinct, :raw, {:same_erased_literal, [{"Atom#:true", "Bool#true"}]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EXTERN `RAW` RETURNS AN INDISTINGUISHABLE UNION [E093] -- literal_extern.cure

             `:true` and `true` erase to the same BEAM value. Cure cannot tell which union
             alternative the foreign result belongs to.

             at literal_extern.cure:3:28
             2 |   @extern(:erlang, :hd, 1)
               |   ------------------------ this declaration crosses an Erlang boundary
             3 |   fn raw(xs: List(Int)) -> true | :true
               |                            ^^^^^^^^^^^^ these union members have indistinguishable BEAM representations

             Hint: Return a tagged record or data type, or choose members with distinct BEAM shapes
             """)

    assert_lsp(diagnostic, registry, range(2, 27, 39), range(1, 2, 26), %{
      "conflict" => %{
        "kind" => "same_erased_literal",
        "pairs" => [%{"left" => ":true", "right" => "true"}]
      },
      "kind" => "extern_union_indistinct",
      "name" => "raw",
      "union_member_ids" => ["Atom#:true", "Bool#true"],
      "union_members" => [":true", "true"]
    })

    fixed = String.replace(source, ":true", ":other")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "literal_extern_fixed.cure")
  end

  test "an unsupported member points to the union and explains the missing discriminator" do
    source =
      "mod OPQ4\n  opaque type Bare\n\n  @extern(:erlang, :whereis, 1)\n  fn look(name: Atom) -> Bare | :undefined\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "opaque_extern.cure")

    assert {:extern_union_indistinct, :look, {:unsupported_member_shape, ["OPQ4#Bare"]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EXTERN `LOOK` RETURNS AN INDISTINGUISHABLE UNION [E093] -- opaque_extern.cure

             Cure has no single BEAM guard that can recognize `Bare`. The raw foreign result
             therefore cannot be assigned to a union alternative safely.

             at opaque_extern.cure:5:26
             4 |   @extern(:erlang, :whereis, 1)
               |   ----------------------------- this declaration crosses an Erlang boundary
             5 |   fn look(name: Atom) -> Bare | :undefined
               |                          ^^^^^^^^^^^^^^^^^ these union members have indistinguishable BEAM representations

             Hint: Return a tagged record or data type, or choose members with distinct BEAM shapes
             """)

    assert_lsp(diagnostic, registry, range(4, 25, 42), range(3, 2, 31), %{
      "conflict" => %{"kind" => "unsupported_member_shape", "members" => ["Bare"]},
      "kind" => "extern_union_indistinct",
      "name" => "look",
      "union_member_ids" => ["Atom#:undefined", "OPQ4#Bare"],
      "union_members" => [":undefined", "Bare"]
    })

    fixed = String.replace(source, "  opaque type Bare", "  @erases(:pid)\n  opaque type Bare")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "opaque_extern_fixed.cure")
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp assert_lsp(diagnostic, registry, primary_range, related_range, payload) do
    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == primary_range
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == related_range
    assert related["message"] == "this declaration crosses an Erlang boundary"
    assert lsp["data"]["payload"] == payload
    refute inspect(payload) =~ "{:data"
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
