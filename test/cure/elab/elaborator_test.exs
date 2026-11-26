defmodule Cure.Elab.ElaboratorTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Env, Kernel, Context, Eval}
  alias Cure.Elab.Elaborator

  defp parse_one(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    case ast do
      {:block, _, [item]} -> item
      single -> single
    end
  end

  test "elaborates the identity fn to a Core lambda the kernel accepts" do
    ast = parse_one("fn id(x: Type) -> Type = x\n")
    assert {:ok, core, _type_value} = Elaborator.elaborate(ast, Env.empty())

    assert core ==
             {:lam, Cure.Core.Grade.unrestricted(),
              {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}, {:var, 0}}

    pi =
      Eval.eval(
        {:pi, Cure.Core.Grade.unrestricted(), {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}},
         {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}},
        []
      )

    assert :ok == Kernel.check(Context.empty(Env.empty()), core, pi)
  end

  test "resolves the inferred Pi type of the identity fn" do
    ast = parse_one("fn id(x: Type) -> Type = x\n")

    assert {:ok, _core, {:vpi, _g, {:vtype, {:finite, %Cure.Core.LevelValue{constant: 0, atoms: []}}}, _cod}} =
             Elaborator.elaborate(ast, Env.empty())
  end

  test "elaborates a two-parameter fn, resolving variables to de Bruijn indices" do
    # fn k(x: Type, y: Type) -> Type = x  ⇒  λλ. #1
    ast = parse_one("fn k(x: Type, y: Type) -> Type = x\n")

    assert {:ok,
            {:lam, _g1, {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}},
             {:lam, _g2, {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}, {:var, 1}}}, _} =
             Elaborator.elaborate(ast, Env.empty())
  end
end
