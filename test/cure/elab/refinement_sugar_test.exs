defmodule Cure.Elab.RefinementSugarTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # A native refinement binder `{x: T | φ}` should take the bare boolean condition
  # and reflect it, matching Liquid Haskell / F* / Lean. When the clause is a
  # comparison/boolean-connective expression (type `Bool`), the desugarer wraps it
  # in `IsTrue(φ)`; a `Type`-valued clause (a named predicate / proposition) passes
  # through unchanged. This is level 1 of the §3a sugar.

  # Extract the single-parameter function's domain (the refinement's Core form).
  # Match the qualified key's final segment exactly: `env.defs` also carries the
  # ambient prelude slice, and a substring match on "ident" would just as happily
  # find `Std.Core#identity` (whose domain is a plain type variable, not the
  # Sigma under test) depending on map ordering.
  defp param_type(env, name) do
    key =
      env.defs
      |> Map.keys()
      |> Enum.find(fn k -> k |> to_string() |> String.ends_with?("#" <> name) end)

    {:pi, _grade, domain, _codomain} = Map.get(env.defs, key).type
    domain
  end

  test "a bare comparison clause desugars to the same Sigma as an explicit IsTrue clause" do
    {:ok, bare} =
      Program.elaborate("""
      mod SugarBare
        use Std.Bool
        use Std.Proof.IntMath
        fn ident(x: {n: Int | n > 0}) -> Int = 0
      end
      """)

    {:ok, explicit} =
      Program.elaborate("""
      mod SugarExplicit
        use Std.Bool
        use Std.Proof.IntMath
        fn ident(x: {n: Int | IsTrue(n > 0)}) -> Int = 0
      end
      """)

    assert param_type(bare, "ident") == param_type(explicit, "ident")
  end

  test "a bare boolean-connective clause is wrapped in IsTrue" do
    {:ok, bare} =
      Program.elaborate("""
      mod SugarConj
        use Std.Bool
        use Std.Proof.IntMath
        fn ident(x: {p: Int | 0 <= p and p <= 100}) -> Int = 0
      end
      """)

    domain = param_type(bare, "ident")

    # Sigma(Int, λp. IsTrue(<and ...>)) — the codomain body must be the IsTrue data,
    # not a bare Bool value.
    assert {:data, :"Std.Sigma#Sigma",
            [{:data, :"Std.Int#Int", [], []}, {:lam, _g, {:data, :"Std.Int#Int", [], []}, body}], []} = domain

    assert {:data, :"Std.Proof.IntMath#IsTrue", [], [_claim]} = body
  end

  test "a Type-valued named-predicate clause passes through unwrapped (not double-wrapped)" do
    {:ok, env} =
      Program.elaborate("""
      mod SugarNamed
        use Std.Bool
        use Std.Proof.IntMath
        fn ident(x: {n: Int | is_positive(n)}) -> Int = 0
      end
      """)

    domain = param_type(env, "ident")

    assert {:data, :"Std.Sigma#Sigma",
            [{:data, :"Std.Int#Int", [], []}, {:lam, _g, {:data, :"Std.Int#Int", [], []}, body}], []} = domain

    # The predicate body is the applied global `is_positive`, NOT `IsTrue(is_positive(...))`.
    refute match?({:data, :"Std.Proof.IntMath#IsTrue", [], _}, body)
  end
end
