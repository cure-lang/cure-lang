defmodule Cure.Elab.MutualRecursionTest do
  @moduledoc """
  Forward references and mutual recursion (Idris parity). Declarations were
  elaborated in a single source-order pass, so a function calling one defined
  later failed with `:unknown_global`. Elaboration is now two-pass: every function
  *signature* is registered first (`Declarations.register_signature`), then every
  *body* is elaborated against the fully-populated environment
  (`Declarations.elaborate_function_body`) — so a call resolves regardless of
  definition order.

  Cure accepts implicit forward references and mutual recursion (no syntactic
  `mutual` block, unlike Idris); this is a more permissive but sound design choice
  — totality is certified separately and best-effort, so a non-total group merely
  stays uncertified. Oracle `func/fn09_mutual_recursion` + `func/fn10_forward_reference`
  pin accept/accept against `mutual`-wrapped Idris.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a function may call another defined later in the module" do
    src =
      @nat <>
        "  fn a(n: Nat) -> Nat = b(n)\n  fn b(n: Nat) -> Nat = S(n)\n  fn g() -> Nat = a(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.MutFwd", functions: [:a, :b, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "mutually recursive functions elaborate and run" do
    src =
      @nat <>
        "  fn ping(n: Nat) -> Nat = match n\n    Z() -> Z()\n    S(k) -> S(pong(k))\n" <>
        "  fn pong(n: Nat) -> Nat = match n\n    Z() -> Z()\n    S(k) -> S(ping(k))\n" <>
        "  fn g() -> Nat = ping(S(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.MutPing", functions: [:ping, :pong, :g])

    # ping/pong together reconstruct the argument.
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "an actually-unknown global is still rejected" do
    assert {:error, {:source_context, {:unknown_global, :nope, _}, _}} =
             Program.elaborate(@nat <> "  fn f(n: Nat) -> Nat = nope(n)\nend\n")
  end

  test "an unknown global in an inferred body retains authored source context" do
    source = "mod InferredContext\n  fn f() = missing_name\nend\n"

    assert {:error, {:source_context, {:unknown_global, :missing_name, _}, %{line: 2, column: column, span: span}}} =
             Program.elaborate(source, file: "inferred_context.cure")

    assert column > 1
    assert span.path == "inferred_context.cure"
    assert span.start_line == 2
  end
end
