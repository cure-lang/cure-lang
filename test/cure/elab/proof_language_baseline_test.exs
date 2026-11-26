defmodule Cure.Elab.ProofLanguageBaselineTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Core.{Env, Validator}
  alias Cure.Elab.{Erase, Program}

  @source """
  mod ProofLanguageBaseline
    use Std.Equivalent

    type Nat = Z | S(Nat)

    fn plus(left: Nat, right: Nat) -> Nat = match left
      Z() -> right
      S(previous) -> S(plus(previous, right))

    fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = match value
      Z() -> reflexive(Z)
      S(previous) -> rewrite plus_zero_right(previous) in reflexive(S(previous))

    fn nested_transitivity(value: Nat) -> Equivalent(Nat, plus(value, Z), value) =
      trans(plus_zero_right(value), reflexive(value))

    fn double_symmetry(value: Nat) -> Equivalent(Nat, plus(value, Z), value) =
      sym(sym(plus_zero_right(value)))

    fn beneath_function(value: Nat) -> Equivalent(Nat, S(plus(value, Z)), S(value)) =
      cong(fn(item) -> S(item), plus_zero_right(value))

    fn rewritten_goal(value: Nat) -> Equivalent(Nat, plus(value, Z), value) =
      rewrite plus_zero_right(value) in reflexive(value)
  end
  """

  @manifest_path Path.expand("../../fixtures/proof_language/diagnostic_manifest.exs", __DIR__)

  defp parse! do
    assert {:ok, tokens} = Lexer.tokenize(@source, file: "proof_baseline.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "proof_baseline.cure", emit_events: false)
    ast
  end

  defp body(env, name) do
    env |> Env.get_def(name) |> Map.fetch!(:body)
  end

  defp digest(term) do
    term
    |> :erlang.term_to_binary([:deterministic])
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
  end

  test "legacy explicit proof syntax has a stable parse and canonical print baseline" do
    ast = parse!()
    printed = Printer.quoted_to_string(ast)

    assert printed =~ "trans(plus_zero_right(value), reflexive(value))"
    assert printed =~ "sym(sym(plus_zero_right(value)))"
    assert printed =~ "cong(fn(item) -> S(item), plus_zero_right(value))"
    assert printed =~ "rewrite plus_zero_right(value) in reflexive(value)"

    assert {:ok, reparsed_tokens} = Lexer.tokenize(printed, emit_events: false)
    assert {:ok, reparsed} = Parser.parse(reparsed_tokens, emit_events: false)
    assert Printer.quoted_to_string(reparsed) == printed
  end

  test "legacy proofs pin Core and erased-form hashes and contain no primitive rewrite" do
    assert {:ok, first_env} = Program.elaborate(@source)
    assert {:ok, second_env} = Program.elaborate(@source)

    expected = %{
      nested_transitivity:
        {"2c7bafbe81527831abca4d8e8af7116117b17c03372104aa4e7baa1d53b72b2d",
         "986c09099b298f7742f0291e8ea45cc9d6903a5670ebdf3ed0dce2bd7650d4b5"},
      double_symmetry:
        {"ff85a0d7c0a33ce62be822e4804573e2928acdeab29b5801bcba9e7bee02bb94",
         "93397a982577775e378ac52c6d848f168a72ecbcaff41e3e901ca7b5fbddc611"},
      beneath_function:
        {"4986cc48cce93793f7188f9aad74c94a39b1738adb3eb4f4b1ac3d9deb46b608",
         "482e3db58e8eaa6432e149c0bc4f373413b01bd19a03769a57a97c49538d10ff"},
      rewritten_goal:
        {"8c0d429839283b71def251091d5f11f23027bd07de739f36fbdf6798bf5411b4",
         "07cc378e8d9f0fed76c85293b8132c28af14e3c4331db246eed7d703b61fabec"}
    }

    observed =
      Map.new(expected, fn {name, _} ->
        core = body(first_env, name)
        second_core = body(second_env, name)
        erased = Erase.erase(first_env, core)

        assert core == second_core
        assert Enum.all?(Validator.nodes(core), &(not match?({:rewrite, _, _, _}, &1)))

        {name, {digest(core), digest(erased)}}
      end)

    assert observed == expected
  end

  test "future proof diagnostic manifest owns E109 through E115 without gaps" do
    {manifest, _binding} = Code.eval_file(@manifest_path)

    assert Map.keys(manifest) |> Enum.sort() == ~w[E109 E110 E111 E112 E113 E114 E115]a

    assert Enum.all?(manifest, fn {_code, entry} ->
             is_atom(entry.key) and entry.variants != [] and entry.labels != [] and
               Enum.all?(entry.variants, &is_atom/1) and Enum.all?(entry.labels, &is_atom/1)
           end)
  end
end
