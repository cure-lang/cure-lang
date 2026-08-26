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
        {"d28d0a97b5b8aab88fe1f312cd12e5199b6c70b3a71549cc99e15e565dd8ada3",
         "986c09099b298f7742f0291e8ea45cc9d6903a5670ebdf3ed0dce2bd7650d4b5"},
      double_symmetry:
        {"412d0690ee1c630541f768ad718ae942792d5165de270fd404e5b11956a5de5b",
         "93397a982577775e378ac52c6d848f168a72ecbcaff41e3e901ca7b5fbddc611"},
      beneath_function:
        {"416c6f115b3363194fb9c3ffeac244c1514392fef029c348f8c2963d47bf5bae",
         "482e3db58e8eaa6432e149c0bc4f373413b01bd19a03769a57a97c49538d10ff"},
      rewritten_goal:
        {"0b4633586b603f3907e60d510966bbfcaa74dc40c40532e34efc62260aceb732",
         "d259ed09fe82b7f7e90623db7ca4743b6370b3593143317da7827d1beaec60fc"}
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
