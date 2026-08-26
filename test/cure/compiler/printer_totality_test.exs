defmodule Cure.Compiler.PrinterTotalityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Printer
  alias Cure.Compiler.Printer.UnprintableNodeError

  test "an unhandled node kind raises loudly, never silently inspects" do
    # A synthetic node kind the Printer has no clause for.
    bogus = {:definitely_not_a_real_node_kind, [line: 1, col: 1], []}

    assert_raise UnprintableNodeError, fn ->
      Printer.quoted_to_string(bogus)
    end
  end

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  # Every non-error node kind the parser can construct in a *well-formed*
  # program. Error/diagnostic node kinds (produced only on parse failure)
  # are excluded — they never appear in a successfully parsed AST.
  @error_node_kinds ~w(
    error expected unexpected_token parser ok pickup_no_else pickup_else_not_last
    pickup_multiple_else lambda_block_unterminated with_multi_arity_mismatch
    named_implicit_not_in_pattern if_deprecated
  )a

  defp node_kinds(ast, acc \\ MapSet.new())

  defp node_kinds({k, _m, ch}, acc) when is_atom(k) and is_list(ch),
    do: Enum.reduce(ch, MapSet.put(acc, k), &node_kinds/2)

  defp node_kinds({k, _m, _v}, acc) when is_atom(k), do: MapSet.put(acc, k)
  defp node_kinds(l, acc) when is_list(l), do: Enum.reduce(l, acc, &node_kinds/2)
  defp node_kinds(_, acc), do: acc

  test "printer is total over the construct-complete fixture (no raise, reparses, fixpoint)" do
    file = "test/fixtures/printer_totality.cure"
    src = File.read!(file)
    ast = parse!(src, file)

    # (a) prints without raising UnprintableNodeError
    out1 = Cure.Compiler.Printer.quoted_to_string(ast)

    # (b) reparses
    ast2 = parse!(out1, file)

    # (c) print is a byte-fixpoint
    out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
    assert out1 == out2
  end

  test "the whole in-repo corpus prints without raising, reparses, and is a print-fixpoint" do
    # Spec §5.3/§7's Printer-totality gate is explicit that this applies to
    # "the whole in-repo .cure corpus", not only the synthetic fixture above:
    # "corpus parse->print never inspects a tuple and always reparses; print
    # is a fixpoint." The fixture test above proves construct-completeness
    # (it is *designed* to contain one of everything); this test proves the
    # same three properties additionally hold for every real file that
    # already exists in this repo, which is a separate, non-redundant claim
    # -- a corpus file could in principle exercise a node-kind combination,
    # ordering, or depth the hand-built fixture doesn't.
    files = Path.wildcard("lib/**/*.cure")

    for file <- files do
      src = File.read!(file)

      with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
           {:ok, ast} <- Parser.parse(toks, file: file, emit_events: false) do
        # A successfully-parsed AST must never contain an error/diagnostic node
        # kind (those are only ever produced on parse failure, per the comment
        # on @error_node_kinds above) -- a genuine invariant this gate is
        # well-positioned to check, since it already walks every corpus file's
        # AST. This is also what actually exercises `@error_node_kinds` and
        # `node_kinds/2` in real test code (both were otherwise unused module
        # attribute/private-function definitions, which fails this project's
        # `mix test --warnings-as-errors` alias -- see mix.exs's `test` alias).
        kinds = node_kinds(ast)

        assert MapSet.disjoint?(kinds, MapSet.new(@error_node_kinds)),
               "#{file}: a successfully parsed AST contained an error node kind: " <>
                 "#{inspect(MapSet.to_list(MapSet.intersection(kinds, MapSet.new(@error_node_kinds))))}"

        # (a) must not raise UnprintableNodeError for any node the corpus exercises.
        out1 = Cure.Compiler.Printer.quoted_to_string(ast)

        # (b) reparses
        {:ok, toks2} = Lexer.tokenize(out1, file: file, emit_events: false)

        assert {:ok, ast2} = Parser.parse(toks2, file: file, emit_events: false),
               "#{file}: migrated/reprinted output failed to reparse"

        # (c) print is a byte-fixpoint
        out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
        assert out1 == out2, "#{file}: print(reparse(print(ast))) != print(ast) -- not a fixpoint"
      end
    end
  end

  # The kinds Cure.Compiler.Printer currently has a `to_string/3` clause
  # for — derived by scanning the module's own source text, not by
  # calling it (calling it would require already knowing each kind's
  # correct arity/shape, which is circular for an exhaustiveness check).
  defp printer_handled_kinds do
    "lib/cure/compiler/printer.ex"
    |> File.read!()
    |> then(&Regex.scan(~r/defp to_string\(\{:([a-z_]+),/, &1))
    |> Enum.map(fn [_, k] -> String.to_atom(k) end)
    |> MapSet.new()
  end

  # Every node-kind atom `parser.ex` constructs as a genuine
  # `{tag, meta, children}` dispatch target (verified by hand against
  # each construction site during the 2026-07-10 plan hardening pass —
  # see the corrected Task-3 list; deliberately NOT auto-derived from a
  # blind regex over parser.ex, which cannot distinguish a real node tag
  # from an internal 2-tuple or a `meta[:kind]` value without reading
  # the surrounding code). Whoever adds a new node kind to the grammar
  # must add it here in the same commit, or this gate cannot do its job.
  @all_node_kinds ~w(
    assignment async_operation attribute_access
    bin_segment binary_op block comment comprehension conditional
    container decorator early_return exception_handling filter
    function_call function_def generator import lambda list literal map
    match_arm pair pattern_match pickup pickup_clause pickup_else
    property range record_update send string_interpolation throw tuple
    type_annotation unary_op variable yield
    pin as_pattern assert_type gadt_ctor indexed_type interface
    implementation pi_type sigma_type with_abs hole forced_pattern
    binary_generator named_implicit_pat union_type typed_pattern
  )a

  # ── Per-kind round-trip unit tests (Task 3) ──────────────────────────────

  test "pin pattern round-trips as ^name" do
    src = """
    mod M
      fn f(t: Atom) -> Bool =
        match t
          ^target -> true
          _ -> false
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "pin.cure"))
    assert out =~ "^target"
    assert parse!(out, "pin.cure")
  end

  test "as-pattern round-trips as name @ inner" do
    src = """
    mod M
      fn f(xs: List) -> List =
        match xs
          whole @ [h | t] -> whole
          _ -> xs
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "as.cure"))
    assert out =~ "whole @ "
    assert parse!(out, "as.cure")
  end

  test "assert_type round-trips as assert_type expr : Type" do
    src = """
    mod M
      fn answer() -> Int = assert_type 42 : Int
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "assert.cure"))
    assert out =~ "assert_type 42 : Int"
    assert parse!(out, "assert.cure")
  end

  test "the nil symbol round-trips as :nil" do
    src = """
    mod M
      fn initial() -> Atom = :nil
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "nil_symbol.cure"))
    assert out =~ "= :nil"
    assert parse!(out, "nil_symbol.cure")
  end

  test "a lifted callback block stays inside the callback when printed" do
    src = """
    lift module Cure.BlockPrinter
      behaviour gen_server
      callback handle_cast(message: Atom, state: Atom) ->
        let tag = message
        pickup
          tag == :stop -> %[:noreply, state]
          else -> %[:noreply, state]
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "callback_block.cure"))
    assert out =~ "callback handle_cast(message: Atom, state: Atom) ->\n"
    assert parse!(out, "callback_block.cure")
  end

  test "hole round-trips as ?name" do
    src = """
    mod M
      fn f() -> Int = ?goal
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "hole.cure"))
    assert out =~ "?goal"
    assert parse!(out, "hole.cure")
  end

  test "forced pattern round-trips as .x and .(compound)" do
    src = """
    mod M
      type Sing indices (n: Nat)
        SZ : Sing(Z)
        SS : Sing(k) -> Sing(S(k))

      fn f(s: Sing(m)) -> Int =
        match s
          SZ({n = .Z}) -> 0
          _ -> 1
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "forced.cure"))
    assert out =~ ".Z"
    assert parse!(out, "forced.cure")
  end

  test "named-implicit dot pattern round-trips as { name = inner }" do
    src = """
    mod M
      type Sing indices (n: Nat)
        SZ : Sing(Z)
        SS : Sing(k) -> Sing(S(k))

      fn f(s: Sing(m)) -> Int =
        match s
          SS({k = .p}, r) -> 1
          _ -> 0
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "nimpl.cure"))
    assert out =~ "{ k = "
    assert parse!(out, "nimpl.cure")
  end

  test "indexed type family with gadt constructors round-trips" do
    src = """
    mod M
      type Vect(a: Type) indices (n: Nat)
        VNil : Vect(a, Z)
        VCons : (k: Nat) -> a -> Vect(a, k) -> Vect(a, S(k))
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "vect.cure"))
    assert out =~ "type Vect(a: Type) indices (n: Nat)"
    assert out =~ "VNil : Vect(a, Z)"
    assert out =~ "VCons : (k: Nat) -> a -> Vect(a, k) -> Vect(a, S(k))"
    assert parse!(out, "vect.cure")
  end

  test "interface round-trips" do
    src = """
    mod M
      interface Show(a)
        fn show(x: a) -> String
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "iface.cure"))
    assert out =~ "interface Show(a)"
    assert out =~ "fn show(x: a) -> String"
    assert parse!(out, "iface.cure")
  end

  test "implementation round-trips" do
    src = """
    mod M
      interface Show(a)
        fn show(x: a) -> String

      implementation Show for Int
        fn show(x: Int) -> String = "int"
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "impl.cure"))
    assert out =~ "implementation Show for Int"
    assert parse!(out, "impl.cure")
  end

  test "pi type round-trips as dependent arrow" do
    src = """
    mod M
      fn f(g: (n: Nat) -> Vect(n)) -> Int = 0
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "pi.cure"))
    assert out =~ "(n: Nat) -> Vect(n)"
    assert parse!(out, "pi.cure")
  end

  test "a dependent function-valued GADT field retains its outer grouping" do
    src = """
    mod M
      type Acc(a: Type) indices (xs: List(a))
        MkAcc : (descend: ((rest: List(a)) -> Acc(a, rest))) -> Acc(a, xs)
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "gadt_pi.cure"))
    assert out =~ "(descend: ((rest: List(a)) -> Acc(a, rest)))"
    assert parse!(out, "gadt_pi.cure")
  end

  test "sigma type round-trips" do
    src = """
    mod M
      fn f(p: Sigma(n: Nat, Vect(n))) -> Int = 0
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "sigma.cure"))
    assert out =~ "Sigma(n: Nat, Vect(n))"
    assert parse!(out, "sigma.cure")
  end

  test "typed typealias parameters round-trip with their annotations" do
    src = """
    mod M
      typealias EqualPair(left: Nat, right: Nat) = Sigma(proof: Equivalent(Nat, left, right), Nat)
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "typed_alias.cure"))

    assert out =~ "typealias EqualPair(left: Nat, right: Nat)"
    assert parse!(out, "typed_alias.cure")
  end

  test "with-abstraction round-trips" do
    src = """
    mod M
      fn f(x: Int) -> Int =
        with g(x)
          0 -> 1
          _ -> 2
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "with.cure"))
    assert out =~ "with g(x)"
    assert parse!(out, "with.cure")
  end

  test "binary generator round-trips as <<pat <- source>>" do
    src = """
    mod M
      fn f(buf: Bitstring) -> List = [b for <<b <- buf>>]
    """

    out = Cure.Compiler.Printer.quoted_to_string(parse!(src, "bingen.cure"))
    assert out =~ "<<b <- buf>>"
    assert parse!(out, "bingen.cure")
  end

  test "every node kind the parser can construct has a matching Printer clause (static, corpus-independent)" do
    missing = MapSet.difference(MapSet.new(@all_node_kinds), printer_handled_kinds())

    assert MapSet.to_list(missing) == [],
           "Printer is missing a to_string/3 clause for: #{inspect(MapSet.to_list(missing))}"
  end
end
