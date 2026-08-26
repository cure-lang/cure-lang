defmodule Cure.Compiler.PrinterFidelityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}

  # The printer backs `cure fmt` / `cure migrate` / `cure rewrite`, so any node it
  # reprints in a form that reparses differently (or raises) silently corrupts
  # user code. These pin round-trip fidelity for node shapes the precedence
  # tests don't reach: the word-spelled prefix operator `bnot`, implicit type
  # parameters `{T: Type}`, and `with`-abstraction rematch arms.

  defp strip(node) do
    case node do
      {tag, _meta, kids} when is_list(kids) -> {tag, Enum.map(kids, &strip/1)}
      {tag, _meta, kid} -> {tag, strip(kid)}
      list when is_list(list) -> Enum.map(list, &strip/1)
      other -> other
    end
  end

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  defp assert_roundtrips(src) do
    ast = parse!(src)
    out = Printer.quoted_to_string(ast)
    reparsed = parse!(out)

    assert strip(ast) == strip(reparsed),
           "reprint changed the parse.\n  in:  #{inspect(src)}\n  out: #{out}"

    out
  end

  test "opaque type round-trips instead of inspecting the raw container tuple" do
    # `container_to_string`'s catch-all `inspect/1`-ed the `:opaque` container into
    # a raw Elixir tuple that fails to reparse, so `cure migrate` aborted any file
    # containing an `opaque type`. It must reprint as surface `opaque type Name`.
    out = assert_roundtrips("mod M\n  opaque type Handle\n")
    assert out =~ "opaque type Handle"
    refute out =~ ":container"
  end

  test "parameterized opaque type keeps its head params on round-trip" do
    out = assert_roundtrips("mod M\n  opaque type Box(a)\n")
    assert out =~ "opaque type Box(a)"
  end

  test "prefix bnot keeps the separating space (bnot a, not bnota)" do
    out = assert_roundtrips("mod M\n  fn f(a: Int) -> Int = bnot a\n")
    assert out =~ "bnot a"
    refute out =~ "bnota"
  end

  test "bnot nested in a bitwise chain round-trips" do
    assert_roundtrips("mod M\n  fn f(a: Int, b: Int) -> Int = a band bnot b\n")
    assert_roundtrips("mod M\n  fn f(a: Int, b: Int) -> Int = bnot a band b\n")
  end

  test "nested unary minus does not fuse into -- (which re-lexes as an FSM arrow)" do
    # `-(-5)` printed as `--5` re-lexes as the start of an FSM transition `--…`,
    # so the reprint fails to parse. The `-` operand needs a separator when its
    # rendering itself begins with `-`.
    out = assert_roundtrips("mod M\n  fn f(x: Int) -> Int = -(-x)\n")
    refute out =~ "--"
    assert_roundtrips("mod M\n  fn f(x: Int) -> Int = -(-(-x))\n")
  end

  test "an implicit type parameter keeps its braces (stays implicit, not positional)" do
    out = assert_roundtrips("mod M\n  fn id({A: Type}, x: A) -> A = x\n")
    assert out =~ "{A: Type}" or out =~ "{A : Type}"
  end

  test "a typealias reprints as typealias, not type (transparent synonym, not a nominal ADT)" do
    # `typealias X = …` parses to a transparent `:type_annotation`; the printer
    # emitted the keyword `type`, which reparses to a nominal single-constructor
    # `:container` — a different node kind and different semantics. Hits the live
    # corpus (`lib/std/char.cure`, `lib/std/string.cure`).
    out = assert_roundtrips("typealias Char = Bounded(1114112)\n")
    assert out =~ "typealias Char"
    refute out =~ ~r/\btype Char/
  end

  test "a nullary constructor keeps its parens (stays a constructor, not a type reference)" do
    # `None()` in a sum type parses to a nullary constructor `{:function_def,
    # …, []}`; the printer dropped the parens to `None`, which reparses to a bare
    # `{:variable, …}` type reference. Hits `lib/std/option.cure`.
    out = assert_roundtrips("type Option(t) = Some(t) | None()\n")
    assert out =~ "None()"
  end

  test "a with-abstraction rematch arm reprints without crashing" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type NV = VZ | VS(Nat)
      fn foo(n: Nat) -> Nat =
        with view(n)
          S(m) | VS(m) -> S(m)
          Z() | VZ() -> Z()
    """

    out = assert_roundtrips(src)
    assert out =~ "S(m) | VS(m)"
    assert out =~ "Z() | VZ()"
  end

  test "the unit value round-trips as ()" do
    # The parser gives `()` its own node kind (`:unit_value`), not a `:literal`, and the
    # printer had no clause for it — so `cure fmt`/`migrate` RAISED on any file containing
    # the unit value. No stdlib file used `()` until Std.Otp's discard shape did.
    out = assert_roundtrips("mod M\n  fn nothing() -> Unit = ()\n")
    assert out =~ "= ()"
    refute out =~ "unit_value"

    # The shape that exposed it: bind an effectful result, discard it, return unit.
    discard = assert_roundtrips("mod M\n  fn go(p: Int) -> Unit =\n    let x = p\n    ()\n")
    assert discard =~ "()"
  end

  test "a `quote` form round-trips instead of raising" do
    # SP5.1 added `quote <form>` (parses to `:quoted_syntax`), and the stdlib now
    # uses it (fsm.cure `quote :handle_event_function`, actor.cure `quote :ok`),
    # but the printer had no clause for the node — so `cure fmt`/`migrate` RAISED
    # UnprintableNodeError on any file containing `quote`.
    out = assert_roundtrips("mod M\n  fn f() -> Syntax = quote :ok\n")
    assert out =~ "quote :ok"
    refute out =~ "quoted_syntax"
  end

  test "a single `$(e)` splice inside a quote round-trips" do
    out = assert_roundtrips("mod M\n  fn f(x: Syntax) -> Syntax = quote $(x)\n")
    assert out =~ "quote $(x)"
    refute out =~ ":splice"
  end

  test "a `$(e ...)` group splice inside a quote round-trips with its ellipsis" do
    out = assert_roundtrips("mod M\n  fn f(xs: List(Syntax)) -> Syntax = quote [$(xs ...)]\n")
    assert out =~ "$(xs ...)"
    refute out =~ ":splice_group"
  end

  test "a structured-family macro round-trips its header params and family/accepts/expands body" do
    # `macro actor <name: ModuleName>` with a `syntax family`/`accepts`/`expands
    # with` body (the structured OTP surface in actor.cure/fsm.cure). The printer
    # rendered only `macro <name>` — it dropped the `<name: ModuleName>` header
    # params (`leading_segments`) and silently discarded the `:syntax_family`,
    # `:accepts`, and `:expands_with` rules via the `macro_rule_lines` catch-all,
    # so `cure fmt`/`migrate` DELETED the whole macro declaration.
    src = """
    mod M
      macro actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
          optional messages Type
          on_cast Cases
        accepts ActorDefinition
        expands with derive_actor_family
    """

    out = assert_roundtrips(src)
    assert out =~ "macro actor <name: ModuleName>"
    assert out =~ "syntax family ActorDefinition"
    assert out =~ "state Type"
    assert out =~ "optional messages Type"
    assert out =~ "on_cast Cases"
    assert out =~ "accepts ActorDefinition"
    assert out =~ "expands with derive_actor_family"
  end

  test "source-defined family productions survive printing" do
    source = """
    macro fsm <name: ModuleName>
      syntax family Transition
        syntax <from: Name> --<event: Name>--> <to: Name>
      syntax family Definition
        one_or_more transitions Transition
      accepts Definition
      expands with derive
    """

    out = source |> parse!() |> Printer.quoted_to_string()
    assert out =~ "syntax <from: Name> --<event: Name>--> <to: Name>"
    assert out =~ "one_or_more transitions Transition"
    assert {:macro_def, _, [transition, _, _, _]} = parse!(out)
    assert length(transition.productions) == 1
  end

  test "absent optional holes in family productions print and reparse" do
    source = """
    fsm Door with Int
      initial Closed
      transitions
        Closed --Open--> Opened
        Opened --Close(code: Int)--> Closed
    """

    out = assert_roundtrips(source)
    assert out =~ "Closed --Open--> Opened"
    assert out =~ "Opened --Close ( code: Int ) --> Closed"
    refute out =~ "family_option"
  end

  test "a `computed by <fn>` rule with a `Code until` hole round-trips (not dropped)" do
    # A Tier-3 `computed by derive_actor` rule (ActorContainers in actor.cure)
    # stores its expander in `:elab`, not `:template`, so the printer's
    # template-requiring clause never matched it and the catch-all silently
    # dropped the whole rule — losing the generated `ActorSyntax` record on
    # reprint. Its segments also use a `<x: Code until y>` (`:code_hole`), which
    # had no `macro_segment_to_string` clause.
    src = """
    mod M
      macro Box
        syntax box <name: ModuleName> derive <cast_body: Code until call> (call <call_body: Code>)? contextual computed by derive_box
    """

    out = assert_roundtrips(src)
    assert out =~ "computed by derive_box"
    assert out =~ "<cast_body: Code until call>"
    assert out =~ "(call <call_body: Code>)?"
  end

  test "a `Declarations until dedent` hole round-trips (not raised on)" do
    # The `<body: Declarations until dedent>` positional hole (used by the Raw13/
    # Raw14 state-body folds in actor.cure) parses to a `:declarations_hole`
    # segment. `macro_segment_to_string` had clauses for `:raw_hole` and
    # `:code_hole` but none for `:declarations_hole`, so it fell through to the
    # `to_string(other)` catch-all and raised Protocol.UndefinedError on the tuple.
    src = """
    mod M
      macro Box
        syntax box <name: ModuleName> state <state_type: Type> <body: Declarations until dedent> contextual computed directly by derive_box_body
    """

    out = assert_roundtrips(src)
    assert out =~ "computed directly by derive_box_body"
    assert out =~ "<body: Declarations until dedent>"
  end
end
