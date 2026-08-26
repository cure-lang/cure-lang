# test/cure/compiler/macro_hygiene_test.exs
defmodule Cure.Compiler.MacroHygieneTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Metadata

  defp parse(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)

    with {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         do: {:ok, Metadata.strip_diagnostics(ast)}
  end

  # Find the first {:fresh_name, _, _} anywhere in an AST. A macro's rule is
  # stored as a plain Elixir map (`%{template: ..., segments: ..., ...}`),
  # not an AST tuple, so the generic tuple-recursion clause below can never
  # reach a rule's `:template` on its own — unwrap it explicitly.
  defp find_fresh(%{template: t}), do: find_fresh(t)
  defp find_fresh({:fresh_name, _, _} = f), do: f
  defp find_fresh({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &find_fresh/1)
  defp find_fresh(_), do: nil

  test "a <fresh Name> in a becomes template parses to a {:fresh_name, meta, name} marker" do
    {:ok, ast} =
      parse("mod M\n  macro G\n    syntax g becomes let <fresh h> = 100 in h\n")

    assert {:fresh_name, _meta, "h"} = find_fresh(ast)
  end

  test "a <fresh Name> lambda parameter binds matching fresh references" do
    {:ok, ast} =
      parse(
        "mod FreshLambda\n  macro Apply\n    syntax apply <n: Code> becomes (fn(<fresh tmp>) -> <fresh tmp>)(n)\n  fn value() -> Int = apply 7\n"
      )

    {:function_call, meta, [_argument]} = fn_body(ast, "value")
    {:lambda, lambda_meta, [{:variable, _, reference}]} = Keyword.fetch!(meta, :callee)
    [{:param, param_meta, binder}] = Keyword.fetch!(lambda_meta, :params)

    assert param_meta[:explicit_fresh]
    assert binder == reference
    refute binder == "tmp"
    refute find_fresh(fn_body(ast, "value"))
  end

  # Find fn body by name (function_def carries name in meta, body as [body]).
  defp fn_body({:function_def, meta, [body]}, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: body)

  defp fn_body({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &fn_body(&1, name))
  defp fn_body(_, _), do: nil

  test "a <fresh> template binder is gensym'd so it cannot capture a same-named use-site arg" do
    # addg's template binds `g` via <fresh g>; the use-site passes its own `g`
    # (the parameter) as the hole. After expansion the binder must be a fresh
    # name (not "g"), distinct from the substituted parameter `g`, so no capture.
    {:ok, ast} =
      parse(
        "mod M\n  macro AddG\n    syntax addg <e: Code> becomes let <fresh g> = 100 in e + g\n  fn f(g: Int) -> Int = addg g\n"
      )

    body = fn_body(ast, "f")
    # body = let <gensym> = 100 in g + <gensym>
    {:block, _, [assign, plus]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:binary_op, _, [{:variable, _, lhs}, {:variable, _, rhs}]} = plus

    # binder was freshened away from "g"
    refute binder == "g"
    # the hole-substituted param stays "g" (NOT captured/freshened)
    assert lhs == "g"
    # the template's own reference `g` was freshened to match the binder
    assert rhs == binder
    # and there is no leftover unexpanded marker ANYWHERE in the expanded body
    refute find_fresh(body)
  end

  test "a <fresh> binder sharing a hole's name does not swallow the use-site argument" do
    # The rule declares BOTH a hole `e` and a template binder `<fresh e>` under the
    # same name. These are two distinct bindings: the hole carries the use-site
    # argument, `<fresh e>` is a template-introduced binder. Freshening must gensym
    # the binder WITHOUT rewriting the plain `e` that is really the hole reference,
    # otherwise the use-site argument is silently dropped (the substitution never
    # finds a plain `e` to replace). Set-of-scopes would keep them apart by scope;
    # here we keep hole material out of the freshening rewrite.
    {:ok, ast} =
      parse(
        "mod M\n  macro Shadow\n    syntax shadow <e: Code> becomes let <fresh e> = 100 in e\n  fn f(x: Int) -> Int = shadow x\n"
      )

    body = fn_body(ast, "f")
    {:block, _, [assign, tail]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:variable, _, tail_name} = tail

    # the <fresh e> binder was gensym'd away from the bare hole name
    refute binder == "e"
    # the trailing `e` is the HOLE: it must become the use-site argument `x`,
    # NOT the freshened binder and NOT dropped.
    assert tail_name == "x"
    # and no unexpanded marker survives anywhere
    refute find_fresh(body)
  end

  test "a use-site name spoofing the gensym namespace cannot capture a <fresh> binder" do
    # The <fresh g> binder would predictably gensym to "g$0" (counter starts at 0).
    # The use-site passes a backtick identifier `g$0` (the only way to write `$` in
    # a name) as the hole, spoofing that gensym. Hygiene must keep the fresh binder
    # distinct from ALL use-site material, so the caller's `g$0` is NOT captured by
    # the template's `let`. The fresh binder therefore skips "g$0".
    {:ok, ast} =
      parse(
        "mod M\n  macro Cap\n    syntax cap <e: Code> becomes let <fresh g> = 100 in e + g\n  fn f() -> Int = cap `g$0`\n"
      )

    body = fn_body(ast, "f")
    {:block, _, [assign, plus]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:binary_op, _, [{:variable, _, lhs}, {:variable, _, rhs}]} = plus

    # the use-site material `g$0` is preserved verbatim (left operand = the hole)
    assert lhs == "g$0"
    # the fresh binder must NOT collide with the spoofed use-site name
    refute binder == "g$0"
    # the template's own reference `g` freshens to match its binder, still distinct
    # from the use-site name — so no capture is possible
    assert rhs == binder
    refute rhs == "g$0"
  end

  test "computed hygiene rewrites explicit markers without rewriting reflected input" do
    generated =
      {:tuple, [],
       [
         {:fresh_name, [], "g"},
         {:variable, [scope: :local], "g"}
       ]}

    {hygienic, next_counter} = Parser.freshen_generated(generated)

    assert {:tuple, [], [{:variable, _, "g$0"}, {:variable, _, "g"}]} = hygienic
    assert next_counter == 1
  end

  test "a computed syntax builder can request the same hygienic freshening pass" do
    source = """
    mod ComputedHygiene
      use Std.Syntax

      macro AddG
        syntax addg <value: Code> computed by build

      fn build(input: AddgSyntax) -> Syntax =
        wrap(input.value)

      fn wrap(value: Syntax) -> Syntax =
        block([
          Node(:assignment, [attr_value(:let, syntax_bool(true))], [fresh("g"), integer(100)]),
          tuple([value, fresh("g")])
        ])

      fn f(g: Int) -> Tuple(Int, Int) = addg g
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :f, [7]) == {7, 100}
  end

  # ---------------------------------------------------------------------------
  # SP5.3 auto full hygiene — auto-rename EVERY unannotated ordinary template
  # binder (no <fresh> needed), keeping <capture> as the opt-out. These fixtures
  # are RED until the scope-aware walk (Task 3) lands; they assert on expanded
  # output. Binder-shape ground-truth is locked in sp53_binder_shapes_test.exs.
  # ---------------------------------------------------------------------------

  test "auto-hygiene: an unannotated let binder is freshened so it cannot capture use-site material" do
    # Template introduces `let acc` with NO <fresh>. The use-site passes its own
    # `acc` (the param) as the hole `e`. Auto-hygiene must gensym the template
    # binder so the hole's `acc` is NOT captured by the template's `let`.
    {:ok, ast} =
      parse(
        "mod M\n  macro Acc\n    syntax m <e: Code> becomes let acc = 0 in e + acc\n  fn f(acc: Int) -> Int = m acc\n"
      )

    body = fn_body(ast, "f")
    {:block, _, [assign, plus]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:binary_op, _, [{:variable, _, hole_ref}, {:variable, _, tmpl_ref}]} = plus

    # the unannotated template binder was auto-freshened away from "acc"
    refute binder == "acc"
    # the hole material (use-site param `acc`) is preserved, NOT captured
    assert hole_ref == "acc"
    # the template's own reference `acc` tracks the freshened binder
    assert tmpl_ref == binder
    refute find_fresh(body)
  end

  test "auto-hygiene: nested let..in shadowing gives each binder a distinct fresh name" do
    # `let x = 1 in let x = 2 in x`: the trailing `x` binds to the INNER `let`.
    # Auto-hygiene must gensym both binders to DISTINCT names and point the
    # trailing reference at the inner one (correct shadowing under freshening).
    {:ok, ast} =
      parse("mod M\n  macro S\n    syntax s becomes let x = 1 in let x = 2 in x\n  fn f() -> Int = s\n")

    body = fn_body(ast, "f")
    {:block, _, [outer_assign, inner_block]} = body
    {:assignment, _, [{:variable, _, outer_b}, _]} = outer_assign
    {:block, _, [inner_assign, {:variable, _, tail}]} = inner_block
    {:assignment, _, [{:variable, _, inner_b}, _]} = inner_assign

    refute outer_b == "x"
    refute inner_b == "x"
    # the two binders are freshened to distinct gensyms (no cross-binding)
    refute outer_b == inner_b
    # the trailing `x` tracks the INNER binder, honoring shadowing
    assert tail == inner_b
  end

  test "auto-hygiene: constructor-pattern destructuring let freshens the LHS leaf, not the RHS" do
    # `let Some(x) = src() in e + x`: the pattern binder `x` (LHS leaf) is a
    # template binder; the RHS `src()` and the hole `e` are use-site/free material.
    # Auto-hygiene must freshen the LHS `x` (and the template's `+ x` reference)
    # while leaving the hole `x` (use-site) and the RHS `src()` untouched.
    {:ok, ast} =
      parse(
        "mod M\n  macro Dbl\n    syntax dbl <e: Code> becomes let Some(x) = src() in e + x\n  fn f(x: Int) -> Int = dbl x\n"
      )

    body = fn_body(ast, "f")
    {:block, _, [assign, plus]} = body
    {:assignment, _, [lhs, rhs]} = assign
    {:function_call, _, [{:variable, _, binder}]} = lhs
    {:binary_op, _, [{:variable, _, hole_ref}, {:variable, _, tmpl_ref}]} = plus

    # the pattern binder `x` (LHS leaf) is auto-freshened away from "x"
    refute binder == "x"
    # the hole `x` (use-site material) is preserved, NOT captured
    assert hole_ref == "x"
    # the template's own `+ x` reference tracks the freshened binder
    assert tmpl_ref == binder
    # the RHS `src()` is left entirely untouched (still a bare call, no args)
    assert {:function_call, _, []} = rhs
  end

  test "auto-hygiene: a free template reference that is neither binder nor hole is left untouched" do
    # `e + freevar`: `e` is a hole (→ use-site `x`), `freevar` is a plain free
    # reference (not a template binder, not a hole). Auto-hygiene must freshen
    # ONLY binders — a free var like `freevar` passes through verbatim, otherwise
    # the walk would over-capture ordinary references (gap-(a) regression guard).
    {:ok, ast} =
      parse("mod M\n  macro Fv\n    syntax fv <e: Code> becomes e + freevar\n  fn f(x: Int) -> Int = fv x\n")

    body = fn_body(ast, "f")
    {:binary_op, _, [{:variable, _, hole_ref}, {:variable, _, free_ref}]} = body

    # the hole `e` is substituted to the use-site arg, NOT freshened
    assert hole_ref == "x"
    # the free reference passes through unchanged
    assert free_ref == "freevar"
  end

  test "auto-hygiene: a <capture Name> binder opts out and binds into caller scope" do
    # `<capture done>` marks a template binder that MUST NOT be freshened — it
    # binds into the caller's scope on purpose (the documented opt-out). After
    # expansion the binder and its reference both stay the literal name `done`.
    {:ok, ast} =
      parse("mod M\n  macro Cap\n    syntax cap becomes let <capture done> = true in done\n  fn f() -> Bool = cap\n")

    body = fn_body(ast, "f")
    {:block, _, [assign, tail]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:variable, _, tail_ref} = tail

    # the <capture done> binder is NOT freshened
    assert binder == "done"
    # its reference stays the same literal name (binds into caller scope)
    assert tail_ref == "done"
    refute find_fresh(body)
  end

  test "auto-hygiene: a match-arm pattern binder is freshened, its body reference tracks it" do
    # `match e / Some(x) -> x / None -> 0` invoked `mt some(x)`: the scrutinee `e`
    # carries the use-site `some(x)`. The arm pattern `Some(x)` binds `x`, used in
    # the arm body. Auto-hygiene freshens the pattern binder + body reference; the
    # scrutinee's use-site `x` (hole material) is preserved.
    {:ok, ast} =
      parse(
        "mod M\n  macro Mt\n    syntax mt <e: Code> becomes match e\n      Some(x) -> x\n      None -> 0\n  fn f(x: Int) -> Int = mt some(x)\n"
      )

    body = fn_body(ast, "f")
    {:pattern_match, _, [scrutinee, arm, _none]} = body
    {:function_call, scrut_meta, [{:variable, _, scrut_ref}]} = scrutinee
    assert Keyword.fetch!(scrut_meta, :name) == "some"
    {:match_arm, arm_meta, [{:variable, _, arm_ref}]} = arm
    {:function_call, pattern_meta, [{:variable, _, binder}]} = Keyword.fetch!(arm_meta, :pattern)
    assert Keyword.fetch!(pattern_meta, :name) == "Some"

    # the pattern binder is auto-freshened away from "x"
    refute binder == "x"
    # the arm body reference tracks the freshened binder
    assert arm_ref == binder
    # the scrutinee's use-site `x` (hole material) is preserved, NOT captured
    assert scrut_ref == "x"
  end

  test "auto-hygiene: a guarded match arm renames the guard reference to the pattern gensym" do
    # `Some(x) when x > 0 -> x`: the guard `x > 0` references the pattern binder.
    # The frame must span BOTH the guard (in meta) and the body, so the guard's
    # `x` is renamed to the SAME gensym as the pattern binder (else it goes free).
    {:ok, ast} =
      parse(
        "mod M\n  macro Mg\n    syntax mg <e: Code> becomes match e\n      Some(x) when x > 0 -> x\n      None -> 0\n  fn f(x: Int) -> Int = mg some(x)\n"
      )

    body = fn_body(ast, "f")
    {:pattern_match, _, [_scrutinee, arm, _none]} = body
    {:match_arm, arm_meta, [{:variable, _, arm_ref}]} = arm
    {:function_call, [{:name, "Some"} | _], [{:variable, _, binder}]} = Keyword.fetch!(arm_meta, :pattern)
    {:binary_op, _, [{:variable, _, guard_ref}, _]} = Keyword.fetch!(arm_meta, :guard)

    refute binder == "x"
    # both the body reference AND the guard reference track the pattern gensym
    assert arm_ref == binder
    assert guard_ref == binder
  end

  test "auto-hygiene: an expression-position lambda param is freshened, its body reference tracks it" do
    # `map(fn(y) -> y + e)` invoked `lm y`: the hole `e` carries the use-site `y`.
    # The lambda param `y` is a template binder; auto-hygiene freshens it and the
    # body reference `y`, while the hole `e` (→ use-site `y`) is preserved.
    {:ok, ast} =
      parse("mod M\n  macro Lm\n    syntax lm <e: Code> becomes map(fn(y) -> y + e)\n  fn f(y: Int) -> Int = lm y\n")

    body = fn_body(ast, "f")
    {:function_call, call_meta, [lambda]} = body
    assert Keyword.fetch!(call_meta, :name) == "map"
    {:lambda, lam_meta, [{:binary_op, _, [{:variable, _, lam_ref}, {:variable, _, hole_ref}]}]} = lambda
    [{:param, _, binder}] = Keyword.fetch!(lam_meta, :params)

    # the lambda param is auto-freshened away from "y"
    refute binder == "y"
    # the template body reference tracks the freshened param
    assert lam_ref == binder
    # the hole `e` (use-site `y`) is preserved, NOT captured by the lambda param
    assert hole_ref == "y"
  end

  test "auto-hygiene: a single-clause named-fn-def param is freshened so it cannot capture the hole" do
    # `fn g(x: Int) = x + e` invoked `withf x`: the hole `e` carries the use-site
    # `x`. The template's `fn g` param `x` is a binder; auto-hygiene freshens it
    # and the `x +` reference, so the hole's `x` (use-site) is NOT captured.
    {:ok, ast} =
      parse(
        "mod M\n  macro Withf\n    syntax withf <e: Code> becomes fn g(x: Int) = x + e\n  fn f(x: Int) -> Int = withf x\n"
      )

    body = fn_body(ast, "f")
    {:function_def, fn_meta, [{:binary_op, _, [{:variable, _, param_ref}, {:variable, _, hole_ref}]}]} = body
    [{:param, _, binder}] = Keyword.fetch!(fn_meta, :params)

    # the fn-def param is auto-freshened away from "x"
    refute binder == "x"
    # the template body reference tracks the freshened param
    assert param_ref == binder
    # the hole `e` (use-site `x`) is preserved, NOT captured by the fn-def param
    assert hole_ref == "x"
  end

  test "auto-hygiene: a guarded/where fn-def renames the guard and constraint references to the param gensym" do
    # `fn g(x: Int) when x > 0 = x + e`: the `guards:` term (in meta) references
    # the param. The frame must span the guard so its `x` tracks the param gensym.
    {:ok, guarded} =
      parse(
        "mod M\n  macro Fg\n    syntax chk <e: Code> becomes fn g(x: Int) when x > 0 = x + e\n  fn f(x: Int) -> Int = chk x\n"
      )

    gbody = fn_body(guarded, "f")
    {:function_def, gmeta, [{:binary_op, _, [{:variable, _, gparam_ref}, _hole]}]} = gbody
    [{:param, _, gbinder}] = Keyword.fetch!(gmeta, :params)
    {:binary_op, _, [{:variable, _, guard_ref}, _]} = Keyword.fetch!(gmeta, :guards)

    refute gbinder == "x"
    assert gparam_ref == gbinder
    # the guard reference tracks the param gensym, not left free / captured
    assert guard_ref == gbinder

    # `fn g(x: Int) where Foo(x) = e`: the `constraints:` term references the param.
    {:ok, whered} =
      parse(
        "mod M\n  macro Fw\n    syntax chk <e: Code> becomes fn g(x: Int) where Foo(x) = e\n  fn f(x: Int) -> Int = chk x\n"
      )

    wbody = fn_body(whered, "f")
    {:function_def, wmeta, [_body]} = wbody
    [{:param, _, wbinder}] = Keyword.fetch!(wmeta, :params)
    [{:function_call, [{:name, "Foo"} | _], [{:variable, _, constraint_ref}]}] = Keyword.fetch!(wmeta, :constraints)

    refute wbinder == "x"
    # the where-clause constraint reference tracks the param gensym
    assert constraint_ref == wbinder
  end

  test "auto-hygiene no-op: a lift-module callback signature (map-shaped OUT set) is left unchanged" do
    # `becomes lift module name / callback init(arg: Int) -> arg`: the callback
    # signature lives in a MAP (§4 OUT set). Auto-hygiene must NOT descend into
    # maps, so the callback param name `arg` stays literal — pinning the boundary
    # so a future executor can't silently "generalize" auto-hygiene into it.
    {:ok, {:container, _, children}} =
      parse(
        "mod M\n  macro Lift\n    syntax mk <name: ModuleName> becomes lift module name\n      behaviour GenServer\n      callback init(arg: Int) -> arg\n  mk Cure.Generated.W\n"
      )

    {:lift_module, meta, []} = List.last(children)
    [callback] = Keyword.fetch!(meta, :callbacks)

    # the map-shaped callback param name is unchanged (walk never entered the map)
    assert [{:param, _, "arg"}] = callback.params
    assert callback.callback_context.parameter_names == ["arg"]
    assert {:variable, _, "arg"} = callback.body
  end

  test "auto-hygiene: a comprehension generator binder (reverse-scope) is freshened over the earlier-sibling body" do
    # `[x + e for x <- xs]` invoked `cmp x`: the hole `e` carries the use-site `x`.
    # The generator binds `x`, scoping the comprehension BODY — an EARLIER sibling
    # (reverse scope). Auto-hygiene must freshen the generator pattern binder AND
    # the body reference `x`, leaving the collection `xs` and the hole `e` (→ `x`).
    {:ok, ast} =
      parse("mod M\n  macro Cmp\n    syntax cmp <e: Code> becomes [x + e for x <- xs]\n  fn f(x: Int) -> Int = cmp x\n")

    body = fn_body(ast, "f")
    {:comprehension, _, [{:binary_op, _, [{:variable, _, body_ref}, {:variable, _, hole_ref}]}, generator]} = body
    {:generator, _, [{:variable, _, binder}, {:variable, _, collection}]} = generator

    # the generator pattern binder is auto-freshened away from "x"
    refute binder == "x"
    # the earlier-sibling body reference tracks the freshened binder (reverse scope)
    assert body_ref == binder
    # the hole `e` (use-site `x`) is preserved, NOT captured by the generator
    assert hole_ref == "x"
    # the collection `xs` is a free reference, left untouched
    assert collection == "xs"
  end

  test "auto-hygiene reconciled with <fresh>: an explicit marker and an auto-discovered binder do not cross-bind" do
    # A template mixing an explicit `<fresh h>` binder with an auto-discovered
    # `let a` binder: each is freshened to its OWN distinct gensym, and each
    # reference tracks its own binder (no cross-binding to the wrong gensym).
    {:ok, ast} =
      parse(
        "mod M\n  macro Mix\n    syntax mix becomes let <fresh h> = 1 in let a = 2 in h + a\n  fn f() -> Int = mix\n"
      )

    body = fn_body(ast, "f")
    {:block, _, [outer_assign, inner_block]} = body
    {:assignment, _, [{:variable, _, h_binder}, _]} = outer_assign
    {:block, _, [inner_assign, {:binary_op, _, [{:variable, _, h_ref}, {:variable, _, a_ref}]}]} = inner_block
    {:assignment, _, [{:variable, _, a_binder}, _]} = inner_assign

    refute h_binder == "h"
    refute a_binder == "a"
    refute h_binder == a_binder
    # each reference tracks its OWN binder
    assert h_ref == h_binder
    assert a_ref == a_binder
    refute find_fresh(body)
  end

  test "a gensym-shaped name lexes as a single identifier token" do
    # Auto-hygiene mints binder names of the form `base$<counter>`. For the
    # expanded corpus to survive a print->reparse round-trip, such a name must
    # lex back as ONE identifier (not `base`, then an unexpected `$`). `$` is a
    # continuation-only char: it may not *start* an identifier.
    {:ok, [tok | rest]} = Lexer.tokenize("initial$0", emit_events: false)
    assert {:identifier, "initial$0"} = {tok.type, tok.value}
    # only the trailing EOF remains
    assert Enum.all?(rest, &(&1.type == :eof))

    # A leading `$` is still not a valid identifier start.
    assert {:error, {:unexpected_character, ?$, _, _}} = Lexer.tokenize("$oops", emit_events: false)
  end

  test "an expanded template with an auto-freshened fn-def param prints and reparses" do
    # This is the corpus-totality scenario in miniature: an OTP-style macro whose
    # template is a single-clause fn-def with an unannotated `initial` param that
    # is also used in the body. Auto-hygiene freshens `initial` -> `initial$N` in
    # both positions; the printed program must reparse (gensym round-trips).
    src =
      "mod M\n  macro Mk\n    syntax mk becomes fn start_link(initial: Int) -> Int = id(initial)\n  fn f() -> Int = mk\n"

    {:ok, ast} = parse(src)

    # `f`'s body IS the expanded start_link fn-def (a nested function_def).
    sl = fn_body(ast, "f")
    assert {:function_def, sl_meta, [call]} = sl
    # both the param binder and its use in the body were freshened to `initial$N`
    assert [{:param, _, pbinder}] = Keyword.fetch!(sl_meta, :params)
    assert String.contains?(pbinder, "$")
    assert {:function_call, _, [{:variable, _, arg} | _]} = call
    assert arg == pbinder

    # print -> reparse is total (would raise :unexpected_character before the fix)
    out = Cure.Compiler.Printer.quoted_to_string(ast)
    assert {:ok, toks2} = Lexer.tokenize(out, emit_events: false)
    assert {:ok, _ast2} = Parser.parse(toks2, emit_events: false)
  end
end
