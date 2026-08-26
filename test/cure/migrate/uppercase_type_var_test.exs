defmodule Cure.Migrate.UppercaseTypeVarTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(ast, file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  # Warnings only, skipping the Printer render step — some structured
  # computed-use surfaces (e.g. an actor `on_call` channel) hit an unrelated
  # Printer limitation, and a warning-only assertion isolates the lint.
  defp migrate_warns(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {_new_ast, warns} = Migrate.run(ast, file: file)
    warns
  end

  test "free uppercase type var is lowercased across the signature" do
    {out, warns} = migrate("mod M\nfn id(x: T) -> T = x\n", "a.cure")
    assert out =~ "x: t"
    assert out =~ "-> t"
    refute out =~ "T"
    warning = Enum.find(warns, &(&1.rule == :W_uppercase_type_var))
    assert warning.line == 2
    assert %Cure.Diagnostic.Span{start_column: 10, end_column: 11} = warning.span
  end

  test "a protocol head reports the authored type-parameter span" do
    source = "mod M\nproto Label(T)\n  fn label(x: T) -> String\n"
    {_out, warns} = migrate(source, "protocol_head.cure")

    warning = Enum.find(warns, &(&1.rule == :W_uppercase_type_var))
    assert warning.line == 2
    assert %Cure.Diagnostic.Span{start_line: 2, start_column: 13, end_column: 14} = warning.span
  end

  test "an uppercase name that resolves to a declared type is left alone" do
    {out, _} = migrate("mod M\ntype Foo = Int\nfn f(x: Foo) -> Foo = x\n", "b.cure")
    assert out =~ "Foo"
  end

  test "a built-in primitive type is left alone even with no local type declaration" do
    # `Int` is parsed identically to a free type var (both are a bare
    # `{:variable, [scope: :local], name}` at parser.ex:3281-3305) and this
    # file declares/imports nothing locally -- this only stays untouched if
    # `build_ctx/1` seeds Cure's built-in primitive type names, not just
    # this file's own `type`/`import` declarations.
    {out, warns} = migrate("mod M\nfn f(x: Int) -> Int = x\n", "e.cure")
    assert out =~ "x: Int"
    assert out =~ "-> Int"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a qualified type's module path is not treated as a free type variable" do
    source = "mod M\nfn same(x: Std.Bool.Bool) -> Std.Bool.Bool = x\n"
    {out, warns} = migrate(source, "qualified.cure")

    assert out =~ "Std.Bool.Bool"
    refute out =~ "std.Bool.Bool"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "the kind universe `Type` in an implicit binder is not lowercased" do
    # `{a: Type}` is a dependently-typed implicit parameter: `a` is the binder,
    # `Type` its kind (the universe). `Type` is a built-in sort, not a free type
    # variable — there is no reading of it as a user variable — yet it is absent
    # from `Cure.Types.Env`'s `types` map, so without an explicit ctx seed the
    # rule downgrades it to a distinct free var `type`, corrupting what `a` binds
    # against. This shape pervades the dependently-typed stdlib (vector, sigma,
    # equivalent, …); it must be left untouched.
    {out, warns} = migrate("mod M\nfn f({a: Type}, x: a) -> a = x\n", "kind.cure")
    assert out =~ "{a: Type}"
    refute out =~ "type"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "T and t in the same signature freshen rather than merge" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t) -> T = x\n", "c.cure")
    # every occurrence of the freshened `T` binder becomes `t1` consistently...
    assert out =~ "x: t1"
    assert out =~ "-> t1"
    # ...and the pre-existing `t` binder is untouched, not merged onto
    assert out =~ "y: t)"
    refute out =~ "T"
  end

  test "freshening skips an already-used t1, landing on t2 (spec §7)" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t, z: t1) -> T = x\n", "d.cure")
    # both `t` and `t1` are taken, so the freshened `T` must become `t2`,
    # not collide with either
    assert out =~ "x: t2"
    assert out =~ "-> t2"
    assert out =~ "y: t,"
    assert out =~ "z: t1)"
    refute out =~ "T"
  end

  test "a renamed type var is also renamed where it recurs in the body (let annotation)" do
    # The binder `T` is bound by the signature and referenced again in a body
    # `let y: T = x` type annotation. Renaming only the signature leaves the
    # body annotation dangling on an unbound `T`; the rename must propagate.
    {out, _} = migrate("mod M\nfn id(x: T) -> T =\n  let y: T = x\n  y\n", "f.cure")
    assert out =~ "x: t"
    assert out =~ "-> t"
    assert out =~ "let y: t ="
    refute out =~ "T"
  end

  test "an implicit type-parameter binder is renamed in sync with its references" do
    # `{T: Type}` introduces the type variable via the param NAME `T`. Renaming
    # only the references (`x: T`, `-> T`) while leaving the binder spelled `T`
    # leaves those references bound to nothing — a working file turned broken
    # that the reparse-only verify still accepts. Binder and references must
    # move together.
    {out, _} = migrate("mod M\nfn id({T: Type}, x: T) -> T = x\n", "impl.cure")

    # Reparse and pull the implicit binder name and the reference names back out.
    {:ok, toks} = Lexer.tokenize(out, file: "impl.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "impl.cure", emit_events: false)
    fdef = find_fn(ast)
    params = Keyword.get(elem(fdef, 1), :params)
    return_type = Keyword.get(elem(fdef, 1), :return_type)

    [{:param, binder_meta, binder_name}, {:param, xmeta, _}] = params
    assert Keyword.get(binder_meta, :implicit), "the implicit param lost its :implicit flag"
    {:variable, _, xtype} = Keyword.get(xmeta, :type)
    {:variable, _, rtype} = return_type

    # All three must be the SAME (lowercased) name — no binder/reference desync.
    assert binder_name == xtype
    assert binder_name == rtype
    assert binder_name == String.downcase(binder_name)
  end

  test "a freshened signature binder avoids a distinct lowercase type var used only in the body" do
    # `T` in the signature lowercases to `t`, but the body already uses a
    # distinct free type var `t` in a `let` annotation. Freshening consulted
    # only signature names, so `T`→`t` silently MERGED onto the body's `t` —
    # violating the rule's own "T and t freshen rather than merge" guarantee.
    # The freshener must see the body's `t` and pick `t1`, leaving body `t`.
    {out, _} = migrate("mod M\nfn f(x: T) -> T =\n  let y: t = g(x)\n  y\n", "bodyfresh.cure")
    assert out =~ "x: t1"
    assert out =~ "-> t1"
    assert out =~ "let y: t ="
    refute out =~ "T"
  end

  # Drives the real `cure migrate` path (`run_to_fixpoint` runs proto_to_interface
  # AND uppercase_type_var together), reprinting the converged AST.
  defp migrate_fixpoint(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)

    {:ok, final, _warns} =
      Migrate.run_to_fixpoint(Cure.Compiler.Trivia.attach(ast, trivia), edition: "2026")

    Printer.quoted_to_string(final)
  end

  test "a proto/interface HEAD type var lowercases in lockstep with its method bodies" do
    # The rule lowercased type vars in method signatures but never touched the
    # proto/interface HEAD's own type-parameter binder, so `proto Foo(T)` migrated
    # to `interface Foo(T)` (head `T`) with a body `fn f(a: t) -> t` (body `t`):
    # the binder desynced from every use. Head and body must move together.
    out = migrate_fixpoint("proto Foo(T)\n  fn f(a: T) -> T\n", "iface.cure")

    assert out =~ ~r/interface Foo\(t\)/
    assert out =~ "a: t"
    assert out =~ "-> t"
    refute out =~ "T"
  end

  test "an impl HEAD (for-type + where-constraint) lowercases in lockstep with its body" do
    # The impl head carries its type vars in `for_type` (`List(T)`) and
    # `constraints` (`Ord(T)`) — meta-borne expressions the rule skipped, leaving
    # the head uppercase while the method body lowercased.
    out =
      migrate_fixpoint(
        "impl Ord for List(T) where Ord(T)\n  fn compare(a: List(T), b: List(T)) -> Int = 0\n",
        "impl.cure"
      )

    assert out =~ "List(t)"
    assert out =~ "Ord(t)"
    refute out =~ "List(T)"
    refute out =~ "Ord(T)"
  end

  test "a class type var stays in lockstep with EVERY method even when it collides with a local var in one" do
    # The head freshens `T` against every var the WHOLE body uses, but each method
    # re-derived its own rename against only ITS signature. So when `T`'s lowercase
    # form `t` is taken by a local in ONE method (`f`), the head freshened to `t1`
    # while a method WITHOUT that local (`g`) independently picked `t` — desyncing
    # `g`'s class-param uses from the head binder (and colliding onto `f`'s
    # unrelated `t`). Every class-param use must equal the head binder.
    out =
      migrate_fixpoint("proto Foo(T)\n  fn f(x: t) -> T\n  fn g(x: T) -> T\n", "collide.cure")

    assert out =~ ~r/interface Foo\(t1\)/
    # g's class-param uses track the head binder t1, not the unrelated t
    assert out =~ ~r/fn g\(x: t1\) -> t1/
    # f's class-param return is t1; its distinct local x stays t
    assert out =~ ~r/fn f\(x: t\) -> t1/
  end

  defp find_fn(ast) do
    ast
    |> flatten_nodes()
    |> Enum.find(fn
      {:function_def, _, _} -> true
      _ -> false
    end)
  end

  defp flatten_nodes({_tag, _meta, kids} = node) when is_list(kids) do
    [node | Enum.flat_map(kids, &flatten_nodes/1)]
  end

  defp flatten_nodes(list) when is_list(list), do: Enum.flat_map(list, &flatten_nodes/1)
  defp flatten_nodes(other), do: [other]

  test "a selectively-imported type constructor is left alone, not lowercased" do
    # `build_ctx` never inspected `{:import, …}` nodes, so a `use`-imported type
    # constructor was absent from ctx and UppercaseTypeVar misread it as a free
    # type variable — rewriting `Vec` to the unbound `vec`, a corruption the
    # reprint-only verify accepts and `cure migrate` would write to disk.
    {out, warns} = migrate("mod M\nuse Std.Vector.{Vec}\nfn f(x: Vec) -> Vec = x\n", "imp.cure")
    assert out =~ "x: Vec"
    assert out =~ "-> Vec"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a locally-declared primitive type is left alone, not lowercased" do
    # `collect_type_names` whitelisted only :struct/:enum, so `primitive Word`'s
    # name never entered ctx and `Word` was rewritten to `word`.
    {out, warns} = migrate("mod M\nprimitive Word\nfn w(x: Word) -> Word = x\n", "prim.cure")
    assert out =~ "x: Word"
    assert out =~ "-> Word"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "an opaque type name is left alone, not lowercased" do
    {out, warns} = migrate("mod M\nopaque type Handle\nfn h(x: Handle) -> Handle = x\n", "op.cure")
    assert out =~ "x: Handle"
    assert out =~ "-> Handle"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a file containing an opaque type migrates instead of aborting the whole run" do
    # The opaque type is untouched; the only trigger is the legitimate `use Std.Eq`
    # module rename. Previously the whole-file verify reprint could not render the
    # opaque container, so `run_to_fixpoint` aborted with a spurious
    # {:verify_failed, _} blamed on an innocent rule.
    out = migrate_fixpoint("mod M\nopaque type Handle\nfn f(x: Int) -> Int = x\n", "opfix.cure")
    assert out =~ "opaque type Handle"
    assert out =~ "fn f(x: Int) -> Int = x"
  end

  test "a renamed type var is also renamed in a body type application" do
    # `empty_of(T)` in the body passes the bound type var as a type argument;
    # it must track the signature rename to `t`, not stay `T`.
    {out, _} = migrate("mod M\nfn wrap(x: T) -> List(T) =\n  cons(x, empty_of(T))\n", "g.cure")
    assert out =~ "x: t"
    assert out =~ "List(t)"
    assert out =~ "empty_of(t)"
    refute out =~ "T"
  end

  test "a declared nullary data constructor used as an index is left alone" do
    # `KA` is a nullary variant of the enum `K`, and appears as an *argument*
    # of a type application (`Pair(Int, KA)`) exactly as an optic kind index
    # like `Optic(s, a, LensKind)` does. It parses as a bare `{:variable}` node
    # indistinguishable from a free type var, so it only stays untouched if
    # `build_ctx/1` seeds this file's declared *constructor* names, not just
    # its declared *type* names.
    src = "mod M\ntype K = KA | KB\nfn f(x: Pair(Int, KA)) -> Int = 0\n"
    {out, warns} = migrate(src, "ctor.cure")
    assert out =~ "KA"
    refute out =~ "ka"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a declared opaque type is left alone" do
    # `opaque type Counter` has no body, so it is a `container_type: :opaque`
    # node. `build_ctx/1` must collect opaque type names alongside struct/enum
    # ones, or the opaque handle used in a signature is misread as a type var.
    src = "mod M\nopaque type Counter\nfn f(x: Counter) -> Counter = x\n"
    {out, warns} = migrate(src, "opaque.cure")
    assert out =~ "x: Counter"
    assert out =~ "-> Counter"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a BEAM/container built-in type is left alone" do
    # `Binary`/`Bitstring`/`Map`/`Tuple`/`Nat` are real Cure types (never free
    # type variables), so — like `Type` — the lint's owned `@builtin_type_names`
    # set must list them explicitly, or every signature that mentions them warns
    # spuriously and `cure migrate --all` would corrupt them.
    for ty <- ~w(Binary Bitstring Map Tuple Nat) do
      src = "mod M\nfn f(x: #{ty}) -> #{ty} = x\n"
      {out, warns} = migrate(src, "builtin.cure")
      assert out =~ "x: #{ty}", "#{ty} should be left as-is"

      refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var)),
             "#{ty} should not warn"
    end
  end

  test "a retired process type (Pid/Ref) is left alone" do
    # `Pid` and `Ref` are NOT builtins: the unindexed process surface was retired
    # in favour of `Std.Otp`'s `Pid(m)`/`MonitorRef`/`TimerRef`, and they were
    # dropped from `@builtin_type_names` for exactly that reason — so a stale
    # declaration is caught rather than silently believed.
    #
    # Dropping them from the builtins is not enough on its own. A retired name
    # resolves to nothing, so this lint reads it as a free type variable and
    # lowercases it: `fn me() -> Pid` becomes `fn me() -> pid`, which is a
    # perfectly well-formed signature over a fresh type variable. That converts
    # the elaborator's precise `retired_process_type` diagnostic — the one that
    # names `Pid(m)` as the replacement — into no diagnostic at all, on a file
    # `cure migrate --all` has already rewritten in place.
    #
    # A retired spelling is a real type name the language withdrew, not a type
    # variable, and it has no mechanical replacement (`Pid(m)` needs the message
    # type, which no rewrite can synthesize). So the lint leaves it exactly as
    # authored and lets the elaborator do the talking, the same way
    # `Rules.RemovedModule` leaves a removed `use` in place.
    for ty <- ~w(Pid Ref) do
      src = "mod M\nfn f(x: #{ty}) -> #{ty} = x\n"
      {out, warns} = migrate(src, "retired.cure")
      assert out =~ "x: #{ty}", "#{ty} should be left as-is"
      assert out =~ "-> #{ty}", "#{ty} should be left as-is in return position"

      refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var)),
             "#{ty} is retired, not a type variable"
    end
  end

  test "an imported type or constructor (from `use Std.X`) is left alone" do
    # `Z` is `Std.Nat`'s zero constructor (`type Nat = Z | S(Nat)`), used here as
    # an index. It is neither a builtin nor declared in THIS file — only the
    # imported module knows it — so `build_ctx/1` must resolve `use Std.Nat` and
    # read its exported type/constructor names, or `Z` is misread as a free type
    # variable and lowercased to `z`.
    src = "mod M\nuse Std.Nat\nfn f(v: Pair(Int, Z)) -> Int = 0\n"
    {out, warns} = migrate(src, "imported.cure")
    assert out =~ "Z"
    refute out =~ "Pair(Int, z)"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a marked prelude constructor used with no `use` statement is left alone" do
    # `proof.cure` references `Nat`/`Z`/`S` with NO import node — it gets them
    # from the elaborator's marked prelude (`Std.Nat` et al. imported into
    # every module). `build_ctx/1` must seed the auto-prelude's exported names
    # unconditionally, or `Z` in a file that never wrote `use Std.Nat` is misread
    # as a free type var and lowercased to `z`.
    src = "mod M\nfn f(v: Pair(Int, Z)) -> Int = 0\n"
    {out, warns} = migrate(src, "marked_prelude.cure")
    assert out =~ "Z"
    refute out =~ "Pair(Int, z)"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  @tag :tmp_dir
  test "an imported USER-module constructor (non-Std sibling) is left alone", %{tmp_dir: dir} do
    # The fix must generalise past `Std.*`. `MyApp.Kinds` is a USER module with
    # NO name→path convention — Cure resolves user modules only by co-compiling
    # all inputs together, a registry this per-file lint lacks — so the only
    # handle is a sibling `.cure` file next to the consumer, matched by its
    # declared `mod` name. Here `KA` is a constructor of `MyApp.Kinds`, used as a
    # type-application index; with the sibling present on disk it must resolve to
    # a real name and NOT be lowercased to `ka`.
    File.write!(Path.join(dir, "kinds.cure"), "mod MyApp.Kinds\ntype K = KA | KB\n")

    src = "mod Consumer\nuse MyApp.Kinds\nfn f(v: Pair(Int, KA)) -> Int = 0\n"
    {out, warns} = migrate(src, Path.join(dir, "consumer.cure"))

    assert out =~ "KA"
    refute out =~ "Pair(Int, ka)"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  @tag :tmp_dir
  test "an unresolvable user import does NOT blanket-suppress — real type vars still warn",
       %{tmp_dir: dir} do
    # Guards against the resolution being a no-op that merely suppresses every
    # uppercase name. The consumer imports `MyApp.Kinds`, but NO sibling declares
    # that module (only an unrelated `Other` sits in the directory), so `KA` is
    # genuinely unknown and MUST still warn. If this ever goes quiet, the fix has
    # degenerated into "ignore all uppercase names near a user import".
    File.write!(Path.join(dir, "other.cure"), "mod Other\ntype Q = QA | QB\n")

    src = "mod Consumer\nuse MyApp.Kinds\nfn f(v: Pair(Int, KA)) -> Int = 0\n"
    {out, warns} = migrate(src, Path.join(dir, "consumer.cure"))

    assert out =~ "Pair(Int, ka)"
    assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a structured macro family's generated record type is left alone, not lowercased" do
    # `syntax family FsmDefinition` synthesizes a record `FsmDefinitionSyntax`
    # (`MacroFamily.syntax_type/1`) during lowering, so it is absent from the raw
    # source AST `build_ctx/1` walks. A sibling expander annotated with that
    # generated type (`definition: FsmDefinitionSyntax`) was therefore misread as
    # carrying a free type variable and lowercased to `fsmdefinitionsyntax`,
    # corrupting the stdlib actor/fsm/app/supervisor expanders. `build_ctx/1`
    # must reproduce the macro lowering to learn the generated record names.
    src = """
    mod M
      macro fsm <name: ModuleName>
        syntax family FsmDefinition
          state Type
        accepts FsmDefinition
        expands with expand_fsm
      fn expand_fsm(definition: FsmDefinitionSyntax) -> Int = 0
    """

    {out, warns} = migrate(src, "family.cure")
    assert out =~ "definition: FsmDefinitionSyntax"
    refute out =~ "fsmdefinitionsyntax"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a legacy computed-by macro's generated input record type is left alone" do
    # A legacy `syntax <keyword> … computed by …` rule synthesizes an input record
    # named `syntax_type(keyword)` — here `widget` -> `WidgetSyntax` — with a field
    # per hole. Same gap as the structured family: the record is generated during
    # lowering, absent from the source AST, so an expander's `input: WidgetSyntax`
    # signature must not be misread as a free type variable.
    src = """
    mod M
      macro Widgets
        syntax widget <name: ModuleName> value <v: Type> derive <b: Code> contextual computed by expand_widget
      fn expand_widget(input: WidgetSyntax) -> Int = 0
    """

    {out, warns} = migrate(src, "legacy.cure")
    assert out =~ "input: WidgetSyntax"
    refute out =~ "widgetsyntax"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a genuinely free type var still warns even alongside a macro declaration" do
    # Guards against the macro-name collection degenerating into blanket
    # suppression: a real free type var `T` in a sibling function must still be
    # flagged when the file also contains a macro declaration.
    src = """
    mod M
      macro fsm <name: ModuleName>
        syntax family FsmDefinition
          state Type
        accepts FsmDefinition
        expands with expand_fsm
      fn expand_fsm(definition: FsmDefinitionSyntax) -> Int = 0
      fn id(x: T) -> T = x
    """

    {out, warns} = migrate(src, "mixed.cure")
    assert out =~ "x: t"
    assert out =~ "definition: FsmDefinitionSyntax"
    assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "an actor computed-use's derived ActorMessage/ActorRequest types are not lowercased" do
    src = """
    mod M
      use Std.Actor

      actor Cure.Generated.StructuredCall
        state Int
        on_cast
          Inc -> state + 1
        on_call Read() returns Int
          reply state

    fn make_message() -> ActorMessage = Inc
      fn make_request() -> ActorRequest = Read()
    """

    warns = migrate_warns(src, "actor_use.cure")
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "a genuinely free type var still warns even alongside a computed-use" do
    # Guards against the computed-use type-name collection degenerating into
    # blanket suppression: a real free type var `T` in a sibling function must
    # still be flagged when the module also contains an fsm/actor computed-use.
    src = """
    mod M
      use Std.Actor

      actor Cure.Generated.Structured
        state Int
        on_cast
          Inc -> state + 1

    fn make_message() -> ActorMessage = Inc
      fn id(x: T) -> T = x
    """

    {out, warns} = migrate(src, "actor_use_free.cure")
    assert out =~ "-> ActorMessage"
    assert out =~ "x: t"
    assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "generated type names inside quoted macro declarations are not lowercased" do
    src = """
    mod M
      fn build() -> Int =
        quote (fn handle(message: Message, state: State) -> Tuple(Atom, State) = state)
    """

    {out, warns} = migrate(src, "quoted_generated_scope.cure")

    assert out =~ "message: Message"
    assert out =~ "state: State"
    assert out =~ "Tuple(Atom, State)"
    refute out =~ "message: message"
    refute out =~ "state: state"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end
end
