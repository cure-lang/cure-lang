defmodule Cure.Elab.TypeDirectedOverloadTest do
  use ExUnit.Case, async: false

  @moduletag :overload

  # TARGET PIN — type-directed overload resolution (spec
  # `docs/superpowers/specs/2026-07-10-overloading-and-argument-labels-design.md`,
  # design approved `b25081ee`, build deferred). Several functions share a name
  # and the CALL SITE picks the right one from the surrounding type context
  # (Idris2 "elaborate-and-prune", keyed by `(name, arity, argument types)`).
  #
  # This unblocks the stdlib rename workarounds: `Std.Measurements` exposes
  # `add`/`sub` only because a bare `plus` collides with ambient `Std.Nat.plus`;
  # `Std.Char.code_point` is a rename to dodge `Std.String.to_int`. With a
  # type-directed resolver both keep their natural name and the argument type
  # decides. See [[overloading-and-argument-labels-spec]],
  # [[std-units-literal-of-measure-landed]].
  #
  # SCOPE — NAMED resolution only. Making the `+` OPERATOR "just work" on a user
  # type is deliberately OUT of scope here: operator conformance is deferred
  # until a Swift-style precedence-group + custom-infix syntax structure is
  # spec'd, so `+` is resolved as a declared operator (associativity/precedence)
  # rather than hard-coded as a third special case in `elaborate_expr_typed`
  # (alongside the existing Semigroup and Ord routing). That test arrives with
  # the precedence-group spec, not this pin.
  #
  # TODAY (genuinely red — verified against the tree): an overload SET is
  # rejected outright — two `fn plus` in scope fail with
  # `{:codegen_error, {:duplicate_definition, :plus}}`. The surface cannot even
  # EXPRESS a set: globals resolve by bare name, so a duplicate is a collision,
  # not a candidate list. GREEN REQUIRES the front-end to gather an overload set
  # under one name, then prune by argument type at the call site (spec §4). When
  # implemented, delete the `@tag :skip` and this must pass.
  test "a bare overloaded name resolves by argument type at the call site" do
    src = """
    mod TypeDirectedOverloadName
      type Meters = MkM(Int)
      type Grams = MkG(Int)

      fn plus(a: Meters, b: Meters) -> Meters = match a
        MkM(x) -> match b
          MkM(y) -> MkM(x + y)

      fn plus(a: Grams, b: Grams) -> Grams = match a
        MkG(x) -> match b
          MkG(y) -> MkG(x + y)

      fn add_m() -> Int = match plus(MkM(3), MkM(4))
        MkM(x) -> x

      fn add_g() -> Int = match plus(MkG(10), MkG(20))
        MkG(x) -> x
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.TypeDirectedOverloadName"

    assert apply(mod, :add_m, []) == 7
    assert apply(mod, :add_g, []) == 30
  end

  # Task 3 — registration probe. Two type-distinct `plus` members must both
  # register under discriminated keys (no silent overwrite, no
  # duplicate_definition). No overloaded CALL appears here: pruning an applied
  # overloaded call arrives with Task 5; this test asserts only that the surface
  # can now EXPRESS the set.
  test "two same-name defs both register (no silent overwrite)" do
    src = """
    mod OverloadReg
      type Meters = MkM(Int)
      type Grams = MkG(Int)
      fn plus(a: Meters, b: Meters) -> Meters = a
      fn plus(a: Grams, b: Grams) -> Grams = a
    end
    """

    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end

  # Task 4 — overlap legality. Two members of the same overload set whose
  # parameter telescopes are position-wise convertible are indistinguishable at
  # any call site: no argument types can ever pick between them. Registering
  # them silently would make every applied call ambiguous. This is rejected as
  # `{:overlapping_overload, name, arity}` — the successor to the old
  # `duplicate_definition` diagnostic for a true same-signature redefinition.
  test "same-arity indistinguishable overloads are rejected as overlapping" do
    src = """
    mod OverlapReject
      fn dup(a: Int, b: Int) -> Int = a
      fn dup(a: Int, b: Int) -> Int = b
    end
    """

    assert {:error, {:overlapping_overload, %{name: :dup, arity: 2} = details}} = elaborate_error(src)

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:overlapping_overload, details}, "overlap.cure", src)

    assert Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- OVERLOADS OF `DUP` CANNOT BE DISTINGUISHED [E105] -------------- overlap.cure

             Both declarations accept the same parameter types and required argument labels.
             A call cannot provide enough information to choose between them.

             at overlap.cure:3:3
             2 |   fn dup(a: Int, b: Int) -> Int = a
               |   --------------------------------- the first indistinguishable `dup` overload is here
             3 |   fn dup(a: Int, b: Int) -> Int = b
               |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this overload has the same callable signature as the first

             Hint: Change a parameter type or required argument label, or rename one function
             """)

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 2, "character" => 2},
             "end" => %{"line" => 2, "character" => 35}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             %{
               "start" => %{"line" => 1, "character" => 2},
               "end" => %{"line" => 1, "character" => 35}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "arity" => 2,
             "first_id" => "OverlapReject#dup~0",
             "first_signature" => "dup(Int, Int)",
             "kind" => "overlapping_overload",
             "name" => "dup",
             "second_id" => "OverlapReject#dup~1",
             "second_signature" => "dup(Int, Int)"
           }

    fixed = String.replace(src, "fn dup(a: Int, b: Int) -> Int = b", "fn dup_other(a: Int, b: Int) -> Int = b")
    assert {:ok, _environment} = Cure.Elab.Program.elaborate(fixed)
  end

  # Slice C — argument labels break an otherwise-overlapping pair. Both members
  # have the identical type `Int -> Int`, so pre-Ph2 they would be rejected as
  # `overlapping_overload`. Distinct labels (`to` vs `from`) make them tellable
  # apart at any call site, so they legally co-register.
  test "same-type overloads with distinct argument labels co-register" do
    src = """
    mod LabelDistinct
      fn move(to dest: Int) -> Int = dest
      fn move(from src: Int) -> Int = src
    end
    """

    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end

  # The label-relaxation is not a blanket escape: two members that share BOTH the
  # same types AND the same label are still indistinguishable and rejected.
  test "same-type overloads with the SAME label are still overlapping" do
    src = """
    mod LabelSame
      fn move(to dest: Int) -> Int = dest
      fn move(to dest: Int) -> Int = dest
    end
    """

    assert {:error, {:overlapping_overload, %{name: :move, arity: 1}}} = elaborate_error(src)
  end

  # Task 5 — call-site pruning failure. When no member's parameter types match
  # the inferred argument types, the call is `{:no_matching_overload, name, _}`
  # rather than silently dispatching one arbitrarily.
  test "no overload matches the argument types" do
    src = """
    mod OvlNoMatch
      type Meters = MkM(Int)
      type Grams = MkG(Int)
      fn plus(a: Meters, b: Meters) -> Meters = a
      fn plus(a: Grams, b: Grams) -> Grams = a
      fn bad() -> Int = match plus(1, 2)
        _ -> 0
    end
    """

    assert {:error, err} = compile_and_load_error(src)
    assert match?({:no_matching_overload, %{name: :plus}}, unwrap_inner(err))

    assert {:codegen_error, diagnostic_error} = err
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(diagnostic_error, "no_match.cure", src)

    assert Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NO OVERLOAD OF `PLUS` MATCHES [E093] -------------------------- no_match.cure

             This call supplies argument types `Int, Int`.

             These overloads are available:

             - `OvlNoMatch.plus(Grams, Grams)`
             - `OvlNoMatch.plus(Meters, Meters)`

             at no_match.cure:6:27
             6 |   fn bad() -> Int = match plus(1, 2)
               |                           ^^^^^^^^^^ these arguments do not match any `plus` overload

             Hint: Change the arguments to match one of the listed signatures
             """)

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 26},
             "end" => %{"line" => 5, "character" => 36}
           }

    assert lsp["data"]["payload"]["arguments"] == ["Int", "Int"]

    assert Enum.map(lsp["data"]["payload"]["candidates"], & &1["signature"]) == [
             "OvlNoMatch.plus(Grams, Grams)",
             "OvlNoMatch.plus(Meters, Meters)"
           ]

    fixed = String.replace(src, "plus(1, 2)", "plus(MkM(1), MkM(2))")
    assert {:ok, module} = Cure.Compiler.compile_and_load(fixed, emit_events: false)
    assert apply(module, :bad, []) == 0
  end

  # Task 7 — inertness. A module with no same-name group must be untouched by the
  # overload machinery: single-provider keys stay bare (`Mod#double`), codegen
  # emits byte-identical names, and ordinary calls still work. Guards the
  # key-format ripple that discriminated keys could otherwise introduce.
  test "a single-definition module is unaffected by the overload machinery" do
    src = """
    mod OvlInert
      fn double(x: Int) -> Int = x + x
      fn quad(x: Int) -> Int = double(double(x))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :quad, [3]) == 12
  end

  # Regression pin for `Resolution.overload_candidates/2`'s ordering: `prefer_local`
  # must run BEFORE `prefer_direct`. A module's own overload members are never
  # listed in its OWN `import_modules`, so if `prefer_direct` ran first it would
  # drop every local member of an overload set (none is a "direct import" of
  # itself), leaving only an ambient `@prelude` provider of the same bare name
  # (e.g. `Std.Nat#plus`) as the sole survivor — silently mis-resolving a call
  # that was meant to hit the local set. Confirmed by construction: swapping the
  # two filters (`prefer_direct` before `prefer_local`) breaks even the stdlib's
  # own build (`Std.Vector`/`Std.Optic` both call a `map` overloaded locally
  # against `Std.List`/`Std.Option`, ambient-shadowed the same way).
  test "a local overload set shadows an ambient prelude provider of the same bare name" do
    src = """
    mod OvlLocalVsPrelude
      type Meters = MkM(Int)
      type Grams = MkG(Int)

      fn plus(a: Meters, b: Meters) -> Meters = match a
        MkM(x) -> match b
          MkM(y) -> MkM(x + y)

      fn plus(a: Grams, b: Grams) -> Grams = match a
        MkG(x) -> match b
          MkG(y) -> MkG(x + y)

      fn add_m() -> Int = match plus(MkM(3), MkM(4))
        MkM(x) -> x
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :add_m, []) == 7
  end

  # Slice D — the headline: argument labels TIE-BREAK an overload set whose
  # members are type-indistinguishable. Both `pick` members have the identical
  # type `Int -> Int`, so argument-type pruning alone cannot choose between them;
  # the written label does. `pick(to: 5)` resolves the `to` member (+1),
  # `pick(from: 5)` the `from` member (+100).
  test "argument labels disambiguate a same-type overload set" do
    src = """
    mod LabelTieBreak
      fn pick(to x: Int) -> Int = x + 1
      fn pick(from x: Int) -> Int = x + 100
      fn use_to() -> Int = pick(to: 5)
      fn use_from() -> Int = pick(from: 5)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :use_to, []) == 6
    assert apply(mod, :use_from, []) == 105
  end

  # Writing an OPTIONAL (single-name) label at an overloaded call site must not
  # break resolution: `describe(x: 5)` echoes the sole parameter's own name,
  # which is legal per spec §3 (`f(5)` or `f(x: 5)`) whether or not `describe`
  # happens to be overloaded. Only argument TYPE need pick the winner here — both
  # candidates are unlabelled (single-name), so the label filter must treat the
  # written "x" as agreeing with both, not reject every candidate outright.
  test "writing an optional single-name label on an overloaded call still resolves by type" do
    src = """
    mod LabelOptionalOverload
      fn describe(x: Int) -> Int = x
      fn describe(x: Int, y: Int) -> Int = x + y
      fn one() -> Int = describe(x: 5)
      fn two() -> Int = describe(x: 5, y: 6)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :one, []) == 5
    assert apply(mod, :two, []) == 11
  end

  # The other half of the tie-break: a BARE call to a mandatorily-labelled set
  # matches no member (every candidate requires its label), so it errors rather
  # than silently dispatching one. `pick(5)` cannot pick `to` or `from`.
  test "a bare call to a mandatorily-labelled overload set matches nothing" do
    src = """
    mod LabelBareMiss
      fn pick(to x: Int) -> Int = x + 1
      fn pick(from x: Int) -> Int = x + 100
      fn bad() -> Int = pick(5)
    end
    """

    assert {:error, err} = compile_and_load_error(src)
    assert match?({:named_argument_mismatch, :missing_label, _}, unwrap_inner(err))
  end

  # A wrong label matches no member either: `pick(via: 5)` names a label neither
  # candidate declares.
  test "an unknown label matches no member" do
    src = """
    mod LabelWrong
      fn pick(to x: Int) -> Int = x + 1
      fn pick(from x: Int) -> Int = x + 100
      fn bad() -> Int = pick(via: 5)
    end
    """

    assert {:error, err} = compile_and_load_error(src)
    assert match?({:named_argument_mismatch, :unknown_label, _}, unwrap_inner(err))
  end

  # Slice E — a two-name parameter declares a MANDATORY external label even on a
  # function that is not overloaded. The single-fn path never reaches the overload
  # pruner, so it validates labels itself: the labelled call is accepted and binds
  # positionally.
  test "a mandatory label is enforced on a non-overloaded function" do
    src = """
    mod LabelSingleOk
      fn move(to dest: Int) -> Int = dest
      fn go() -> Int = move(to: 7)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :go, []) == 7
  end

  # The enforcement half: a bare positional call omits a label the parameter
  # declares mandatory, so it is rejected rather than silently bound.
  test "a bare call to a mandatorily-labelled non-overloaded function is rejected" do
    src = """
    mod LabelSingleMiss
      fn move(to dest: Int) -> Int = dest
      fn bad() -> Int = move(5)
    end
    """

    assert {:error, err} = compile_and_load_error(src)
    assert match?({:named_argument_mismatch, :missing_label, _}, unwrap_inner(err))
  end

  # A written label that names no parameter of a non-overloaded function is
  # likewise rejected.
  test "a wrong label on a non-overloaded function is rejected" do
    src = """
    mod LabelSingleWrong
      fn move(to dest: Int) -> Int = dest
      fn bad() -> Int = move(from: 5)
    end
    """

    assert {:error, err} = compile_and_load_error(src)
    assert match?({:named_argument_mismatch, :unknown_label, _}, unwrap_inner(err))
  end

  # A single-name parameter's label is OPTIONAL: the caller may write it or omit
  # it, and both forms elaborate to the same positional binding.
  test "an optional single-name label is accepted written or omitted" do
    src = """
    mod LabelSingleOptional
      fn inc(x: Int) -> Int = x + 1
      fn bare() -> Int = inc(4)
      fn labelled() -> Int = inc(x: 4)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :bare, []) == 5
    assert apply(mod, :labelled, []) == 5
  end

  # Slice F — the internal binder name of an OPTIONAL (single-name) parameter is
  # retained on the def record, so a written optional label that names no
  # parameter is rejected (spec §4 step 2: a written label must name a parameter).
  test "a wrong optional label on a non-overloaded function is rejected" do
    src = """
    mod LabelOptWrong
      fn inc(x: Int) -> Int = x + 1
      fn bad() -> Int = inc(y: 4)
    end
    """

    assert {:error, err} = compile_and_load_error(src)
    assert match?({:named_argument_mismatch, :unknown_label, _}, unwrap_inner(err))
  end

  # Slice F — a mixed mandatory/optional overload set of the SAME type. Without
  # the retained internal name, `f(to: 5)` matched BOTH members (the optional
  # member's label filter was lenient) and reported a spurious `ambiguous_overload`
  # even though `to:` names only the first. With the name recorded, the written
  # label prunes the optional member and the call resolves.
  test "a written mandatory label resolves against a mixed mandatory/optional overload set" do
    src = """
    mod LabelMixedSet
      fn f(to x: Int) -> Int = x + 1
      fn f(y: Int) -> Int = y + 100
      fn use_to() -> Int = f(to: 5)
      fn use_bare() -> Int = f(5)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :use_to, []) == 6
    assert apply(mod, :use_bare, []) == 105
  end

  # Task 6 — cross-module resolution (Design "Both"). Two `use`d modules each
  # export `to_int` on a different type; an unqualified `to_int(x)` resolves by
  # `x`'s type. Faithful mirror of `Std.Char.code_point` vs `Std.String.to_int`,
  # the rename workaround this feature retires.
  @tag :tmp_dir
  test "an unqualified call resolves across two used modules by argument type", %{tmp_dir: dir} do
    files = %{
      "a.cure" => """
      mod OvlCharMod
        fn to_int(c: Char) -> Int = 65
      end
      """,
      "b.cure" => """
      mod OvlStrMod
        fn to_int(s: String) -> Int = 3
      end
      """,
      "main.cure" => """
      mod OvlXConsumer
        use OvlCharMod
        use OvlStrMod
        fn from_char() -> Int = to_int('A')
        fn from_str() -> Int = to_int("abc")
      end
      """
    }

    assert {:ok, mod} = compile_multi(dir, files, "Cure.OvlXConsumer")
    assert apply(mod, :from_char, []) == 65
    assert apply(mod, :from_str, []) == 3
  end

  # Two direct imports both provide `foo(Int)`: no argument type can pick between
  # them, so the call is `{:ambiguous_overload, name, owners}` rather than an
  # arbitrary dispatch.
  @tag :tmp_dir
  test "genuinely ambiguous cross-module overloads report :ambiguous_overload", %{tmp_dir: dir} do
    files = %{
      "a.cure" => "mod OvlAmbA\n  fn foo(x: Int) -> Int = 1\nend\n",
      "b.cure" => "mod OvlAmbB\n  fn foo(x: Int) -> Int = 2\nend\n",
      "main.cure" => """
      mod OvlAmbC
        use OvlAmbA
        use OvlAmbB
        fn pick() -> Int = foo(1)
      end
      """
    }

    assert {:error, err} = compile_multi_error(dir, files)
    assert match?({:ambiguous_overload, :foo, _}, unwrap_inner(err))

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(err, "main.cure", files["main.cure"])

    assert Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CALL TO `FOO` IS AMBIGUOUS [E093] --------------------------------- main.cure

             Both `OvlAmbA.foo` and `OvlAmbB.foo` accept the arguments at this call site.
             Cure cannot choose one without changing the program's meaning.

             at main.cure:4:22
             4 |   fn pick() -> Int = foo(1)
               |                      ^^^^^^ qualify this call with the module you intend

             Note: While checking canonical module `OvlAmbC` during body_check.

             Hint: Choose `OvlAmbA.foo(...)` or `OvlAmbB.foo(...)`
             """)

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 21},
             "end" => %{"line" => 3, "character" => 27}
           }

    assert lsp["data"]["payload"] == %{
             "kind" => "ambiguous_overload",
             "module_identity" => ["root", "OvlAmbC"],
             "name" => "foo",
             "owners" => ["OvlAmbA", "OvlAmbB"],
             "pipeline_stage" => "body_check",
             "qualified_candidates" => ["OvlAmbA.foo", "OvlAmbB.foo"]
           }

    fixed_files =
      Map.update!(files, "main.cure", &String.replace(&1, "foo(1)", "OvlAmbA.foo(1)"))

    assert {:ok, module} = compile_multi(dir, fixed_files, "Cure.OvlAmbC")
    assert apply(module, :pick, []) == 1
  end

  @tag :tmp_dir
  test "a named call that still fits multiple providers reports E115 ambiguity", %{tmp_dir: dir} do
    files = %{
      "a.cure" => "mod OvlNamedAmbA\n  fn foo(x: Int) -> Int = 1\nend\n",
      "b.cure" => "mod OvlNamedAmbB\n  fn foo(x: Int) -> Int = 2\nend\n",
      "main.cure" => """
      mod OvlNamedAmbC
        use OvlNamedAmbA
        use OvlNamedAmbB
        fn pick() -> Int = foo(x: 1)
      end
      """
    }

    assert {:error, err} = compile_multi_error(dir, files)
    assert match?({:named_argument_mismatch, :ambiguous_label, _}, unwrap_inner(err))
  end

  # The dot-qualified escape hatch names the provider directly, routed through the
  # existing qualified-global clause rather than the overload pruner, so it sidesteps
  # the ambiguity entirely.
  @tag :tmp_dir
  test "qualifying resolves the ambiguity (escape hatch)", %{tmp_dir: dir} do
    files = %{
      "a.cure" => "mod OvlAmbA\n  fn foo(x: Int) -> Int = 1\nend\n",
      "b.cure" => "mod OvlAmbB\n  fn foo(x: Int) -> Int = 2\nend\n",
      "main.cure" => """
      mod OvlAmbD
        use OvlAmbA
        use OvlAmbB
        fn pick() -> Int = OvlAmbA.foo(1)
      end
      """
    }

    assert {:ok, mod} = compile_multi(dir, files, "Cure.OvlAmbD")
    assert apply(mod, :pick, []) == 1
  end

  # Write `files` under `dir/src` with a minimal Cure.toml, compile the project,
  # load every produced beam, and hand back the `Cure.<Start>` module atom. No
  # off-the-shelf helper loads-and-invokes a `compile_project` beam, so the load
  # step is added here.
  defp compile_multi(dir, files, start_module) do
    src = Path.join(dir, "src")
    ebin = Path.join(dir, "ebin")
    File.mkdir_p!(src)

    Enum.each(files, fn {name, body} -> File.write!(Path.join(src, name), body) end)

    File.write!(Path.join(dir, "Cure.toml"), """
    [project]
    name = "ovltest"
    version = "0.1.0"
    source_paths = ["src"]
    """)

    with {:ok, project} <- Cure.Project.load(dir),
         {:ok, %{modules: modules}} <-
           Cure.Project.compile_project(project, output_dir: ebin, check_types: false) do
      artifact_root = Cure.Compiler.Artifacts.Writer.resolve(ebin)
      Code.prepend_path(artifact_root)
      # `compile_project/2` load-after-compiles each beam so downstream modules
      # resolve imports; purge that already-current version before our own reload
      # so a second `load_file` does not trip `:not_purged` on the old code.
      Enum.each(modules, fn m ->
        :code.purge(m)
        {:module, ^m} = :code.load_file(m)
      end)

      {:ok, String.to_existing_atom(start_module)}
    end
  end

  defp compile_multi_error(dir, files) do
    {:error, _} = compile_multi(dir, files, "unused")
  end

  defp elaborate_error(src), do: unwrap(Cure.Elab.Program.elaborate(src))

  defp compile_and_load_error(src), do: Cure.Compiler.compile_and_load(src, emit_events: false)

  # `compile_and_load/2` wraps an elaboration failure as `{:codegen_error, inner}`;
  # `compile_project/2` wraps a per-module failure one layer further as
  # `{:compile_failed, {:codegen_error, inner}}`. Peel either envelope so the test
  # can assert on the overload diagnostic directly.
  defp unwrap_inner({:compile_failed, inner}), do: unwrap_inner(inner)
  defp unwrap_inner({:codegen_error, inner}), do: unwrap_inner(inner)
  defp unwrap_inner({:module_body_check_failed, {_package, _module}, inner}), do: unwrap_inner(inner)
  defp unwrap_inner({:source_context, inner, _context}), do: unwrap_inner(inner)
  defp unwrap_inner(other), do: other

  defp unwrap({:ok, _} = ok), do: flunk("expected an error, got #{inspect(ok)}")
  defp unwrap({:error, reason}), do: {:error, reason}
end
