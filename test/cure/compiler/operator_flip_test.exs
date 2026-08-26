defmodule Cure.Compiler.OperatorFlipTest do
  @moduledoc """
  Phase 3: operators parse via the declaration-driven `FixityTable`, not the
  static `Precedence` table. Word operators (`and`/`or`/`not`) and user-declared
  symbolic operators bind by their `precedencegroup`, and an overloadable
  operator desugars to a call on a function named by its lexeme.
  """
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Emit, Program}

  # -- real evaluation harness (mirrors the Phase-2 differential test) --------

  defp run(src, fname) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    out = :"Cure.OpFlip#{System.unique_integer([:positive])}"
    {:ok, m} = Emit.compile_and_load(env, module: out, functions: fns)
    apply(m, fname, [])
  end

  # The return type is inferred (not annotated), so the harness evaluates
  # value-surface expressions of any type — Bool (`true and false`), Int
  # (`-(5)`), etc. — without forcing an incorrect `-> Bool` annotation.
  defp eval(expr), do: run("mod E\n  fn go() = #{expr}\nend\n", :go)

  defp eval_in(src, call) do
    fname = call |> String.trim_trailing("()") |> String.to_atom()
    run(src, fname)
  end

  # An error tag surfaces from `Program.elaborate/1` either bare (elaboration
  # errors are single tuples) or inside the parser's error LIST (parse errors).
  # Match either wrapping while pinning the tag — the intent, not the envelope.
  defp assert_error_tag(src, tag) do
    assert {:error, payload} = Program.elaborate(src)

    found =
      case payload do
        list when is_list(list) ->
          Enum.find(list, fn candidate ->
            is_tuple(candidate) and tuple_size(candidate) > 0 and elem(candidate, 0) == tag
          end)

        {:source_context, reason, _context} ->
          if is_tuple(reason) and tuple_size(reason) > 0 and elem(reason, 0) == tag, do: reason

        other ->
          if is_tuple(other) and tuple_size(other) > 0 and elem(other, 0) == tag, do: other
      end

    assert found, "expected an #{inspect(tag)} error, got: #{inspect(payload)}"
    found
  end

  test "word operators resolve to their functions" do
    assert eval("true and false") == false
    assert eval("false or true") == true
    assert eval("true or false and false") == true
    assert eval("false or true and false") == false
    assert eval("not true") == false
  end

  test "a user-declared operator dispatches to its function" do
    src = """
    mod M
      use Std.Operators
      precedencegroup Custom
        associativity: left
        higher_than: Additive
      infix `<?>` : Custom
      fn `<?>`(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
      fn go() -> Int = 1 <?> 2 <?> 3
    end
    """

    assert eval_in(src, "go()") == 6
  end

  test "incomparable operators without parens are rejected" do
    src = """
    mod M
      use Std.Operators
      precedencegroup GroupA
        associativity: left
      precedencegroup GroupB
        associativity: left
      infix `<?>` : GroupA
      infix `<!>` : GroupB
      fn `<?>`(a: Int, b: Int) -> Int = a
      fn `<!>`(a: Int, b: Int) -> Int = b
      fn bad() -> Int = 1 <?> 2 <!> 3
    end
    """

    error = assert_error_tag(src, :ambiguous_precedence)
    assert {:ambiguous_precedence, details} = error
    assert details.operator_span.start_line == 11
    assert details.operator_span.start_column == 23
    assert details.span.start_line == 11
    assert details.span.start_column == 29

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "precedence.cure", src)
    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- OPERATOR PRECEDENCE IS AMBIGUOUS [E094] --------------------- precedence.cure

             These operators have no declared relative precedence; add parentheses to choose
             the grouping.

             at precedence.cure:11:29
             11 |   fn bad() -> Int = 1 <?> 2 <!> 3
                |                       ---   ^^^ the conflicting operator is here; this operator has no precedence relative to the surrounding one

             Hint: Add parentheses around the operation that should happen first
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 10, "character" => 28},
             "end" => %{"line" => 10, "character" => 31}
           }

    assert [%{"location" => %{"range" => first_range}, "message" => "the conflicting operator is here"}] =
             lsp["relatedInformation"]

    assert first_range == %{
             "start" => %{"line" => 10, "character" => 22},
             "end" => %{"line" => 10, "character" => 25}
           }
  end

  test "a fixity declaration with no function errors at use" do
    src = """
    mod M
      use Std.Operators
      infix `<@>` : Additive
      fn nope() -> Int = 1 <@> 2
    end
    """

    assert_error_tag(src, :no_operator_meaning)
  end

  test "prefix minus desugars to negate" do
    assert eval("-(5)") == -5
    assert eval("- 5 + 2") == -3
  end

  test "rebinding a builtin syntactic operator is rejected" do
    src = """
    mod M
      use Std.Operators
      infix `|>` : Additive
    end
    """

    assert_error_tag(src, :conflicting_operator_fixity)
  end

  test "redeclaring the fixity of a stdlib operator is rejected as a conflict" do
    # `+`'s fixity is fixed by Std.Operators (now @prelude). Redeclaring its group
    # collides with the prelude entry present in every assembled table — the
    # conflict is detected structurally at parse, not by a location rule.
    src = """
    mod M
      use Std.Operators
      infix `+` : Multiplicative
    end
    """

    assert_error_tag(src, :conflicting_operator_fixity)
  end

  test "redeclaring an imported Melquiades fixity is rejected" do
    src = """
    mod M
      use Std.Otp
      infix `✉` : Additive
    end
    """

    assert_error_tag(src, :conflicting_operator_fixity)
  end

  test "Std.Operators itself elaborates green (idempotent re-add onto its own prelude)" do
    # `Std.Operators` is @prelude, so its own declarations are already in every
    # assembled table's base. Re-folding them while elaborating the module is an
    # identical redeclaration — a no-op, never a self-conflict.
    {:ok, src} = File.read("lib/std/operators.cure")
    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end

  test "a cyclic precedencegroup relation is rejected" do
    # `Ring` binds tighter than `Loop` while `Loop` binds tighter than `Ring`:
    # an unsatisfiable order the toposort would otherwise linearise silently.
    src = """
    mod M
      use Std.Operators
      precedencegroup Ring
        associativity: left
        higher_than: Loop
      precedencegroup Loop
        associativity: left
        higher_than: Ring
    end
    """

    assert {:error, {:precedence_cycle, %{groups: groups, spans: spans}}} =
             Cure.Elab.Program.elaborate(src)

    assert Enum.sort(groups) == [:Loop, :Ring]
    assert Enum.map(spans, & &1.start_line) == [3, 6]
  end

  test "a group closing a cycle through the built-in tower is rejected" do
    # `Weighted` claims to bind BOTH tighter than `Additive` and looser than
    # `Concat`, but the built-in tower already fixes `Additive` tighter than
    # `Concat` — so the three groups form a cycle only visible with the
    # built-in edges included.
    src = """
    mod M
      use Std.Operators
      precedencegroup Weighted
        associativity: left
        higher_than: Additive
        lower_than: Concat
    end
    """

    assert {:error, {:precedence_cycle, %{groups: groups, spans: [_weighted]}}} =
             Cure.Elab.Program.elaborate(src)

    assert :Weighted in groups
  end

  test "a precedence cycle spanning a use edge is rejected in the importer" do
    # A declares `Ga higher_than Gb`; B `use`s A and declares `Gb higher_than Ga`.
    # The cycle is visible only in `fixity(B)` (base + own + use-closure), so this
    # proves the cycle check was repointed off the builtin+own-only table.
    dir = Path.join(System.tmp_dir!(), "of_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    File.write!(
      Path.join(dir, "a.cure"),
      "mod A\n  precedencegroup Ga\n    associativity: left\n    higher_than: Gb\nend\n"
    )

    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])

    src = """
    mod B
      use A
      precedencegroup Gb
        associativity: left
        higher_than: Ga
    end
    """

    try do
      assert {:error, {:precedence_cycle, %{groups: groups, spans: [_gb]}}} =
               Cure.Elab.Program.elaborate(src)

      assert :Ga in groups and :Gb in groups
    after
      Process.put(:cure_source_roots, prev)
      File.rm_rf!(dir)
    end
  end
end
