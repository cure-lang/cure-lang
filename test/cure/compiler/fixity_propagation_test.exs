defmodule Cure.Compiler.FixityPropagationTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.{Lexer, Parser}

  setup do
    dir = Path.join(System.tmp_dir!(), "fp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])

    on_exit(fn ->
      Process.put(:cure_source_roots, prev)
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  defp parse(src, opts \\ []) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(tokens, [emit_events: false] ++ opts)
  end

  test "a module that uses A can parse A's operator; assembly succeeds", %{dir: dir} do
    File.write!(Path.join(dir, "a.cure"), """
    mod A
      precedencegroup G
        associativity: left
      infix `<?>` : G
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    src = "mod B\n  use A\n  fn go() -> Int = 1 <?> 2\nend\n"
    assert {:ok, _ast} = parse(src)
  end

  test "conflicting fixity across two used modules is a parse error", %{dir: dir} do
    File.write!(
      Path.join(dir, "a.cure"),
      "mod A\n  precedencegroup Ga\n    associativity: left\n  infix `<?>` : Ga\nend\n"
    )

    File.write!(
      Path.join(dir, "b.cure"),
      "mod B\n  precedencegroup Gb\n    associativity: left\n  infix `<?>` : Gb\nend\n"
    )

    src = "mod C\n  use A\n  use B\nend\n"
    assert {:error, errors} = parse(src)

    assert Enum.any?(
             errors,
             &match?({:conflicting_operator_fixity, %{operator: "<?>", spans: [_, _]}}, &1)
           )
  end

  test "single-file parse with no source universe still binds core operators" do
    # No :cure_source_roots entries resolve; the built-in prelude still applies.
    Process.put(:cure_source_roots, [])
    src = "mod M\n  fn f(a: Int, b: Int) -> Int = a + b * 2\nend\n"
    assert {:ok, _ast} = parse(src)
  end

  test "a user @prelude module reaches and compiles in a sibling via the driver", %{dir: dir} do
    # P is marked @prelude, so its operator is ambient — a sibling that never
    # `use`s P must still see `<?>`. The compile driver harvests P as a prelude
    # provider (DepGraph.prelude_provider_names/1) and threads it into the
    # parse of M via the :prelude_providers option.
    File.write!(Path.join(dir, "p.cure"), """
    @prelude
    mod P
      precedencegroup G
        associativity: left
      infix `<?>` : G
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    File.write!(Path.join(dir, "m.cure"), "mod M\n  fn go() -> Int = 1 <?> 2\nend\n")

    {:ok, graph} =
      Cure.Compiler.DepGraph.scan([Path.join(dir, "p.cure"), Path.join(dir, "m.cure")])

    providers = Cure.Compiler.prelude_provider_names(graph)
    assert "P" in providers

    # Without the provider list, M cannot see `<?>` (it never `use`s P).
    assert {:error, _} = parse(File.read!(Path.join(dir, "m.cure")))

    # The real driver boundary must do more than parse: P is an implicit source
    # import, so M elaborates the operator meaning regardless of sibling order.
    # `compile_files` computes its own canonical dependency order, so the
    # input list order below is deliberately not pre-sorted.
    out = Path.join(dir, "ebin")

    assert {:ok, %{errors: []}} =
             Cure.Compiler.compile_files([Path.join(dir, "p.cure"), Path.join(dir, "m.cure")],
               output_dir: out,
               emit_events: false,
               source_roots: [dir],
               prelude_providers: providers
             )

    assert apply(:"Cure.M", :go, []) == 1
  end

  test "a @prelude provider propagates operators from its own use-closure", %{dir: dir} do
    # P is @prelude but declares no operator itself; it `use`s H, which declares
    # `<?>`. A sibling M that never `use`s either must still see `<?>` — the
    # provider's operators are its whole use-closure, not just its own(P).
    File.write!(Path.join(dir, "h.cure"), """
    mod H
      precedencegroup G
        associativity: left
      infix `<?>` : G
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    File.write!(Path.join(dir, "p.cure"), "@prelude\nmod P\n  use H\nend\n")
    File.write!(Path.join(dir, "m.cure"), "mod M\n  fn go() -> Int = 1 <?> 2\nend\n")

    {:ok, graph} =
      Cure.Compiler.DepGraph.scan([
        Path.join(dir, "h.cure"),
        Path.join(dir, "p.cure"),
        Path.join(dir, "m.cure")
      ])

    providers = Cure.Compiler.prelude_provider_names(graph)
    assert "P" in providers

    assert {:ok, _ast} =
             parse(File.read!(Path.join(dir, "m.cure")), prelude_providers: providers)
  end

  test "a precedence cycle closed through an ambient provider is rejected", %{dir: dir} do
    File.write!(Path.join(dir, "p.cure"), """
    @prelude
    mod P
      precedencegroup A
        associativity: left
        higher_than: B
    end
    """)

    src = """
    mod M
      precedencegroup B
        associativity: left
        higher_than: A
      fn go() -> Int = 1
    end
    """

    {:ok, graph} = Cure.Compiler.DepGraph.scan([Path.join(dir, "p.cure")])
    providers = Cure.Compiler.prelude_provider_names(graph)

    assert {:error, errors} =
             parse(src, prelude_providers: providers, validate_fixity_cycles: true)

    assert {:precedence_cycle, %{groups: groups, spans: [_]}} =
             Enum.find(errors, &match?({:precedence_cycle, _}, &1))

    assert MapSet.new(groups) == MapSet.new([:A, :B])
  end
end
