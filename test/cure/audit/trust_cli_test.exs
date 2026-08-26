defmodule Cure.Audit.TrustCLITest do
  use ExUnit.Case, async: true
  alias Cure.Audit.{CLI, Source}

  test "locates a stdlib module by its mod header, not its filename" do
    assert {:ok, path} = Source.locate("Std.NonEmpty")
    assert Path.basename(path) == "non_empty.cure"

    assert {:ok, path} = Source.locate("Std.CRDT")
    assert Path.basename(path) == "crdt.cure"
  end

  test "std_dir is an absolute compile-time path to the real lib/std" do
    # The CLI seeds this into the import resolver so `use Std.X` imports resolve
    # from any CWD; if it were relative, auditing from outside the repo would
    # silently drop a module into UNAUDITED and look like a clean zero-axiom
    # report.
    dir = Source.std_dir()
    assert Path.type(dir) == :absolute
    assert File.exists?(Path.join(dir, "list.cure"))
  end

  test "import_seed_dir seeds only when NOTHING already resolves the stdlib" do
    # The CLI seeds the baked stdlib dir into the import resolver, but ONLY when
    # no source dir already resolves — otherwise it would outrank (shadow) a
    # stdlib the user configured via CURE_HOME/CURE_LIB, silently auditing the
    # wrong code. `import_seed_dir/1` takes the RESOLVED dir, not just the
    # Application-env override.
    assert Source.import_seed_dir("/some/resolved/stdlib") == nil
    assert Source.import_seed_dir(nil) == Source.std_dir()
  end

  test "--target reaches the JSON payload, not only the text report" do
    {:ok, json} = CLI.run("Std.List", format: "json", target: :atomvm)
    assert json =~ ~s("unavailable_on_target":{"target":"atomvm")

    {:ok, plain} = CLI.run("Std.List", format: "json")
    assert plain =~ ~s("unavailable_on_target":null)
  end

  test "an unknown module is not found" do
    assert Source.locate("Std.NoSuchModule") == {:error, :not_found}
  end

  test "CLI.run propagates a locate miss, which is what the halt(1) clause needs" do
    assert CLI.run("Std.NoSuchModule", []) == {:error, :not_found}
  end

  test "Std.List produces a report and does not fail --strict" do
    assert {:ok, text} = CLI.run("Std.List", [])
    assert text =~ "AXIOMS — OTP (1)"
    assert text =~ "UNAUDITED (0)"
    assert {:ok, _} = CLI.run("Std.List", strict: true)
  end

  test "Std.Io elaborates and lands outside UNAUDITED" do
    assert {:ok, text} = CLI.run("Std.Io", [])
    assert text =~ "UNAUDITED (0)"
  end

  test "--strict succeeds when UNAUDITED is empty" do
    assert {:ok, _} = CLI.run("Std.Io", strict: true)
    assert {:ok, _} = CLI.run("Std.Io", [])
  end

  test "--target adds the section; its absence omits it" do
    {:ok, with_target} = CLI.run("Std.List", target: :atomvm)
    {:ok, without} = CLI.run("Std.List", [])
    assert with_target =~ "UNAVAILABLE ON TARGET"
    refute without =~ "UNAVAILABLE ON TARGET"
  end

  test "two runs are byte-identical" do
    {:ok, a} = CLI.run("Std.List", [])
    {:ok, b} = CLI.run("Std.List", [])
    assert a == b
  end
end

defmodule Cure.Audit.GoldenTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.CLI

  @expected """
  AXIOMS — OTP (1)
    erlang:length/1          ∀ {a}. List(a) -> Int

  AXIOMS — CURE RUNTIME (0)

  AXIOMS — CURE BRIDGE (0)

  OPAQUE TYPES (0)

  KERNEL BUILTINS
    22 builtin operators (Cure.Core.Builtins)

  HOLES (0)

  ABSURD (0)

  NOT PROVEN TOTAL (1)   — cannot be used in proofs; not assumptions
    last

  UNRESOLVED (0)   — names a signature mentions that do not exist

  UNAUDITED (0)
  """

  # `OPAQUE TYPES` is the audited module's own trust surface: what it declares,
  # plus what its reachable definitions name. It is not a census of every opaque
  # family in the environment — once `Tuple` became an ambient `@prelude opaque
  # type`, a census reported it for every module in the language, including ones
  # that never mention a pair.
  test "Std.List matches the spec's sample report" do
    {:ok, text} = CLI.run("Std.List", [])
    assert text == @expected
  end

  test "not-proven-total lists only last, and no axioms" do
    {:ok, text} = CLI.run("Std.List", [])
    [_, tail] = String.split(text, "NOT PROVEN TOTAL (1)", parts: 2)
    [names, _] = String.split(tail, "\n\n", parts: 2)

    # `last` recurses through a nested case scrutinee (its `[x]` middle clause
    # forces `[]`/`[_|t]` to compile inside the outer `[h|t']` case); size-change
    # cannot yet trace the decrease across that nesting, so `last` stays sound-but-
    # unproven. `drop`/`take` delegate to `*_rest` helpers and ARE proven total.
    assert names =~ "last"
    refute names =~ "reverse"
    refute names =~ "drop"
    refute names =~ "take"
    # length/1 is an extern and struct_eq is a builtin op: neither belongs here.
    refute names =~ "length"
    refute names =~ "struct_eq"
  end
end
