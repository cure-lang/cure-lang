defmodule Cure.Elab.CrossModuleCoherenceTest do
  @moduledoc """
  Regression: interfaces and their instances must survive an import.

  `Program.merge_env/2` — the only function that folds an imported module's env into
  the importer's — built a fresh `%Env{}` literal naming only
  `families/ctors/ctor_to_family/defs/certified/builtins`. `interfaces`, `coherence`,
  and `constrained` were never mentioned, so they reverted to the struct defaults and
  BOTH sides' data was discarded.

  Coherence in Cure is global by design (see `Cure.Elab.Coherence`'s moduledoc). A
  design that can only see instances declared in the current file is not global
  coherence, it is per-file coherence — and worse, it made cross-module overlap
  undetectable: merging a second import wiped the first import's table before the two
  could be compared.

  `merge_env/2` now merges all nine `Env` fields and enforces global coherence across
  the merge. It also carries a compile-time assertion that no `Env` field is left
  unmerged, so the next field added to the struct cannot be silently dropped here.
  """
  use ExUnit.Case, async: false

  alias Cure.Core.Env
  alias Cure.Elab.{Coherence, Program}

  setup do
    tmp =
      Path.join(System.tmp_dir!(), "cure_cross_module_coherence_#{System.unique_integer([:positive])}")

    File.mkdir_p!(tmp)

    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [tmp])

    on_exit(fn ->
      if previous,
        do: Process.put(:cure_source_roots, previous),
        else: Process.delete(:cure_source_roots)

      File.rm_rf!(tmp)
    end)

    {:ok, tmp: tmp}
  end

  test "an interface and its anonymous implementation stay visible to the importing module", %{
    tmp: tmp
  } do
    File.write!(Path.join(tmp, "coimpl.cure"), """
    mod Std.CoImpl
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)

    assert {:ok, env} = Program.elaborate("mod P\n  use Std.CoImpl\n  fn ignore() -> Int = 0\nend\n")

    assert Env.get_interface(env, :Eqs) != nil
    assert {:ok, _dict_ref} = Coherence.lookup_anon(Env.coherence(env), :Eqs, :"Std.Int#Int")
  end

  test "two imported modules supplying the same NAMED instance is an overlap error", %{tmp: tmp} do
    # Merging must preserve the uniqueness rules, not just the table. Named instances
    # are exempt from global (interface, head) uniqueness but their NAMES must still
    # be unique, and before this fix the second import wiped the first's table so the
    # two could never be compared.
    #
    # Method globals now carry their declaring module in their canonical identity,
    # so two modules can no longer merge byte-identical ANONYMOUS descriptors by
    # accident (that overlap is detected — see the anonymous-overlap test below).
    # Named-instance overlap is a separate coherence rule, checked on the `as` name.
    File.write!(Path.join(tmp, "coiface.cure"), """
    mod Std.CoIface
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
    end
    """)

    File.write!(Path.join(tmp, "coone.cure"), """
    mod Std.CoOne
      use Std.CoIface
      implementation Eqs for Int as fast
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)

    File.write!(Path.join(tmp, "cotwo.cure"), """
    mod Std.CoTwo
      use Std.CoIface
      implementation Eqs for Bool as fast
        fn eqs(x: Bool, y: Bool) -> Bool = true
    end
    """)

    src = "mod P\n  use Std.CoOne\n  use Std.CoTwo\n  fn ignore() -> Int = 0\nend\n"

    assert {:error, {:overlapping_named_instance, %{name: :fast}}} = Program.elaborate(src)
  end

  test "two imported modules supplying the same ANONYMOUS instance is an overlap error", %{
    tmp: tmp
  } do
    # The anonymous-provenance gap: two modules each declaring `implementation Eqs
    # for Int` used to produce byte-identical descriptors (`%{iface, head, methods,
    # as}` with no declaring module), so `merge_coherence/2` merged them idempotently
    # as if they were one instance and their method defs collided silently in
    # `env.defs`. Now that method globals carry their declaring module in their
    # canonical identity, the two distinct instances are distinguishable and their
    # global-(interface, head) overlap is caught — while the diamond (same instance,
    # two paths, next test) still merges cleanly.
    File.write!(Path.join(tmp, "anoniface.cure"), """
    mod Std.AnonIface
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
    end
    """)

    File.write!(Path.join(tmp, "anonone.cure"), """
    mod Std.AnonOne
      use Std.AnonIface
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)

    File.write!(Path.join(tmp, "anontwo.cure"), """
    mod Std.AnonTwo
      use Std.AnonIface
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = true
    end
    """)

    src = "mod P\n  use Std.AnonOne\n  use Std.AnonTwo\n  fn ignore() -> Int = 0\nend\n"

    assert {:error, {:overlapping_instance, %{interface: :Eqs, head: :"Std.Int#Int"}}} =
             Program.elaborate(src)
  end

  test "a transitively imported module can use builtin globals", %{tmp: tmp} do
    # `import_source_env/2` elaborated an imported module's declarations against its
    # own imports ALONE, never seeding the builtins — unlike `module_slice_env/1`,
    # which handles the same job for a directly-imported module. So `Int`/`Bool` and
    # every builtin global were missing exactly one import-hop deep.
    File.write!(Path.join(tmp, "seedbase.cure"), """
    mod Std.SeedBase
      fn bump(x: Int) -> Int = int_add(x, 1)
    end
    """)

    File.write!(Path.join(tmp, "seedmid.cure"), "mod Std.SeedMid\n  use Std.SeedBase\nend\n")

    assert {:ok, _env} = Program.elaborate("mod P\n  use Std.SeedMid\n  fn g() -> Int = 0\nend\n")
  end

  test "the same instance reaching the importer by two paths is not an overlap", %{tmp: tmp} do
    # A diamond: P imports both Std.CoDiaA and Std.CoDiaB, and both re-deliver the
    # instance declared once in Std.CoDiaBase. Identical descriptors must merge
    # idempotently rather than trip the uniqueness check.
    File.write!(Path.join(tmp, "codiabase.cure"), """
    mod Std.CoDiaBase
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """)

    for {file, mod} <- [{"codiaa.cure", "Std.CoDiaA"}, {"codiab.cure", "Std.CoDiaB"}] do
      File.write!(Path.join(tmp, file), "mod #{mod}\n  use Std.CoDiaBase\nend\n")
    end

    src = "mod P\n  use Std.CoDiaA\n  use Std.CoDiaB\n  fn ignore() -> Int = 0\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    assert {:ok, _dict_ref} = Coherence.lookup_anon(Env.coherence(env), :Eqs, :"Std.Int#Int")
  end
end
