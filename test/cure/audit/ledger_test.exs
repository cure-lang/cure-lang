defmodule Cure.Audit.LedgerTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Ledger

  defp audit(src), do: Ledger.audit_source(src, "Test")

  test "an @extern yields exactly one ffi_postulate with its MFA and rendered type" do
    src = """
    mod Test.One
      @extern(:erlang, :length, 1)
      fn len(xs: List(t)) -> Int
    end
    """

    report = audit(src)
    assert [axiom] = report.axioms
    assert axiom.mfa == {:erlang, :length, 1}
    assert axiom.bucket == :otp
    assert axiom.type == "∀ {a}. List(a) -> Int"
  end

  test "widening the declared type changes the rendered line" do
    narrow = """
    mod Test.Narrow
      @extern(:erlang, :length, 1)
      fn len(xs: List(Int)) -> Int
    end
    """

    wide = """
    mod Test.Wide
      @extern(:erlang, :length, 1)
      fn len(xs: List(t)) -> Int
    end
    """

    [a] = audit(narrow).axioms
    [b] = audit(wide).axioms
    assert a.mfa == b.mfa
    refute a.type == b.type
  end

  test "buckets by target module" do
    assert Ledger.bucket({:erlang, :length, 1}) == :otp
    assert Ledger.bucket({:cure_std_crdt, :or_add, 4}) == :cure_runtime
    assert Ledger.bucket({:"Elixir.Cure.FSM.Builtins", :spawn_fsm, 2}) == :cure_bridge
  end

  test "divergence: builtin_op is an axiom here and invisible to codegen reachability" do
    src = """
    mod Test.Arith
      fn double(x: Int) -> Int = x + x
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    roots = Ledger.roots(env)

    # The ledger counts canonical builtin operations, not owner-local aliases.
    assert audit(src).builtin_count == 22

    # Codegen's walk deliberately drops them ("never emitted as a function form").
    codegen_reachable = Cure.Elab.Program.reachable_def_names(env, roots)
    builtin_names = for {n, d} <- env.defs, Map.get(d, :builtin_op), do: n
    assert Enum.all?(builtin_names, fn n -> n not in codegen_reachable end)
    refute builtin_names == []
  end

  test "an opaque type is reported; a genuinely empty inductive is not" do
    opaque = """
    mod Test.Opaque
      opaque type Effect
    end
    """

    empty = """
    mod Test.Empty
      type Void =
        |
    end
    """

    assert audit(opaque).opaque == [:"Test.Opaque#Effect"]
    assert audit(empty).opaque == []
  end

  test "roots exclude the prelude" do
    src = """
    mod Test.Roots
      fn f(x: Int) -> Int = x
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Ledger.roots(env) == [:"Test.Roots#f"]
  end

  test "prelude externs are not attributed to the audited module" do
    src = """
    mod Test.NoPreludeLeak
      fn f(x: Int) -> Int = x
    end
    """

    assert audit(src).axioms == []
  end

  test "an axiom hidden behind a shadowed prelude name is still reported" do
    # `roots/1` diffs the module env against a prelude env. A module may define
    # its own global under a prelude name (`eq`, `plus`, …). If the diff keys on
    # NAME alone, that def is excluded from roots, and if nothing else references
    # it, the whole axiom vanishes — a fail-open hole in a fail-closed tool. The
    # diff must key on (name, body): a redefinition has a different body.
    src = """
    mod Test.Shadow
      @extern(:evil_module, :sneaky_axiom, 2)
      fn eq(x: Int, y: Int) -> Int
    end
    """

    report = Ledger.audit_source(src, "Test.Shadow")
    assert [axiom] = report.axioms
    assert axiom.mfa == {:evil_module, :sneaky_axiom, 2}
  end

  test "a module that fails to elaborate is recorded as unaudited" do
    report = Ledger.audit_source("mod Test.Broken\n  fn f(x: Int) -> = \nend\n", "Test.Broken")
    assert [{"Test.Broken", _reason}] = report.unaudited
    assert report.axioms == []
  end
end

defmodule Cure.Audit.TargetsTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Targets

  test "atomvm lacks re, inets, httpc, persistent_term and Registry" do
    for m <- [:re, :inets, :httpc, :persistent_term, :"Elixir.Registry"] do
      assert Targets.unavailable?(:atomvm, {m, :any, 0}), "expected #{m} unavailable"
    end
  end

  test "atomvm has erlang and lists" do
    refute Targets.unavailable?(:atomvm, {:erlang, :length, 1})
    refute Targets.unavailable?(:atomvm, {:lists, :reverse, 1})
  end

  test "an unknown target has nothing unavailable" do
    assert Targets.unavailable(:no_such_vm) == MapSet.new()
  end

  test "atomvm is a known target" do
    assert :atomvm in Targets.known()
  end
end

defmodule Cure.Audit.UnresolvedTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.{CLI, Ledger}

  # A bodyless `@extern` is a postulate: its signature is believed, not checked,
  # so a name that is defined nowhere — not a def, not a family, not a
  # constructor — still elaborates. The spec asserted this could not happen
  # ("Kernel.infer/2 already rejects dangling globals"). It does happen, and it
  # is a sharp finding: an axiom whose type names something that does not exist.
  #
  # A ledger that raises here is a ledger that cannot audit the modules where
  # this occurs. Report the finding; do not crash on it.
  #
  # This used to be spelled with `Pid`, which was dangling in exactly this way.
  # It no longer is: a bare `Pid` is now rejected outright as
  # `:retired_process_type` in favour of the indexed `RawPid`, so spelling it
  # that way would test the elaborator's refusal rather than the ledger's
  # tolerance. Any never-declared name does the job.

  test "a dangling global in a signature is reported, not raised" do
    src = """
    mod Test.Dangling
      @extern(:erlang, :self, 0)
      fn me() -> Widget
    end
    """

    report = Ledger.audit_source(src, "Test.Dangling")
    assert report.unresolved == [:Widget]
    assert [axiom] = report.axioms
    assert axiom.mfa == {:erlang, :self, 0}
  end

  test "a global naming a real def is not reported unresolved" do
    src = """
    mod Test.Resolved
      fn f(x: Int) -> Int = x
      fn g(x: Int) -> Int = f(x)
    end
    """

    assert Ledger.audit_source(src, "Test.Resolved").unresolved == []
  end

  test "Std.Fsm's macro-only surface introduces no retired FSM bridge" do
    assert {:ok, text} = CLI.run("Std.Fsm", [])

    refute text =~ "Cure.FSM.Builtins"
    refute text =~ "Cure.Fsm.Builtins"
  end

  test "the other OTP-facing modules audit without crashing" do
    for m <- ~w(Std.Actor Std.Supervisor Std.Process) do
      assert {:ok, _} = CLI.run(m, []), "#{m} crashed"
    end
  end
end
