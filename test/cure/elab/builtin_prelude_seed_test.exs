defmodule Cure.Elab.BuiltinPreludeSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  @bool_src "@group(:core)\nmod Std.Bool\n  @builtin(:bool)\n  type Bool = False | True\n"

  test "compiling Std.Bool's own prelude source registers :bool" do
    {:ok, env} = Cure.Elab.Program.elaborate(@bool_src)
    assert Inductive.builtin(env, :bool) == :"Std.Bool#Bool"
  end

  test "prelude-compiled Bool family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@bool_src)
    seeded = Builtins.seed(Env.empty())
    assert Inductive.get_family(env, :Bool) == Inductive.get_family(seeded, :Bool)
    from_prelude = env |> Inductive.ctors_of(:Bool) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:Bool) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "a @builtin decorator on a non-prelude module cannot hijack the key" do
    # env0 is auto-seeded (Task 4.5), so :bool is always bound to the canonical
    # seeded :Bool. A user module tagging its own `Coin` @builtin(:bool) does NOT
    # capture the key — the register pass only honors @builtin in prelude sources.
    src = "mod M\n  @builtin(:bool)\n  type Coin = Heads | Tails\n"
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :bool) == :"Std.Bool#Bool"
    refute Inductive.builtin(env, :bool) == :Coin
  end
end
