defmodule Cure.Elab.ShowDependentTest do
  @moduledoc """
  `Std.Show` on the dependent pipeline. `show/1` is an interface method resolved
  by coherence to a per-type instance; each instance renders to a `String`.
  `String` is nominal -- `rec String { characters: List(Char) }` -- so it erases
  to the tagged pair `{String, chars}` and not to a bare charlist.

  This is the counterpart to `Cure.Elab.SemigroupConcatTest`: `<>` and `show`
  are the two overloaded surfaces the string-producing stdlib rests on. Show was
  previously blocked on the dependent pipeline (its bodies used `<>` and named
  `String` without importing `Std.Semigroup`/`Std.String`, and its FFI helpers
  returned a `Binary` rather than the code-point list the signatures promise; the
  `*_to_list` results are now wrapped into the nominal `String` before leaving
  the module). This
  test pins the end-to-end behaviour so a regression is caught as a run failure,
  not just an elaboration one.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp eval(src, fname, mod, args) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, args)
  end

  test "show(Int) renders decimal digits" do
    src = "mod T\n  use Std.Show\n  fn go() -> String = show(42)\nend\n"
    assert eval(src, :go, :"Cure.ShowIntLit", []) == {:String, ~c"42"}
  end

  test "show dispatches on a variable's declared type" do
    src = "mod T\n  use Std.Show\n  fn go(n: Int) -> String = show(n)\nend\n"
    assert eval(src, :go, :"Cure.ShowIntVar", [7]) == {:String, ~c"7"}
  end

  test "show(Bool) renders the literal words" do
    src = "mod T\n  use Std.Show\n  fn go() -> String = show(true)\nend\n"
    assert eval(src, :go, :"Cure.ShowBool", []) == {:String, ~c"true"}
  end

  test "show composes with `<>` (the interpolation shape)" do
    src = """
    mod T
      use Std.Show
      use Std.Semigroup
      fn go(n: Int) -> String = "n=" <> show(n)
    end
    """

    assert eval(src, :go, :"Cure.ShowCat", [5]) == {:String, ~c"n=5"}
  end
end
