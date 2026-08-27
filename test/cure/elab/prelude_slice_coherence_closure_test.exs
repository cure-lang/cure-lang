defmodule Cure.Elab.PreludeSliceCoherenceClosureTest do
  @moduledoc """
  A coherence ref kept by a `@prelude` slice must name method globals that are
  still defs in the same env.

  `restrict_env_to(env, :all)` keeps a whole-module provider's coherence WHOLE —
  instance resolution is the reason a typeclass module is `@prelude`, and
  instances are cumulative rather than owned — while restricting the def surface
  to what the provider OWNS plus the globals those owned bodies reach. Coherence
  entries were not part of that seed, so an instance that arrived in the
  provider's env transitively (`Std.Literal`'s `ExpressibleByCharacterLiteral`,
  `Std.String`'s `Semigroup`, …) survived as a ref whose mangled method global
  had been dropped.

  Nothing reports a dangling ref at slice time. It surfaces much later and much
  further away, as `{:unknown_global,
  :"Std.Literal#__impl_ExpressibleByCharacterLiteral_Std.Char#Char_from_character_literal"}`
  in a module that merely wrote `c == '|'` — or, when the site is a literal
  initializer, as `literal_initializer_not_compile_time_value` with an unsolved
  `{:hole, "__pending__"}` in the head. Five stdlib modules failed the first way
  and two the second.

  The ambient prelude of a module that imports nothing is the smallest place the
  invariant is observable, so that is where it is checked.
  """
  use ExUnit.Case, async: false

  alias Cure.Core.Env
  alias Cure.Elab.Program

  defp dangling_refs(env, refs) do
    for {key, ref} <- refs,
        {method, global} <- Map.get(ref, :methods) || %{},
        is_nil(Env.get_def(env, global)) do
      {key, method, global}
    end
  end

  test "no ambient instance names a method global the slice dropped" do
    assert {:ok, env} = Program.elaborate("mod NoImports\n  fn f(x: Int) -> Int = x\nend\n")

    coherence = env.coherence
    assert coherence, "the ambient prelude must contribute a coherence registry at all"

    dangling = dangling_refs(env, coherence.anon) ++ dangling_refs(env, coherence.named)

    assert dangling == [],
           "these ambient instances resolve to globals that are not defs:\n" <>
             Enum.map_join(dangling, "\n", fn {key, method, global} ->
               "  #{inspect(key)} .#{method} -> #{global}"
             end)
  end
end
