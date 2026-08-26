defmodule Cure.Elab.ImplicitAppUnknownGlobalTest do
  @moduledoc """
  Red→green for the missing-def guard in
  `Elaborator.elaborate_implicit_app_bidirectional/6`.

  Its first act was `%{type: _, quantities: _} = Env.get_def(env, name)`, which
  raises `MatchError` when `name` is not a def in this environment. That is not
  a hypothetical: `Cure.Elab.Resolve.method_call_checked_candidates/7` walks
  EVERY anonymous instance registered for an interface, takes each candidate's
  mangled method global, and elaborates it — deliberately swallowing
  `{:error, _}` so a candidate that does not apply is skipped. A candidate whose
  mangled global is absent from `env.defs` therefore has to yield a diagnostic;
  raising instead aborts the whole compilation and hides every later error in
  the run.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env}
  alias Cure.Elab.Elaborator

  defp env, do: Builtins.seed(Env.empty())

  test "an absent global yields a diagnostic instead of raising" do
    env = env()
    refute Env.get_def(env, :"Nope#absent"), "fixture must name a global that is not a def"

    assert {:error, {:unknown_global, :"Nope#absent"}} =
             Elaborator.elaborate_implicit_global_app(
               env,
               :"Nope#absent",
               [],
               [],
               Context.empty(env)
             )
  end

  test "the diagnostic survives arguments that would themselves need elaboration" do
    env = env()

    args = [{:variable, [line: 1], "unbound_thing"}]

    assert {:error, {:unknown_global, :"Nope#absent"}} =
             Elaborator.elaborate_implicit_global_app(
               env,
               :"Nope#absent",
               args,
               [],
               Context.empty(env)
             )
  end

  test "a candidate sweep skips an absent mangled global rather than aborting" do
    # The shape `Resolve.method_call_checked_candidates/7` relies on: fold over
    # candidates, discard the errors, keep the successes. With the raise in
    # place this reduce blew up on the first absent candidate.
    env = env()
    candidates = [:"Nope#absent", :"AlsoNope#absent"]

    survivors =
      Enum.reduce(candidates, [], fn mangled, acc ->
        case Elaborator.elaborate_implicit_global_app(env, mangled, [], [], Context.empty(env)) do
          {:ok, term, _type} -> [term | acc]
          {:error, _} -> acc
        end
      end)

    assert survivors == []
  end
end
