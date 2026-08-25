defmodule Cure.Elab.PendingBodyMergeTest do
  @moduledoc """
  An import must not replace an elaborated body with the `__pending__` placeholder.

  `Declarations` forward-declares a signature with `{:hole, "__pending__"}` for a
  body, to be overwritten once the real body elaborates. A module's published env
  can still carry that placeholder for a def it never owned — `Std.String` holds
  a pending record for `Std.Literal`'s `ExpressibleByCharacterLiteral` method — and
  `merge_env/2` merged defs with plain `Map.merge/2`, so the importer's side won
  unconditionally. Importing `Std.String` therefore DELETED the elaborated body
  that the ambient prelude had already supplied.

  Nothing observes that at merge time. It surfaces at the next site that needs to
  REDUCE the body: a character literal is checked by normalising
  `from_character_literal(CharacterLiteral(46))` to `LiteralValue(_)`, which
  cannot pass a hole, so `c == '.'` fails with
  `literal_initializer_not_compile_time_value` and an `{:app, {:hole,
  "__pending__"}, _}` head — in a module whose only sin was `use Std.String`.

  A pending body means "not elaborated yet". It is strictly less information than
  an elaborated body for the same key, so it must lose the merge.
  """
  use ExUnit.Case, async: false

  alias Cure.Core.Env
  alias Cure.Elab.Program

  @method :"Std.Literal#__impl_ExpressibleByCharacterLiteral_Std.Char#Char_from_character_literal"

  test "importing a module keeps an already-elaborated instance body" do
    assert {:ok, env} =
             Program.elaborate("mod KeepsBody\n  use Std.String\n  fn g(x: Int) -> Int = x\nend\n")

    assert %{body: body} = Env.get_def(env, @method),
           "fixture must name a def the ambient prelude supplies"

    refute body == {:hole, "__pending__"},
           "an import replaced an elaborated body with the pending placeholder"
  end

  test "a character literal still elaborates alongside that import" do
    assert {:ok, _env} =
             Program.elaborate(
               "mod LiteralAlongsideImport\n  use Std.String\n  fn f(c: Char) -> Bool = c == '.'\nend\n"
             )
  end
end
