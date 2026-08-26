defmodule Cure.Compiler.AmbientRawActorTest do
  use ExUnit.Case, async: false

  # §1e enabling capability — definition-site (ambient) resolution of a stdlib
  # computed/family macro's expander.
  #
  # A prelude/builtin stdlib macro (`actor`, from Std.Actor) matches its rule
  # heads from BARE source without `use Std.Actor` (the prelude-macro-head gate,
  # parser.ex:582). But a `computed by`/family expander is a Cure FUNCTION that
  # `macro_expand.execute` must elaborate+evaluate in the caller's env; a bare
  # source's env lacks Std.Actor, so the expander is `:unknown_global`. That is
  # the wall that blocks routing the 15 terse raw templates through the shared
  # family emitter: the immutable behavioral guards (container_macro_test.exs)
  # and the Raw01..Raw16 goldens all compile terse raw forms from bare source.
  #
  # The fix is macro hygiene as every real macro system does it (Lean/Racket):
  # the macro's expander resolves in its DEFINITION-SITE scope (Std.Actor), not
  # the use-site. This test pins the capability on the block-form family raw
  # actor: bare source, no `use`, must compile and behave. The raw branch's
  # OUTPUT is self-contained (@extern GenServer callbacks + `%[...]` tuples), so
  # only the EXPANDER needs Std.Actor — user-body elaboration needs nothing.
  @tag timeout: 120_000
  test "bare-source raw family actor expands without use Std.Actor" do
    source = """
    actor Cure.Generated.AmbientRawCast
      state Int
      messages Atom
      handle_cast
        %[:noreply, state]
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.AmbientRawCast", :handle_cast, [:ping, 7]) == {:noreply, 7}
    assert apply(:"Cure.Generated.AmbientRawCast", :init, [3]) == {:ok, 3}
  end
end
