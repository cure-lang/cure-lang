defmodule Cure.Elab.PreludeProviderBootstrapTest do
  @moduledoc """
  Every `@prelude` provider must be elaborable with NO prelude of its own.

  `module_prelude_env/1` hands a module in the prelude-bootstrap closure
  `Env.empty()` rather than the prelude slice, because injecting a provider
  back into one of its own dependencies would manufacture a cycle. The price is
  that a provider may rely only on names it EXPLICITLY imports — an ambient name
  that every ordinary module gets for free is not available to it.

  Marking a declaration `@prelude` therefore silently changes the rules for the
  module that holds it, and nothing checked the module still satisfied them.
  `Std.Tuple` gained `@prelude opaque type Tuple`; its `first`/`second` bodies
  are `t.1`/`t.2`, which lower to `Std.Sigma#sigma_first`/`sigma_second` — names
  it had always received ambiently and never imported. It joined the bootstrap
  closure, lost the ambient slice, and every stdlib module that reaches
  `Std.Tuple` through the prelude failed with `{:unknown_global, :sigma_first}`.

  This is the invariant, checked against the live manifest so a provider added
  later is covered without editing this test.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @tag timeout: 300_000
  test "every prelude provider elaborates without an ambient prelude" do
    failures =
      for entry <- Program.prelude_manifest(),
          result = Program.elaborate(File.read!(entry.path), path: entry.path),
          match?({:error, _}, result) do
        {:error, reason} = result
        {entry.source, reason}
      end

    assert failures == [],
           "prelude providers must depend only on what they explicitly `use`:\n" <>
             Enum.map_join(failures, "\n", fn {source, reason} ->
               "  #{source} => #{inspect(reason, limit: 6)}"
             end)
  end
end
