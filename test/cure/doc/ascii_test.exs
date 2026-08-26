defmodule Cure.Doc.AsciiTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Ascii

  test "renders generic lifted module metadata" do
    callbacks = [%{name: :init, arity: 1}, %{name: :handle, arity: 2}]

    ast =
      {:lift_module,
       [
         behaviour: :user_defined,
         module: "Cure.Example",
         callbacks: callbacks,
         declarations: [{:function_def, [], []}],
         line: 1
       ], []}

    out = Ascii.render(ast)

    assert out =~ "module Cure.Example"
    assert out =~ "behaviour: user_defined"
    assert out =~ "init/1"
    assert out =~ "handle/2"
    assert out =~ "declarations: 1"
  end

  test "returns nil for non-lifted input" do
    assert Ascii.render({:literal, [], 0}) == nil
  end
end
