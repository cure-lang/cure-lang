defmodule Cure.Compiler.RecordDefaultsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp compile_and_load(source) do
    Compiler.compile_and_load(source, emit_events: false)
  end

  # A record now erases to a tagged, field-ordered BEAM tuple (`{:Point, x, y}`),
  # not a `%{__struct__: …}` map — the classic-pipeline representation is gone.
  # Field access is by declaration-order tuple position (`elem(r, 1)` = first
  # field). The tag keeps the record's declared (PascalCase) name.

  describe "record fields with default values" do
    test "defaults fill in omitted fields at construction time" do
      source = """
      mod RecordDefaults.Simple
        use Std.String
        rec Person
          name: String = "Anonymous"
          age: Int = 0

        fn blank() -> Person = Person{}
        fn named(n: String) -> Person = Person{name: n}
      """

      {:ok, mod} = compile_and_load(source)

      # {:Person, name, age} — `String` is a nominal record, so a string field
      # erases to `{:String, charlist}` rather than to the bare charlist.
      blank = mod.blank()
      assert elem(blank, 0) == :Person
      assert elem(blank, 1) == {:String, ~c"Anonymous"}
      assert elem(blank, 2) == 0

      alice = mod.named({:String, ~c"Alice"})
      assert elem(alice, 1) == {:String, ~c"Alice"}
      # default for age still applies
      assert elem(alice, 2) == 0
    end

    test "caller-provided value overrides the default" do
      source = """
      mod RecordDefaults.Override
        rec Counter
          value: Int = 0

        fn custom(v: Int) -> Counter = Counter{value: v}
      """

      {:ok, mod} = compile_and_load(source)
      # {:Counter, value}
      assert elem(mod.custom(42), 1) == 42
    end

    test "records without defaults still work" do
      source = """
      mod RecordDefaults.NoDefaults
        rec Point
          x: Int
          y: Int

        fn origin() -> Point = Point{x: 0, y: 0}
      """

      {:ok, mod} = compile_and_load(source)
      # {:Point, x, y}
      o = mod.origin()
      assert elem(o, 0) == :Point
      assert elem(o, 1) == 0
      assert elem(o, 2) == 0
    end
  end
end
