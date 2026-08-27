defmodule Cure.Stdlib.StringFfiBoundaryTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  # `String` is nominal -- `rec String { characters: List(Char) }` -- and erases
  # to `{:String, charlist}`. An `@extern` is a DIRECT Erlang remote call with no
  # marshalling, so every `String` written in an extern signature is an assertion
  # that the Erlang function on the other side produces or consumes that tagged
  # pair. For `:io.put_chars/1`, `:erlang.integer_to_binary/1`, `:string.uppercase/1`
  # and friends the assertion is simply false, and the call dies at run time:
  #
  #     :io.put_chars({:String, ~c"hello world\n"})
  #     ** (ArgumentError) argument error
  #
  # `Std.String`'s own module doc already states the convention -- "BEAM
  # boundaries receive and return code-point lists through small private
  # externs" -- and `Std.String` follows it. These tests pin the convention for
  # every other module that crosses the same boundary.
  defp std(name) do
    module = String.to_atom("Cure.Std." <> Macro.camelize(name))
    {:module, ^module} = :code.ensure_loaded(module)
    module
  end

  # The erased form of a Cure `String`, which is what a BEAM caller must pass.
  defp cure_string(text), do: {:String, String.to_charlist(text)}

  describe "Std.Io" do
    test "println writes its argument and returns unit" do
      m = std("io")
      assert capture_io(fn -> assert m.println(cure_string("hello world")) == :unit end) == "hello world\n"
    end

    test "print writes its argument without a newline" do
      m = std("io")
      assert capture_io(fn -> assert m.print(cure_string("bare")) == :unit end) == "bare"
    end

    test "the rendering functions return Cure strings, not raw Erlang terms" do
      m = std("io")
      assert m.int_to_string(42) == cure_string("42")
      assert m.int_to_string(-1) == cure_string("-1")
      assert m.atom_to_string(:hello) == cure_string("hello")
      assert {:String, chars} = m.float_to_string(1.5)
      assert List.to_string(chars) =~ "1.5"
    end

    test "print_int and print_float round-trip through println" do
      m = std("io")
      assert capture_io(fn -> m.print_int(7) end) == "7\n"
      assert capture_io(fn -> m.print_float(2.5) end) =~ "2.5"
    end
  end

  describe "Std.Char" do
    test "case mapping produces code points, which Std.String tags" do
      c = std("char")
      s = std("string")

      assert c.uppercased_characters(?a) == ~c"A"
      assert c.lowercased_characters(?Z) == ~c"z"
      assert s.uppercased_character(?a) == cure_string("A")
      assert s.lowercased_character(?Z) == cure_string("z")
    end
  end

  describe "Std.Show" do
    test "the primitive show instances produce Cure strings" do
      m = std("show")
      assert apply(m, :"__impl_Show_Std.Int#Int_show", [42]) == cure_string("42")
      assert apply(m, :__impl_Show_Atom_show, [:ok]) == cure_string(":ok")
    end
  end
end
