defmodule Cure.Stdlib.JsonRunTest do
  use ExUnit.Case, async: true

  @json :"Cure.Std.Json"

  # `Std.Json` is written against `String`, which is nominal --
  # `rec String { characters: List(Char) }` -- so it erases to the tagged pair
  # `{:String, code_points}`. A BEAM caller of a compiled Cure function speaks
  # that erased language directly: a bare charlist is not a Cure `String`.
  #
  # Note the doubled tag in `Value`: JSON's own `String(String)` constructor
  # erases to `{:String, <a nominal String>}`, i.e. `{:String, {:String, chars}}`.
  # `Std.Literal`'s spellings stay at `List(Char)` by design -- a literal records
  # raw source text -- so those remain bare charlists below.
  defp cure_string(text), do: {:String, String.to_charlist(text)}

  test "decodes objects, arrays, exact decimals, and surrogate pairs in Cure" do
    source = {:String, ~c"{\"n\":-1.2300e+4,\"s\":\"\\uD83D\\uDE00\",\"a\":[true,null]}"}

    assert {:ok,
            {:Object,
             [
               {:ObjectMember, {:String, ~c"n"}, {:Number, {:DecimalNumber, {:DecimalLiteral, ~c"-1.2300e+4"}}}},
               {:ObjectMember, {:String, ~c"s"}, {:String, {:String, [0x1F600]}}},
               {:ObjectMember, {:String, ~c"a"}, {:Array, [{:Boolean, true}, :Null]}}
             ]}} = apply(@json, :decode, [source])
  end

  test "keeps the three JSON number categories distinct" do
    assert {:ok, {:Number, {:NaturalNumber, {:NaturalLiteral, ~c"12", 12}}}} =
             apply(@json, :decode, [cure_string("12")])

    assert {:ok, {:Number, {:IntegerNumber, {:IntegerLiteral, ~c"-12", -12}}}} =
             apply(@json, :decode, [cure_string("-12")])

    assert {:ok, {:Number, {:DecimalNumber, {:DecimalLiteral, ~c"12.00"}}}} =
             apply(@json, :decode, [cure_string("12.00")])
  end

  test "rejects malformed numbers, trailing input, and trailing commas" do
    for source <- ["01", "1.", "1e", "1 true", "[1,]", ~S({"a":1,})] do
      assert {:error, _reason} = apply(@json, :decode, [cure_string(source)])
    end
  end

  test "encodes the full-name Value representation without the Elixir shim" do
    value =
      {:Object,
       [
         {:ObjectMember, cure_string("message"), {:String, cure_string("a\n\"b")}},
         {:ObjectMember, cure_string("number"), {:Number, {:DecimalNumber, {:DecimalLiteral, ~c"1.2300"}}}}
       ]}

    assert apply(@json, :encode, [value]) ==
             cure_string(~S({"message":"a\n\"b","number":1.2300}))
  end

  test "escapes every JSON control character" do
    text = Enum.to_list(0..31)
    encoded = apply(@json, :encode, [{:String, {:String, text}}])

    assert encoded ==
             {:String,
              ~c"\"\\u0000\\u0001\\u0002\\u0003\\u0004\\u0005\\u0006\\u0007\\b\\t\\n\\u000b\\f\\r\\u000e\\u000f\\u0010\\u0011\\u0012\\u0013\\u0014\\u0015\\u0016\\u0017\\u0018\\u0019\\u001a\\u001b\\u001c\\u001d\\u001e\\u001f\""}

    assert {:ok, {:String, {:String, ^text}}} = apply(@json, :decode, [encoded])
  end

  test "Decimal decoding routes exact JSON numbers through literal protocols" do
    source = """
    mod TypedJsonDecimal
      use Std.Json
      use Std.Decimal
      use Std.Result

      fn value() -> Result(Decimal, DecodeError) =
        assert_type decode_as("1.2300") : Result(Decimal, DecodeError)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, {:Finite, {:FiniteDecimal, :Positive, 12300, -4}}} = apply(module, :value, [])
  end

  test "Nat uses its typed JSON instance" do
    source = """
    mod TypedJsonNat
      use Std.Json
      use Std.Result

      fn natural() -> Result(Nat, DecodeError) =
        assert_type decode_as("42") : Result(Nat, DecodeError)

      fn encoded() -> String = to_json(assert_type 42 : Nat)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, 42} = apply(module, :natural, [])
    assert {:String, ~c"42"} = apply(module, :encoded, [])
  end

  test "parameterized Option codecs receive their element dictionaries" do
    source = """
    mod TypedJsonOption
      use Std.Json
      use Std.Option
      use Std.Result

      fn present() -> Result(Option(Int), DecodeError) =
        assert_type decode_as("-7") : Result(Option(Int), DecodeError)

      fn absent() -> Result(Option(Int), DecodeError) =
        assert_type decode_as("null") : Result(Option(Int), DecodeError)

      fn encoded() -> String =
        encode_optional(assert_type Some(42) : Option(Int))

      fn encoded_nested() -> String =
        to_json(assert_type Some(Some(42)) : Option(Option(Int)))

      fn encode_optional(value: Option(t)) -> String requires ToJSON(t) =
        to_json(value)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, {:some, -7}} = apply(module, :present, [])
    assert {:ok, :none} = apply(module, :absent, [])
    assert {:String, ~c"42"} = apply(module, :encoded, [])
    assert {:String, ~c"42"} = apply(module, :encoded_nested, [])
  end

  test "derived record encoding constructs structured JSON and escapes fields" do
    source = """
    mod DerivedJsonRecord
      use Std.Json

      @derive(ToJSON)
      rec Person
        name: String
        age: Int

      fn encoded() -> String =
        to_json(Person{name: "A\\nB", age: 42})
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:String, ~c"{\"name\":\"A\\nB\",\"age\":42}"} = apply(module, :encoded, [])
  end

  test "derived record decoding checks fields through their FromJSON instances" do
    source = """
    mod DerivedJsonDecodeRecord
      use Std.Json
      use Std.Result

      @derive(FromJSON)
      rec Person
        name: String
        age: Int

      fn decoded() -> Result(Person, DecodeError) =
        assert_type decode_as("{\\\"name\\\":\\\"Ada\\\",\\\"age\\\":36}") : Result(Person, DecodeError)

      fn missing() -> Result(Person, DecodeError) =
        assert_type decode_as("{\\\"name\\\":\\\"Ada\\\"}") : Result(Person, DecodeError)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, {:Person, {:String, ~c"Ada"}, 36}} = apply(module, :decoded, [])
    assert {:error, {:UnexpectedValue, message}} = apply(module, :missing, [])
    assert message == {:String, ~c"missing JSON object member: age"}
  end
end
