defmodule Cure.Compiler.MacroPacketTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroPacket}
  alias Cure.Diagnostic.Renderer

  test "builds a dependency-ordered packet layout and property plan" do
    fields = [
      %{name: :version, kind: :scalar, type: :byte},
      %{name: :length, kind: :scalar, type: :byte},
      %{name: :payload, kind: :bytes, length: :length},
      %{name: :crc, kind: :crc, over: [:version, :length, :payload]}
    ]

    assert {:ok, packet} = MacroPacket.build(:Frame, fields, endian: :be)
    assert packet.kind == :quoted_packet
    assert packet.properties == [:round_trip, :total_parse, :fault_rejection]
    assert {:packet_def, [name: :Frame, endian: :be], ^fields} = hd(packet.declarations)
    assert Enum.at(packet.layout, 2) == {:payload, 2, nil}
  end

  test "rejects forward dependencies, missing endianness, and duplicate fields" do
    assert {:error, {:forward_packet_length, :payload, :length}} =
             MacroPacket.build(:Frame, [%{name: :payload, kind: :bytes, length: :length}])

    assert {:error, {:missing_packet_endian, :value}} =
             MacroPacket.build(:Frame, [%{name: :value, kind: :scalar, type: :u16}])

    assert {:error, :duplicate_packet_field} =
             MacroPacket.build(:Frame, [
               %{name: :x, kind: :scalar, type: :byte},
               %{name: :x, kind: :scalar, type: :byte}
             ])
  end

  test "crc coverage names undeclared fields" do
    assert {:error, {:invalid_packet_crc_fields, :crc, [:missing]}} =
             MacroPacket.build(:Frame, [
               %{name: :value, kind: :scalar, type: :byte},
               %{name: :crc, kind: :crc, over: [:value, :missing]}
             ])
  end

  test "every packet validation branch has stable user-facing output" do
    cases = [
      {fn -> MacroPacket.build(42, []) end,
       """
       -- PACKET NAME IS INVALID [E092] -----------------------------------------------

       A packet name must be an atom or string, but this declaration uses `42`.

       Hint: Use a stable packet name such as `Frame`
       """},
      {fn -> MacroPacket.build(:Frame, [], endian: :middle) end,
       """
       -- PACKET BYTE ORDER IS INVALID [E092] -----------------------------------------

       `middle` is not a packet byte order. Multi-byte scalar fields use big-endian
       (`be`) or little-endian (`le`) order.

       Hint: Use `endian: :be` or `endian: :le`
       """},
      {fn -> MacroPacket.build(:Frame, [42]) end,
       """
       -- PACKET FIELD IS MALFORMED [E092] --------------------------------------------

       A packet field must declare a name and one supported shape: constant, scalar,
       bytes, or checksum.

       Hint: Use a `const`, `scalar`, `bytes`, or `crc` field with all required properties
       """},
      {fn -> MacroPacket.build(:Frame, [%{name: :x, kind: :unknown}]) end,
       """
       -- PACKET FIELD IS MALFORMED [E092] --------------------------------------------

       A packet field must declare a name and one supported shape: constant, scalar,
       bytes, or checksum.

       Hint: Use a `const`, `scalar`, `bytes`, or `crc` field with all required properties
       """},
      {fn -> MacroPacket.build(:Frame, [%{kind: :scalar, type: :byte}]) end,
       """
       -- PACKET FIELD HAS NO NAME [E092] ---------------------------------------------

       Every packet field needs a name so later length and checksum fields can refer to
       it.

       Hint: Add a unique `name` to every packet field
       """},
      {fn ->
         MacroPacket.build(:Frame, [
           %{name: :x, kind: :scalar, type: :byte},
           %{name: :x, kind: :scalar, type: :byte}
         ])
       end,
       """
       -- PACKET FIELD NAME IS REPEATED [E092] ----------------------------------------

       Two packet fields have the same name, so generated accessors and layout entries
       would collide.

       Hint: Give every packet field a unique name
       """},
      {fn -> MacroPacket.build(:Frame, [%{name: :x, kind: :scalar, type: :u64}]) end,
       """
       -- PACKET SCALAR TYPE IS UNKNOWN [E092] ----------------------------------------

       `u64` is not a fixed-width packet scalar.

       Hint: Use one of `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, or `byte`
       """},
      {fn -> MacroPacket.build(:Frame, [%{name: :value, kind: :scalar, type: :u16}]) end,
       """
       -- PACKET FIELD NEEDS A BYTE ORDER [E092] --------------------------------------

       The multi-byte `value` field has no byte order, so its encoded bytes would be
       ambiguous.

       Hint: Set `endian: :be` or `endian: :le` on the packet or this field
       """},
      {fn -> MacroPacket.build(:Frame, [%{name: :payload, kind: :bytes, length: :length}]) end,
       """
       -- PACKET LENGTH FIELD COMES TOO LATE [E092] -----------------------------------

       The `payload` field takes its length from `length`, but that length field has
       not been decoded yet.

       Hint: Declare `length` before `payload`
       """},
      {fn ->
         MacroPacket.build(:Frame, [
           %{name: :value, kind: :scalar, type: :byte},
           %{name: :crc, kind: :crc, over: [:value, :missing]}
         ])
       end,
       """
       -- PACKET CHECKSUM REFERENCES UNAVAILABLE FIELDS [E092] ------------------------

       The `crc` checksum includes `missing`, but those fields have not been decoded
       before the checksum.

       Hint: List only earlier packet fields in `over`, or move the referenced fields before `crc`
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "packet.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_packet_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end
end
