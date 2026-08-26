defmodule Antigen.ManyQuantityDecodeTest do
  @moduledoc """
  Regression: a banked `kind=family` challenge whose ctor field carries the ω
  erasure quantity (`:many`) must decode in a fresh process. The quantity round-trips
  through `to_existing_atom("many")`, so `:many` has to be interned — i.e. present in
  `Challenge.__known_atoms__/0` alongside its siblings `:unrestricted`/`:erased`. Otherwise
  `decode_record` raises `ArgumentError` ("not an already existing atom") in any VM
  that never generated a many-quantity term (e.g. the replay gate). Surfaced by banking
  universes/family seeds.

  The record below is built from string parts (never the `:many` *atom* literal), so
  it faithfully reproduces the cross-process decode — nothing here interns `:many`.
  """
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  # A real universes/family record (ctor field quantity ω): "many" lives only as text
  # inside the base64 scaffold, never as an atom literal.
  @many_quantity_record Enum.join(
                          [
                            "antigen-record",
                            "kind=family",
                            "assay=universes",
                            "label=well_typed",
                            "seed=94754166",
                            "note=parameterized uniform (result param = a)",
                            "scaffold=g3QAAAAFbQAAAAVjdG9yc2wAAAABdAAAAAVtAAAACWFyZ19uYW1lc2wAAAABbQAAAAF4am0AAAAEbmFtZW0AAAACcGNtAAAACnF1YW50aXRpZXNsAAAAAW0AAAAEbWFueWptAAAACnJpZHhfY291bnRhAW0AAAAMcnBhcmFtX2NvdW50YQFqbQAAAA9mYW1faW5kZXhfbmFtZXNsAAAAAW0AAAABbmptAAAACWZhbV9sZXZlbGEAbQAAAAhmYW1fbmFtZW0AAAABUG0AAAAPZmFtX3BhcmFtX25hbWVzbAAAAAFtAAAAAWFq",
                            "key=Y3RvcnM9W2ludF9saXQsaW50X3R5cGUsdHlwZSx2YXJdfGRlcHRoPWIwXzJ8ZmxhZ3M9W2JpbmRlcl9kZXB0aF9iMF8yLGZvcm1lcl9hcHBfbjAsZm9ybWVyX2Nhc2VfbjAsZm9ybWVyX2N0b3JfbjAsZm9ybWVyX2RhdGFfbjAsZm9ybWVyX2VxX24wLGZvcm1lcl9sYW1fbjAsZm9ybWVyX3BpX24wLGZvcm1lcl9yZXdyaXRlX24wXXxsYWJlbD13ZWxsX3R5cGVk",
                            "pieces=fam_param:0::(type 0);;fam_index:0::(int-type);;ctor:0:arg:0::(var 0);;ctor:0:ridx:0::(int -3);;ctor:0:rparam:0::(var 1)"
                          ],
                          "\t"
                        )

  test "the ω erasure quantity :many is an interned known atom" do
    assert :many in Challenge.__known_atoms__()
  end

  test "a many-quantity family record decodes (no unminted-atom crash)" do
    assert {:ok, %Challenge{}} = Corpus.decode_record(@many_quantity_record)
  end
end
