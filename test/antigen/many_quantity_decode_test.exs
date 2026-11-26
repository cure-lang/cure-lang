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
                            "format=2",
                            "universe=cure_universe/1/max_plus_finite_omega",
                            "kind=family",
                            "assay=universes",
                            "label=well_typed",
                            "seed=94754166",
                            "note=parameterized uniform (result param = a)",
                            "scaffold=g3QAAAAEbQAAAAVjdG9yc2wAAAABdAAAAAVtAAAACWFyZ19uYW1lc2wAAAABbQAAAAF4am0AAAAEbmFtZW0AAAACcGNtAAAACnF1YW50aXRpZXNsAAAAAW0AAAAEbWFueWptAAAACnJpZHhfY291bnRhAW0AAAAMcnBhcmFtX2NvdW50YQFqbQAAAA9mYW1faW5kZXhfbmFtZXNsAAAAAW0AAAABbmptAAAACGZhbV9uYW1lbQAAAAFQbQAAAA9mYW1fcGFyYW1fbmFtZXNsAAAAAW0AAAABYWo=",
                            "key=YW50aWdlbi8yfGN1cmVfdW5pdmVyc2UvMS9tYXhfcGx1c19maW5pdGVfb21lZ2F8YW50aWJvZHkvM3xkYTE1OTM3NjI0YTU2MGIyYjg0OTY3ZjI0YmIzMjZmNzI1MjZkMzhjZDJmODk2MzdkNjgyZjRjNzZmZjk5Y2Rj",
                            "pieces64=W1siZmFtX3NvcnQiLCIoY3VyZS1jb3JlIDIgKHR5cGUgKGZpbml0ZSAobGV2ZWwtbmYgMCkpKSkiXSxbImZhbV9wYXJhbTowIiwiKGN1cmUtY29yZSAyICh0eXBlIChmaW5pdGUgKGxldmVsLW5mIDApKSkpIl0sWyJmYW1faW5kZXg6MCIsIihjdXJlLWNvcmUgMiAoaW50LXR5cGUpKSJdLFsiY3RvcjowOmFyZzowIiwiKGN1cmUtY29yZSAyICh2YXIgMCkpIl0sWyJjdG9yOjA6cmlkeDowIiwiKGN1cmUtY29yZSAyIChpbnQgLTMpKSJdLFsiY3RvcjowOnJwYXJhbTowIiwiKGN1cmUtY29yZSAyICh2YXIgMSkpIl1d"
                          ],
                          "\t"
                        )

  test "the ω erasure quantity :many is an interned known atom" do
    assert :many in Challenge.__known_atoms__()
  end

  test "a many-quantity family record decodes (no unminted-atom crash)" do
    assert {:ok, %Challenge{}} = Corpus.decode_record(@many_quantity_record)
    paths = :code.get_path() |> Enum.reverse() |> Enum.flat_map(&["-pa", List.to_string(&1)])

    script = """
    {:ok, challenge} = Antigen.Corpus.decode_record(System.fetch_env!("ANTIGEN_MANY_RECORD"))
    true = Enum.any?(challenge.payload.ctors, fn ctor ->
      Enum.any?(ctor.quantities, &(Atom.to_string(&1) == "many"))
    end)
    """

    {diagnostics, status} =
      System.cmd(
        System.find_executable("elixir"),
        ["--erl", "+S 2:2"] ++ paths ++ ["-e", script],
        env: [{"ANTIGEN_MANY_RECORD", @many_quantity_record}],
        stderr_to_stdout: true
      )

    assert status == 0, diagnostics
  end
end
