# Antigen human-readable corpus — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make banked Antigen corpus records human-readable on disk — terms as tagged s-expressions, `note` as plaintext, mutant `fault` provenance as a readable field — while preserving exact round-trip replay and backward-compatibility with existing Base64 records.

**Architecture:** The readable term format already exists: `Cure.Core.Serialize.encode/decode` emits/parses the exact tagged s-expression (`(ctor vcons (app …) …)`, `(case … (branch T 0 …))`, `(type 0)`) — it is the C2 re-validation format. So there is **no new term codec**: readable pieces are `Serialize.encode(t)` with the Base64 wrapper dropped, and decode is `Serialize.decode/1`. All changes live in `lib/antigen/corpus.ex` (plus a one-time migration Mix task). `Antigen.Challenge` is **untouched** — the mutant `fault` is relocated purely at the Corpus layer (pop out of the scaffold on encode; merge back into the scaffold on decode), so `to_pieces`/`from_pieces` see `scaffold["fault"]` unchanged.

**Tech Stack:** Elixir; ExUnit; `Cure.Core.Serialize` (existing s-expr codec); `Antigen.Corpus`.

## Global Constraints

- **Ghost-authored commits:** every commit uses `--author="Made In Heaven <madeinheaven@madeinheaven.com>"` and **no** `Co-Authored-By` trailer.
- **Test env:** `MIX_ENV=test mix test …` (dev env crashes). macOS has no `timeout`. `elixir` does not read stdin via `-`; use a script file.
- **One build/test run at a time** — never launch concurrent suites.
- **Reuse `Serialize`, do not fork it.** No new `Antigen.SExpr` module (spec §3.0). Term pieces encode with `Serialize.encode/1`, decode with `Serialize.decode/1` (which returns `{:ok, term} | {:error, _}` and mints atoms via `String.to_atom` — this is the pre-existing posture; not a regression).
- **`Challenge` is not modified.** All format work is in `lib/antigen/corpus.ex`.
- **Backward-compatible:** a record is wholly-legacy (Base64 pieces + Base64 note + fault-in-scaffold) or wholly-new (s-expr pieces + plaintext note + `fault=` field). Decode infers the record's format from its **pieces** (`(`-prefix ⇒ new; else legacy) and reads note/fault to match. Base64's alphabet (`A–Za–z0–9+/=`) never starts with `(`, and every `Serialize.encode` output starts with `(`, so this is unambiguous.
- **Dedup-key stability:** `dedup_key(_, :antibody)` uses `Serialize.encode` (binary) and the `key=` field stores it Base64 — both independent of display format. Migration preserves the byte-exact stored key. Do not change `dedup_key/2`, `seen?/2`, or `extract_key/1`.
- **Tests are set in stone.** Once a Step-1 red test is committed to the test file, the only legitimate way to make it green is to change `lib/antigen/corpus.ex` / `lib/mix/tasks/antigen.migrate.ex` — never weaken, skip, or delete the test to force a pass. The sole exception is a test that is itself proven wrong (state why before touching it); "the test is failing and editing it is the fastest path to green" is never a valid reason.

---

## Task 1: Readable term pieces (drop Base64) + dual-read

**Files:**
- Modify: `lib/antigen/corpus.ex` (`encode_record/2` pieces; `decode_pieces/1`)
- Test: `test/antigen/corpus_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Serialize.encode/1 :: binary`, `Serialize.decode/1 :: {:ok, term} | {:error, _}` (already aliased in corpus.ex).
- Produces: pieces stored as `id::(sexpr)`; `decode_pieces/1` reads both `id::(sexpr)` and legacy `id::<base64>`.

- [ ] **Step 1: Write the failing tests**

```elixir
# append to test/antigen/corpus_test.exs
  alias Cure.Core.Serialize

  test "term pieces are stored as readable s-expressions, not Base64" do
    c =
      Challenge.new(
        kind: :stub, assay: "stub", label: :none,
        payload: %{term: {:ctor, :vcons, [{:ctor, :Z, []}, {:ctor, :Z, []}, {:ctor, :vnil, []}]}},
        seed: 7, note: "n"
      )

    line = Corpus.encode_record(c)
    # the piece is the literal Serialize s-expr, inline in the line
    assert line =~ "term::(ctor vcons (ctor Z) (ctor Z) (ctor vnil))"
    refute line =~ "term::" <> Base.encode64(Serialize.encode(c.payload.term))
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.term == c.payload.term
  end

  test "decode_record still reads a legacy Base64 piece (dual-read)" do
    term = {:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}}
    # hand-build a legacy record: pieces = id::Base64(Serialize.encode(term))
    legacy =
      Enum.join(
        [
          "antigen-record", "kind=stub", "assay=stub", "label=none", "seed=1",
          "note=aGk=", "scaffold=-", "key=" <> Base.encode64("k"),
          "pieces=term::" <> Base.encode64(Serialize.encode(term))
        ],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.payload.term == term
  end
```

- [ ] **Step 2: Run — expect FAIL**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: the first test FAILS (pieces currently Base64, so the `=~` on the inline s-expr fails); the second may pass already (legacy path is the current path) — that is fine, it is a regression guard.

- [ ] **Step 3: Implement**

In `lib/antigen/corpus.ex`, change the piece encoder in `encode_record/2`. Replace:

```elixir
    piece_str =
      pieces
      |> Enum.map(fn {id, t} -> "#{id}::#{Base.encode64(Serialize.encode(t))}" end)
      |> Enum.join(";;")
```

with:

```elixir
    piece_str =
      pieces
      |> Enum.map(fn {id, t} -> "#{id}::#{Serialize.encode(t)}" end)
      |> Enum.join(";;")
```

Then make `decode_pieces/1` dual-read per piece. Replace the `case String.split(piece, "::", parts: 2)` body:

```elixir
      case String.split(piece, "::", parts: 2) do
        [id, b64] ->
          case Serialize.decode(Base.decode64!(b64)) do
            {:ok, t} -> {:cont, {:ok, [{id, t} | acc]}}
            err -> {:halt, err}
          end

        _ ->
          {:halt, {:error, {:bad_piece, piece}}}
      end
```

with:

```elixir
      case String.split(piece, "::", parts: 2) do
        [id, body] ->
          decoded =
            case body do
              "(" <> _ -> Serialize.decode(body)                       # new: inline s-expr
              _ -> Serialize.decode(Base.decode64!(body))              # legacy: Base64-wrapped
            end

          case decoded do
            {:ok, t} -> {:cont, {:ok, [{id, t} | acc]}}
            err -> {:halt, err}
          end

        _ ->
          {:halt, {:error, {:bad_piece, piece}}}
      end
```

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/corpus.ex test/antigen/corpus_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): store corpus term pieces as readable s-expressions (dual-read legacy)"
```

---

## Task 2: Plaintext note (format-gated dual-read)

**Files:**
- Modify: `lib/antigen/corpus.ex` (`encode_record/2` note; `decode_record/1` note; add `enc_note/1`, `dec_note/1`, `legacy_record?/1`; keep the old `dec_opt/1` for the legacy branch)
- Test: `test/antigen/corpus_test.exs`

**Interfaces:**
- Produces: notes stored as escaped plaintext (`nil` → `-`); `decode_record/1` recovers the note for both new (plaintext) and legacy (Base64) records, choosing by record format.
- Consumes: `legacy_record?/1` (added here) — `true` iff the record's first piece body does not start with `(` (i.e. Base64 pieces). Used to gate note (and, in Task 3, fault) decoding so a record is read wholly in one format.

- [ ] **Step 1: Write the failing tests**

```elixir
# append to test/antigen/corpus_test.exs
  test "note is stored as readable plaintext and round-trips special chars" do
    for note <- ["negative occurrence: Bad left of an arrow", "has\ttab and % and\nnewline", "-", "plain", nil] do
      c = Challenge.new(kind: :stub, assay: "stub", label: :none,
                        payload: %{term: {:type, 0}}, seed: 1, note: note)
      line = Corpus.encode_record(c)
      refute String.contains?(line, "\n"), "record must stay one line for note=#{inspect(note)}"
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.note == note
    end
  end

  test "a real (non-nil) note is human-readable in the line (not Base64)" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none,
                      payload: %{term: {:type, 0}}, seed: 1, note: "negative occurrence")
    line = Corpus.encode_record(c)
    assert line =~ "note=negative occurrence"
    refute line =~ "note=" <> Base.encode64("negative occurrence")
  end

  test "legacy Base64 note decodes to the original text (format inferred from Base64 pieces)" do
    term = {:type, 0}
    legacy =
      Enum.join(
        ["antigen-record", "kind=stub", "assay=stub", "label=none", "seed=1",
         "note=" <> Base.encode64("hello world"), "scaffold=-", "key=" <> Base.encode64("k"),
         "pieces=term::" <> Base.encode64(Serialize.encode(term))],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.note == "hello world"
    assert c.payload.term == term
  end
```

- [ ] **Step 2: Run — expect FAIL**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: the special-chars test FAILS (`\t`/`\n`/`%` note currently Base64-encoded via `enc_opt`, so either the record breaks across a tab/newline or the readability assertion fails); the readability test FAILS (note is Base64 today).

- [ ] **Step 3: Implement**

In `encode_record/2`, change `"note=#{enc_opt(c.note)}"` to `"note=#{enc_note(c.note)}"`.

In `decode_record/1`, the note is decoded from `m["note"]`. Change the `from_pieces` call site so the note is format-gated. Locate:

```elixir
      {:ok, Challenge.from_pieces(kind, m["assay"], label, seed, dec_opt(m["note"]), scaffold, pieces)}
```

Replace with (compute `legacy?` once from the raw pieces string, before the note/scaffold decode — note it must be computed from `m["pieces"]`, available in scope):

```elixir
      note = if legacy_record?(m["pieces"]), do: dec_opt(m["note"]), else: dec_note(m["note"])
      {:ok, Challenge.from_pieces(kind, m["assay"], label, seed, note, scaffold, pieces)}
```

Add the helpers near `enc_opt`/`dec_opt` (keep `dec_opt/1` for the legacy branch; `enc_opt/1` may become unused — that is fine, or delete it if the compiler warns):

```elixir
  # A record is legacy iff its (first) piece body is Base64, i.e. does not start
  # with "(" — every Serialize.encode output starts with "(", Base64 never does.
  # Empty/absent pieces ⇒ treat as new-format (plaintext note); real records
  # always carry ≥1 term piece, so this default is not exercised by live data.
  defp legacy_record?(nil), do: false
  defp legacy_record?(""), do: false
  defp legacy_record?(pieces_str) do
    case String.split(pieces_str, ";;", parts: 2) do
      [first | _] ->
        case String.split(first, "::", parts: 2) do
          [_id, "(" <> _] -> false
          [_id, _body] -> true
          _ -> false
        end
    end
  end

  # note: nil -> "-"; a literal "-" -> "%2D"; else percent-escape %/tab/newline.
  # `%` MUST be escaped first (its own escape introduces further `%`).
  defp enc_note(nil), do: "-"
  defp enc_note("-"), do: "%2D"
  defp enc_note(s) do
    s
    |> String.replace("%", "%25")
    |> String.replace("\t", "%09")
    |> String.replace("\n", "%0A")
  end

  defp dec_note("-"), do: nil
  defp dec_note(s) do
    s
    |> String.replace("%2D", "-")
    |> String.replace("%09", "\t")
    |> String.replace("%0A", "\n")
    |> String.replace("%25", "%")
  end
```

Note the unescape order mirrors the escape order's inverse: `%25` (the `%` escape) is unescaped **last**, so a real `"%09"` inside a note (escaped to `"%2509"`) round-trips (→ `%09` after `%25`→`%` last, not mis-read as a tab). Verify this ordering with the special-chars test.

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: PASS. If a `%`-containing note fails, re-check the unescape order (must be `%2D`,`%09`,`%0A` before `%25`).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/corpus.ex test/antigen/corpus_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): store corpus note as readable plaintext (format-gated legacy decode)"
```

---

## Task 3: Readable `fault` provenance field

**Files:**
- Modify: `lib/antigen/corpus.ex` (`encode_record/2` fault split; `decode_record/1` fault merge; add `encode_fault/1`, `decode_fault/1`, and a tiny s-expr reader `read_sexp/1`)
- Test: `test/antigen/corpus_test.exs`

**Interfaces:**
- Produces: for a record whose scaffold contains a non-nil `"fault"`, a dedicated `fault=<assoc-sexpr>` field; the fault is removed from the Base64 scaffold. `decode_record/1` re-merges `scaffold["fault"]` so `Challenge.from_pieces` is unchanged.
- Fault value grammar (verified against `Generators.Mutation.build/2` + `Generators.Conversion.conv_reject/0`): each entry `(key value)`, keys sorted alphabetically; `value` is one of — bare atom name, integer, `nil`, `(pair <int> <int>)` (only `scope` for `:out_of_scope_var`), `(list <name>…)` (only `wrap_path`), `(term <serialize-sexpr>)` (only `expected_head`/`injected_head` for `:universe`, holding e.g. `{:type,0}`).

- [ ] **Step 1: Write the failing tests**

```elixir
# append to test/antigen/corpus_test.exs — a helper to build a mutant_term challenge with a given fault
  defp mutant(fault, term \\ {:ctor, :Z, []}) do
    Challenge.new(
      kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: {:type, 0}, term: term, fault: fault}
    )
  end

  test "mutant fault round-trips every value shape and is readable in the line" do
    faults = [
      # atom/integer/nil/list (head_swap + deepen)
      %{kind: :head_swap, witness: :head, expected_head: :Nat, injected_head: :Vec,
        scope: nil, depth: 3, wrap_path: [:app_arg, :case_branch]},
      # integer-pair scope (out_of_scope_var)
      %{kind: :out_of_scope_var, witness: :scope, expected_head: nil,
        injected_head: nil, scope: {2, 2}, depth: 0, wrap_path: []},
      # Core-term head values (universe)
      %{kind: :universe, witness: :level, expected_head: {:type, 0},
        injected_head: {:type, 1}, scope: nil, depth: 1, wrap_path: [:pair]},
      # conversion carrier fault (integers + atoms)
      %{kind: :conv_index, witness: :conv, expected_index: 2, actual_index: 3,
        reduction: :required, depth: 2, carrier: :conv_index}
    ]

    for f <- faults do
      line = Corpus.encode_record(mutant(f))
      refute String.contains?(line, "\n")
      assert line =~ "fault=((", "fault must be an inline assoc-sexpr for #{inspect(f)}"
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.payload.fault == f, "fault mismatch for #{inspect(f)}"
    end
  end

  test "non-mutant records carry no fault= field" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none,
                      payload: %{term: {:type, 0}}, seed: 1, note: "n")
    refute Corpus.encode_record(c) =~ "\tfault="
  end

  test "legacy fault-in-scaffold still decodes (dual-read)" do
    # a legacy mutant: Base64 pieces + fault inside the Base64 scaffold, no fault= field
    fault = %{kind: :head_swap, witness: :head, expected_head: :Nat,
              injected_head: :Vec, scope: nil, depth: 0, wrap_path: []}
    scaffold = %{"sig" => "v1", "ctx_len" => 0, "fault" => fault}
    legacy =
      Enum.join(
        ["antigen-record", "kind=mutant_term", "assay=mutation/rejection", "label=ill_typed",
         "seed=1", "note=-", "scaffold=" <> Corpus.encode_scaffold(scaffold),
         "key=" <> Base.encode64("k"),
         "pieces=type::" <> Base.encode64(Serialize.encode({:type, 0})) <>
           ";;term::" <> Base.encode64(Serialize.encode({:ctor, :Z, []}))],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.payload.fault == fault
  end
```

- [ ] **Step 2: Run — expect FAIL**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: the round-trip test FAILS (fault is currently inside the Base64 scaffold; no `fault=` field, no readable assoc-sexpr).

- [ ] **Step 3: Implement**

In `encode_record/2`, split the fault out of the scaffold and emit a field. Locate the current field list build:

```elixir
    Enum.join(
      [
        @marker,
        "kind=#{c.kind}",
        "assay=#{c.assay}",
        "label=#{c.label}",
        "seed=#{c.seed || "-"}",
        "note=#{enc_note(c.note)}",
        "scaffold=#{encode_scaffold(scaffold)}",
        "key=#{Base.encode64(key)}",
        "pieces=#{piece_str}"
      ],
      "\t"
    )
```

Replace with (pop fault before Base64-ing the scaffold; conditionally include the `fault=` field):

```elixir
    {fault, scaffold_rest} = Map.pop(scaffold, "fault")

    fault_field = if is_map(fault), do: ["fault=#{encode_fault(fault)}"], else: []

    Enum.join(
      [
        @marker,
        "kind=#{c.kind}",
        "assay=#{c.assay}",
        "label=#{c.label}",
        "seed=#{c.seed || "-"}",
        "note=#{enc_note(c.note)}",
        "scaffold=#{encode_scaffold(scaffold_rest)}"
      ] ++ fault_field ++ [
        "key=#{Base.encode64(key)}",
        "pieces=#{piece_str}"
      ],
      "\t"
    )
```

In `decode_record/1`, after building `scaffold`, merge the fault field back. Locate:

```elixir
      scaffold = decode_scaffold(m["scaffold"] || "-")
      note = if legacy_record?(m["pieces"]), do: dec_opt(m["note"]), else: dec_note(m["note"])
      {:ok, Challenge.from_pieces(kind, m["assay"], label, seed, note, scaffold, pieces)}
```

Replace with:

```elixir
      base_scaffold = decode_scaffold(m["scaffold"] || "-")

      scaffold =
        case m["fault"] do
          nil -> base_scaffold                            # legacy: fault (if any) already in scaffold
          f_str -> Map.put(base_scaffold, "fault", decode_fault(f_str))
        end

      note = if legacy_record?(m["pieces"]), do: dec_opt(m["note"]), else: dec_note(m["note"])
      {:ok, Challenge.from_pieces(kind, m["assay"], label, seed, note, scaffold, pieces)}
```

Add the fault codec + a tiny s-expr reader as private helpers:

```elixir
  # ── fault provenance codec (readable assoc-sexpr) ────────────────────────────
  # Encodes a flat fault map as `((key val)…)`, keys sorted for determinism.
  # Values: atom->name, int->digits, nil->"nil", {i,i}->"(pair i i)",
  # [atoms]->"(list a b …)", Core-term tuple->"(term <serialize>)".
  defp encode_fault(map) do
    body =
      map
      |> Enum.sort_by(fn {k, _} -> Atom.to_string(k) end)
      |> Enum.map(fn {k, v} -> "(#{k} #{enc_fault_val(v)})" end)
      |> Enum.join(" ")

    "(" <> body <> ")"
  end

  defp enc_fault_val(nil), do: "nil"
  defp enc_fault_val(v) when is_integer(v), do: Integer.to_string(v)
  defp enc_fault_val({a, b}) when is_integer(a) and is_integer(b), do: "(pair #{a} #{b})"
  defp enc_fault_val(v) when is_atom(v), do: Atom.to_string(v)
  defp enc_fault_val(v) when is_list(v),
    do: "(list " <> Enum.map_join(v, " ", &Atom.to_string/1) <> ")"

  defp enc_fault_val(v) when is_tuple(v) do
    if Cure.Core.Term.term?(v),
      do: "(term " <> Serialize.encode(v) <> ")",
      else: raise(ArgumentError, "unencodable fault value: #{inspect(v)}")
  end

  # decode_fault: parse the assoc-sexpr back into the flat map.
  defp decode_fault(str) do
    {sexp, _rest} = read_sexp(str)  # sexp = list of [key | value-tokens] groups

    sexp
    |> Enum.map(fn [k | vtoks] -> {String.to_atom(k), dec_fault_val(vtoks)} end)
    |> Map.new()
  end

  # a value is a single token (atom/int/"nil") or a nested group [tag | rest]
  defp dec_fault_val(["nil"]), do: nil
  defp dec_fault_val([tok]) when is_binary(tok) do
    case Integer.parse(tok) do
      {n, ""} -> n
      _ -> String.to_atom(tok)
    end
  end
  defp dec_fault_val([["pair", a, b]]), do: {String.to_integer(a), String.to_integer(b)}
  defp dec_fault_val([["list" | elems]]), do: Enum.map(elems, &String.to_atom/1)
  # a "(term X)" group parses to ["term", X] where X is the single nested term
  # s-expr (itself a token list). Re-serialize X (NOT the wrapping list) so
  # Serialize.decode rebuilds it.
  defp dec_fault_val([["term", term_sexp]]) do
    {:ok, t} = Serialize.decode(reassemble_tok(term_sexp))
    t
  end

  # ── minimal s-expr reader: string -> {[group|token], rest} ───────────────────
  # tokens are bare words (binaries); a "(" opens a nested list. Returns the
  # top-level list's children. Used only for the small, trusted fault field.
  defp read_sexp("(" <> rest), do: read_list(String.trim_leading(rest), [])
  defp read_list(")" <> rest, acc), do: {Enum.reverse(acc), rest}
  defp read_list("(" <> _ = s, acc) do
    {child, rest} = read_sexp(s)
    read_list(String.trim_leading(rest), [child | acc])
  end
  defp read_list(s, acc) do
    {word, rest} = read_word(s, [])
    read_list(String.trim_leading(rest), [word | acc])
  end

  defp read_word(<<c, _::binary>> = s, acc) when c in [?\s, ?(, ?)],
    do: {acc |> Enum.reverse() |> List.to_string(), s}
  defp read_word(<<>>, acc), do: {acc |> Enum.reverse() |> List.to_string(), <<>>}
  defp read_word(<<c, rest::binary>>, acc), do: read_word(rest, [c | acc])

  # A "(term …)" group's nested term is itself an s-expr; `read_sexp` has already
  # parsed it into nested token lists. Re-serialize those lists back to the flat
  # Serialize string so `Serialize.decode/1` can rebuild the term.
  defp reassemble(toks), do: "(" <> Enum.map_join(toks, " ", &reassemble_tok/1) <> ")"
  defp reassemble_tok(tok) when is_binary(tok), do: tok
  defp reassemble_tok(list) when is_list(list), do: reassemble(list)
```

> **Reader note for the implementer:** `read_sexp/1` returns the *children* of the
> outermost list. `decode_fault` therefore receives `[[key, v…], [key, v…], …]`.
> A `(term …)` value re-serializes its already-parsed nested lists via
> `reassemble/1` and hands the flat string to `Serialize.decode/1`. If the deep
> composite term test (Step 1's `:universe` fault holding `{:type,0}`/`{:type,1}`)
> fails, print the intermediate `read_sexp` output and confirm the nesting shape
> matches `dec_fault_val`'s `[["term" | term_toks]]` clause.

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: PASS. Watch specifically the `:universe` (term-valued heads) and `:out_of_scope_var` (int-pair scope) cases.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/corpus.ex test/antigen/corpus_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): surface mutant fault as a readable provenance field (dual-read legacy scaffold)"
```

---

## Task 4: Migration Mix task + migrate the three committed corpora

**Files:**
- Create: `lib/mix/tasks/antigen.migrate.ex`
- Modify: `lib/antigen/corpus.ex` (add public `raw_key/1`; `extract_key/1` becomes a one-line delegate to it)
- Migrate + commit: `test/antigen/seeds.sexp`, `test/antigen/corpus.sexp`, `test/antigen/reach.sexp`
- Test: `test/antigen/corpus_test.exs`

**Interfaces:**
- Produces: `mix antigen.migrate <path>…` — rewrites each file in place from any format to new readable format, preserving the byte-exact stored dedup key and record order; idempotent (new-format input reproduces byte-identical output).
- Consumes: `Corpus.decode_record/1`, `Corpus.encode_record/2` (challenge, verbatim key), `Corpus.stream/1`. Needs the legacy `key=` bytes: expose them via a new public `Corpus.raw_key/1 :: binary` (Base64-decoded stored key of a record line) — factor it out of the existing private `extract_key/1`.

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/antigen/corpus_test.exs
  test "migration is lossless and idempotent (keys, challenges, bytes)" do
    path = Path.join(@tmp, "mig.sexp")
    # bank a heterogeneous set the legacy way: write legacy Base64 records by hand
    # via a legacy encoder is overkill — instead bank via the CURRENT encoder,
    # which already emits new format, then assert migration is a byte-identical
    # no-op (idempotency), AND that decode/key identity is preserved.
    challenges = [
      Challenge.new(kind: :stub, assay: "stub", label: :none,
                    payload: %{term: {:ctor, :S, [{:ctor, :Z, []}]}}, seed: 1, note: "one"),
      mutant(%{kind: :out_of_scope_var, witness: :scope, expected_head: nil,
               injected_head: nil, scope: {1, 1}, depth: 0, wrap_path: []})
    ]

    for c <- challenges, do: Corpus.append(path, c, Corpus.dedup_key(c, :antibody))
    before_bytes = File.read!(path)
    keys_before = corpus_keys(path)

    Mix.Tasks.Antigen.Migrate.run([path])

    after_bytes = File.read!(path)
    assert after_bytes == before_bytes, "already-new-format file must migrate byte-identically (idempotent)"
    assert corpus_keys(path) == keys_before, "dedup keys must be identical after migration"

    decoded = Corpus.stream(path) |> Enum.map(fn {:ok, c} -> c end)
    assert length(decoded) == length(challenges)
    assert Enum.at(decoded, 1).payload.fault.scope == {1, 1}
  end

  defp corpus_keys(path) do
    path |> File.stream!() |> Enum.map(&Corpus.raw_key/1) |> Enum.sort()
  end
```

- [ ] **Step 2: Run — expect FAIL**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: FAIL — `Mix.Tasks.Antigen.Migrate` and `Corpus.raw_key/1` are undefined.

- [ ] **Step 3: Implement**

First expose `raw_key/1` in `lib/antigen/corpus.ex` (refactor from `extract_key/1`, which keeps calling it):

```elixir
  @doc "The Base64-decoded stored dedup key of one record line, or nil if absent."
  @spec raw_key(String.t()) :: binary() | nil
  def raw_key(line) do
    line
    |> String.split("\t")
    |> Enum.find_value(fn f ->
      case String.split(f, "=", parts: 2) do
        ["key", b64] -> Base.decode64!(String.trim(b64))
        _ -> nil
      end
    end)
  rescue
    _ -> nil
  end

  defp extract_key(line), do: raw_key(line)
```

(Delete the old private `extract_key/1` body — it becomes the one-line delegate above.)

Then create `lib/mix/tasks/antigen.migrate.ex`:

```elixir
defmodule Mix.Tasks.Antigen.Migrate do
  use Mix.Task
  alias Antigen.Corpus

  @shortdoc "Rewrite banked Antigen corpora into the human-readable format (idempotent)."
  @moduledoc """
  Rewrites each given `.sexp` corpus file in place from any format (legacy Base64
  or already-new) into the readable format — s-expr term pieces, plaintext note,
  readable `fault=` field — preserving the byte-exact stored dedup key and record
  order. Idempotent: a new-format file re-migrates to byte-identical output.

      mix antigen.migrate test/antigen/seeds.sexp test/antigen/corpus.sexp test/antigen/reach.sexp
  """

  @impl true
  def run(paths) do
    Enum.each(paths, &migrate_file/1)
  end

  defp migrate_file(path) do
    lines = path |> File.stream!() |> Enum.to_list()

    out =
      lines
      |> Enum.map(fn line ->
        trimmed = String.trim_trailing(line, "\n")

        case Corpus.decode_record(trimmed) do
          {:ok, c} -> Corpus.encode_record(c, Corpus.raw_key(trimmed))
          _ -> trimmed                      # leave undecodable lines (e.g. blank) untouched
        end
      end)

    tmp = path <> ".migrating"
    File.write!(tmp, Enum.map_join(out, "\n", & &1) <> "\n")
    File.rename!(tmp, path)
    Mix.shell().info("migrated #{path} (#{length(lines)} records)")
  end
end
```

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: PASS.

- [ ] **Step 5: Migrate the three committed corpora + verify replay**

```bash
MIX_ENV=test mix antigen.migrate test/antigen/seeds.sexp test/antigen/corpus.sexp test/antigen/reach.sexp
```

Then confirm every static-replay test that reads these files still passes (dual-read + dedup-key stability mean they must):

```bash
MIX_ENV=test mix test test/antigen/corpus_replay_test.exs test/antigen/indexed_seed_test.exs \
  test/antigen/positivity_seed_test.exs test/antigen/totality_seed_test.exs \
  test/antigen/universes_seed_test.exs test/antigen/reach_pin_test.exs \
  test/antigen/rewrite_seed_test.exs test/antigen/typed_term_seed_test.exs
```

Expected: PASS. Eyeball `git diff --stat test/antigen/*.sexp` — the three files should be rewritten; open `test/antigen/seeds.sexp` and confirm terms now read as `(ctor …)`, notes are plaintext, and mutant records carry a readable `fault=`.

- [ ] **Step 6: Commit**

```bash
git add lib/mix/tasks/antigen.migrate.ex lib/antigen/corpus.ex test/antigen/corpus_test.exs \
  test/antigen/seeds.sexp test/antigen/corpus.sexp test/antigen/reach.sexp
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): antigen.migrate task + migrate committed corpora to readable format"
```

---

## Task 5: Readability smoke + quarantine guard

**Files:**
- Test: `test/antigen/corpus_test.exs`

**Interfaces:** consumes only public `Corpus` + the migrated `test/antigen/seeds.sexp`.

- [ ] **Step 1: Write the test**

```elixir
# append to test/antigen/corpus_test.exs
  @looks_base64 ~r/\A[A-Za-z0-9+\/]{16,}={0,2}\z/

  test "a banked mutant record in seeds.sexp is fully human-readable" do
    seeds = "test/antigen/seeds.sexp"
    line =
      seeds
      |> File.stream!()
      |> Enum.find(fn l -> String.contains?(l, "kind=mutant_term") end)

    assert line, "expected at least one mutant_term in #{seeds}"
    # drop the leading "antigen-record" marker (no `=`) before building the map —
    # `Map.new`/`:maps.from_list` cannot mix its 1-tuple with the other fields' 2-tuples
    fields = line |> String.trim_trailing("\n") |> String.split("\t") |> tl()
    m = Map.new(fields, fn f -> List.to_tuple(String.split(f, "=", parts: 2)) end)

    # readable, not Base64, in the three human-facing fields
    assert m["pieces"] =~ "(", "pieces must be s-expr"
    refute Regex.match?(@looks_base64, m["note"] || "-")
    assert m["fault"] =~ "((", "mutant must carry a readable fault field"
    refute Regex.match?(@looks_base64, m["fault"])
    # and it still decodes
    assert {:ok, c} = Corpus.decode_record(line)
    assert c.kind == :mutant_term
  end
```

- [ ] **Step 2: Run — expect PASS** (Tasks 1–4 already deliver the behavior; this is the end-to-end evidence)

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: PASS. If `seeds.sexp` happens to contain no `mutant_term` seed, bank one first via `MIX_ENV=test mix antigen --count 300 --seeds test/antigen/seeds.sexp --corpus tmp/x.sexp` (mutants are banked as seeds) then re-run migration on `seeds.sexp` and this test — but first check: the committed `seeds.sexp` already contains mutant_term records (the mutation-corpus work banked them), so this fallback should be unnecessary.

- [ ] **Step 3: Quarantine check**

Run: `MIX_ENV=test mix test test/antigen/architecture_test.exs`
Expected: PASS. (No new module lives under `generators/`/`assays/`; the fault reader is in `corpus.ex`, so the `StreamData`-literal quarantine is unaffected.)

- [ ] **Step 4: Commit**

```bash
git add test/antigen/corpus_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): end-to-end readability smoke over migrated seeds.sexp"
```

---

## Self-Review

**Spec coverage:**
- §2.1 readable pieces → Task 1. §2.2 plaintext note → Task 2. §2.3 readable fault → Task 3. §2.4 unchanged fields (key stays Base64) → preserved (Global Constraints; `key=` untouched).
- §3.0 reuse Serialize (no SExpr module) → Global Constraints + Task 1. §3.4 fault value shapes (int-pair, term, list) → Task 3 codec + tests.
- §4.1/4.2 encode/decode + dual-read → Tasks 1–3. §4.3 dedup-key stability → Global Constraints, exercised by Task 4 idempotency + Task 5.
- §5 Challenge untouched → held across all tasks (only `corpus.ex` + the migrate task change production code).
- §6 migration (all three files) → Task 4. §6.1 note "-" edge → Task 2 (`enc_note("-")→"%2D"`, tested).
- §7 tests: 1 (former round-trip) covered by Serialize's own suite (Global Constraints); 3 (record round-trip incl. `:out_of_scope_var`/`:universe`) → Task 3; 4 (dual-read legacy) → Tasks 1–3 legacy tests; 5 (migration lossless/idempotent) → Task 4; 6 (readability smoke) → Task 5; 7 (full suite) → Stage 5. Test 2 (atom-safety) removed per §3.0 (moot).

**Placeholder scan:** none — every step has concrete code/commands.

**Type consistency:** `legacy_record?/1` (Task 2) is reused conceptually by Task 3's fault path only through the shared record; fault decoding is gated by the presence of the `fault=` field (`m["fault"]`), not `legacy_record?` — consistent because a new-format mutant always has `fault=` and a legacy mutant never does. `raw_key/1` (Task 4) is public; `extract_key/1` delegates to it. `encode_record/2`, `decode_record/1`, `encode_scaffold/1`, `dedup_key/2`, `raw_key/1` are the only public `Corpus` functions touched; `encode_scaffold/1` is already public (used by Task 3's legacy test).

**Deviation from spec (recorded):** the spec's original §3 (new `Antigen.SExpr` module with `to_existing_atom`) is superseded by §3.0 (reuse `Serialize`, which mints). This removes the `:boom`/`@known_atoms` audit the Stage-1 review demanded — that finding only applied to a new safe decoder and is moot under Serialize reuse. The known limitation (hand-edit typos mint rather than error) is documented in §3.0 and will be surfaced in the completion report.

A second, smaller deviation (not previously recorded): spec §3.4 specifies a **key-specific** decode rule for `:out_of_scope_var`'s `scope` — print as a bare paren-pair `(scope (5 5))`, decoded only because `decode_fault` is hard-coded to know the `scope` key holds a 2-tuple. Task 3's `encode_fault`/`decode_fault` instead dispatch by **value shape**: any 2-tuple of integers (regardless of key) encodes as `(pair N N)` and decodes back to a 2-tuple via the `["pair", a, b]` token pattern — no key-specific knowledge needed. This is a deliberate improvement (removes the exact fragility spec §3.4 calls out — "a schema fact, not something `decode_fault` can infer from the printed form alone" — by making the value shape self-describing instead), verified round-trip-correct for the `:out_of_scope_var` fixture (`scope: {2, 2}` → `(scope (pair 2 2))` → `{2, 2}`). It is accepted as an intentional deviation, not a defect; the printed form differs cosmetically from the spec's example but the round-trip contract (§7 test 3) is unaffected.
