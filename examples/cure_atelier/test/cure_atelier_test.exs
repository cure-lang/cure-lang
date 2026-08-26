defmodule CureAtelierTest do
  use ExUnit.Case, async: false

  # ----------------------------------------------------------------------
  # v0.27.0 showcase -- each describe block exercises one feature.
  # ----------------------------------------------------------------------

  alias Cure.OTel
  alias Cure.OTel.MemoryExporter
  alias Cure.Protocol
  alias Cure.Temporal.{Checker, Parser}
  alias Cure.Types.Synth
  alias Cure.Term.Hyperlink

  setup do
    OTel.stop()
    MemoryExporter.reset()
    OTel.clear_ctx()

    on_exit(fn ->
      OTel.stop()
      MemoryExporter.reset()
    end)

    :ok
  end

  describe "Std.CRDT.ORSet concurrent tag set" do
    test "painter and curator can add/remove tags without coordination" do
      painter_set =
        :cure_std_crdt.or_empty()
        |> :cure_std_crdt.or_add(:painter, 1, :abstract)
        |> :cure_std_crdt.or_add(:painter, 2, :cubism)

      curator_set =
        :cure_std_crdt.or_empty()
        |> :cure_std_crdt.or_add(:curator, 1, :abstract)
        |> :cure_std_crdt.or_add(:curator, 2, :impressionism)

      merged = :cure_std_crdt.or_merge(painter_set, curator_set)

      assert Enum.sort(:cure_std_crdt.or_value(merged)) ==
               [:abstract, :cubism, :impressionism]
    end
  end

  describe "Std.Time timestamps" do
    test "parse -> format round-trips a UTC instant" do
      {:ok, inst} = :cure_std_time.parse_iso8601("2026-05-01T09:00:00Z")
      assert :cure_std_time.format_iso8601(inst) == "2026-05-01T09:00:00Z"
    end

    test "diff/add arithmetic matches intuition" do
      {:ok, a} = :cure_std_time.parse_iso8601("2026-05-01T09:00:00Z")
      {:ok, b} = :cure_std_time.parse_iso8601("2026-05-01T09:05:00Z")
      d = :cure_std_time.diff(b, a)
      assert {:Duration, 300_000_000} = d

      back = :cure_std_time.add(a, d)
      assert back == b
    end
  end

  describe "Std.Regex title validation" do
    test "the Curator runs its compile-time typed title pattern" do
      assert :"Cure.Main.Curator".valid_title(~c"Starry Night (1889)")
      refute :"Cure.Main.Curator".valid_title(~c"starry night (1889)")
    end

    test "the title pattern requires a four-digit parenthesized year" do
      refute :"Cure.Main.Curator".valid_title(~c"Starry Night (89)")
      refute :"Cure.Main.Curator".valid_title(~c"Starry Night 1889")
    end
  end

  describe "Cure.Protocol session types (PROTO001 matrix)" do
    @gallery """
    protocol Atelier.Gallery with Painter, Curator
      Painter -> Curator: SubmitPiece(String)
      Curator -> Painter: Accept
      end
    """

    test "happy-path protocol verifies cleanly" do
      assert {:ok, _script} = Protocol.parse_and_verify(@gallery)
    end

    test "dead role surfaces PROTO001" do
      dead = """
      protocol Atelier.Gallery with Painter, Curator, Spectator
        Painter -> Curator: SubmitPiece
        Curator -> Painter: Accept
        end
      """

      assert {:error, errors} = Protocol.parse_and_verify(dead)

      assert Enum.any?(errors, fn
               {:protocol_violation, msg, meta} ->
                 Keyword.get(meta, :code) == "PROTO001" and msg =~ "Spectator"

               _ ->
                 false
             end)
    end

    test "projection onto Painter emits send + recv transitions" do
      {:ok, script} = Protocol.parse(@gallery)
      transitions = Protocol.project(script, "Painter")
      events = Enum.map(transitions, & &1.event)

      assert Enum.any?(events, &(&1 =~ "send"))
      assert Enum.any?(events, &(&1 =~ "recv"))
    end
  end

  describe "Cure.Temporal over the Exhibit FSM" do
    # Exhibit states: Closed -> Open -> Closed (loops forever).
    defp exhibit_model do
      Checker.from_fsm(
        [
          %{from: "Closed", to: "Open"},
          %{from: "Open", to: "Closed"}
        ],
        "Closed"
      )
    end

    test "always eventually Open holds" do
      {:ok, f} = Parser.parse_one("always eventually Open")
      assert {:ok, :holds} = Checker.check(f, exhibit_model())
    end

    test "safety property 'never Open' fails with a counterexample" do
      {:ok, f} = Parser.parse_one("never Open")
      assert {:violation, trail} = Checker.check(f, exhibit_model())
      assert "Open" in trail
    end

    test "parser round-trips a two-property script" do
      src = """
      always eventually Open
      never (Open and Closed)
      """

      assert {:ok, props} = Parser.parse(src)
      assert length(props) == 2
    end
  end

  describe "Cure.OTel captures actor-send spans" do
    test "span/3 inside an actor send registers with the memory exporter" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1, service_name: "atelier")
      _ = :sys.get_state(OTel)

      OTel.span("cure.actor.send", %{"inbox" => "Atelier.Gallery"}, fn ->
        OTel.span("cure.fsm.transition", %{"from" => "Closed", "to" => "Open"}, fn ->
          :ok
        end)
      end)

      _ = :sys.get_state(OTel)

      spans = MemoryExporter.all()
      names = Enum.map(spans, & &1.name) |> Enum.sort()
      assert "cure.actor.send" in names
      assert "cure.fsm.transition" in names

      outer = Enum.find(spans, &(&1.name == "cure.actor.send"))
      inner = Enum.find(spans, &(&1.name == "cure.fsm.transition"))

      # Parent/child relationship is preserved across nested spans.
      assert inner.trace_id == outer.trace_id
      assert inner.parent_span_id == outer.span_id
    end
  end

  describe "Cure.Types.Synth suggests fixes for a hole" do
    test "given n : Int and a List(Int), synth finds both n and Std.List.length" do
      candidates =
        Synth.synthesise("Int", %{"n" => "Int", "xs" => "List(Int)"}, %{}, max: 10)

      # The cheapest candidate is just `n`.
      assert Enum.at(candidates, 0).expr == "n"

      # But Std.List.length appears when scoped over xs.
      assert Enum.any?(candidates, &(&1.expr =~ "Std.List.length"))
    end
  end

  describe "Cure.Term.Hyperlink rendering" do
    test "emission respects CURE_HYPERLINKS=0" do
      # Force emission off deterministically regardless of the tty.
      previous = System.get_env("CURE_HYPERLINKS")
      System.put_env("CURE_HYPERLINKS", "0")

      on_exit(fn ->
        case previous do
          nil -> System.delete_env("CURE_HYPERLINKS")
          v -> System.put_env("CURE_HYPERLINKS", v)
        end
      end)

      assert Hyperlink.file_line_link("foo.cure", 42) == "foo.cure:42"
    end
  end
end
