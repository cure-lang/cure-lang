defmodule Cure.Protocol.ParserTest do
  use ExUnit.Case, async: true

  alias Cure.Protocol.Parser
  alias Cure.Protocol.Script

  describe "parse/1" do
    test "parses a minimal Ping/Pong protocol" do
      dsl = """
      protocol Ping.Pong with Client, Server
        Client -> Server: Ping
        Server -> Client: Pong
        end
      """

      assert {:ok, %Script{name: "Ping.Pong", roles: ["Client", "Server"], body: body}} =
               Parser.parse(dsl)

      assert [
               {:msg, "Client", "Server", "Ping", []},
               {:msg, "Server", "Client", "Pong", []},
               {:end_, []}
             ] = body
    end

    test "captures message args in parentheses" do
      dsl = """
      protocol Echo with A, B
        A -> B: Say(String, Int)
        B -> A: Ack
        end
      """

      assert {:ok, %Script{body: body}} = Parser.parse(dsl)
      assert [{:msg, "A", "B", "Say", ["String", "Int"]}, _, _] = body
    end

    test "supports `loop` as top-level body sealer" do
      dsl = """
      protocol Ping.Pong with Client, Server
        Client -> Server: Ping
        Server -> Client: Pong
        loop
      """

      assert {:ok, %Script{body: body}} = Parser.parse(dsl)
      assert [{:loop, _}] = body
    end

    test "strips comments (#) at end of line" do
      dsl = """
      protocol X with A, B # trailing comment
        A -> B: Ping  # another comment
        end
      """

      assert {:ok, %Script{name: "X"}} = Parser.parse(dsl)
    end

    test "rejects a header without at least two roles" do
      assert {:error, _} = Parser.parse("protocol Bad with Solo\n  end")
    end

    test "rejects a malformed step" do
      dsl = """
      protocol Bad with A, B
        this is not a step
      """

      assert {:error, {:bad_step, _}} = Parser.parse(dsl)
    end
  end
end

defmodule Cure.Protocol.VerifierTest do
  use ExUnit.Case, async: true

  alias Cure.Protocol

  describe "verify/1" do
    test "accepts a well-formed protocol" do
      {:ok, script} =
        Protocol.parse("""
        protocol Ping.Pong with Client, Server
          Client -> Server: Ping
          Server -> Client: Pong
          end
        """)

      assert Protocol.verify(script) == :ok
    end

    test "emits PROTO001 when a declared role is never used" do
      {:ok, script} =
        Protocol.parse("""
        protocol Idle with Client, Server, Spectator
          Client -> Server: Ping
          end
        """)

      assert {:error, errors} = Protocol.verify(script)

      assert Enum.any?(errors, fn
               {:protocol_violation, msg, meta} ->
                 Keyword.get(meta, :code) == "PROTO001" and msg =~ "Spectator"

               _ ->
                 false
             end)
    end
  end

  describe "project/2 and participant_trace/2" do
    test "Client projection has send- and recv- transitions" do
      {:ok, script} =
        Protocol.parse("""
        protocol Ping.Pong with Client, Server
          Client -> Server: Ping
          Server -> Client: Pong
          end
        """)

      transitions = Protocol.project(script, "Client")
      events = Enum.map(transitions, & &1.event)

      assert Enum.any?(events, &(&1 =~ "send"))
      assert Enum.any?(events, &(&1 =~ "recv"))
    end

    test "participant_trace returns a model usable by Cure.Temporal.Checker" do
      {:ok, script} =
        Protocol.parse("""
        protocol Ping.Pong with Client, Server
          Client -> Server: Ping
          Server -> Client: Pong
          end
        """)

      model = Protocol.participant_trace(script, "Server")
      assert is_map(model)
      assert Map.has_key?(model, :initial)
      assert Map.has_key?(model, :edges)
      assert model.initial == "S0"
    end
  end
end
