defmodule Cure.Compiler.MacroProtocolTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroProtocol}
  alias Cure.Diagnostic.Renderer

  @steps [
    %{sender: :phone, receiver: :device, message: %{name: :hello, fields: [:name]}},
    %{sender: :device, receiver: :phone, message: %{name: :info, fields: [:model]}}
  ]

  test "builds deterministic protocol endpoints and message inventory" do
    assert {:ok, protocol} = MacroProtocol.build(:Provisioning, [:phone, :device], @steps, timeout: 10)
    assert protocol.kind == :quoted_protocol
    assert Enum.map(protocol.messages, & &1.name) == [:hello, :info]
    assert is_integer(protocol.declaration_hash)
    assert [_declaration] = protocol.declarations

    atom_steps = [%{sender: :phone, receiver: :device, message: :ping}]
    assert {:ok, %{messages: [:ping]}} = MacroProtocol.build(:Ping, [:phone, :device], atom_steps)
  end

  test "rejects malformed roles and steps" do
    assert {:error, {:protocol_role_count, 3}} = MacroProtocol.build(:P, [:a, :b, :c], @steps)

    bad = [%{sender: :phone, receiver: :phone, message: %{name: :loop}}]
    assert {:error, {:self_protocol_step, :phone}} = MacroProtocol.build(:P, [:phone, :device], bad)
  end

  test "choice branches must begin with a message from the decider" do
    choices = [
      %{decider: :phone, branches: [[%{sender: :phone, receiver: :device, message: %{name: :join}}]]}
    ]

    assert {:ok, _} = MacroProtocol.build(:P, [:phone, :device], @steps, choices: choices)

    bad_choices = [%{decider: :phone, branches: [[%{sender: :device, receiver: :phone, message: %{name: :wrong}}]]}]

    assert {:error, {:unprojectable_choice, :phone}} =
             MacroProtocol.build(:P, [:phone, :device], @steps, choices: bad_choices)
  end

  test "malformed host definitions return protocol verdicts instead of raising" do
    assert {:error, {:invalid_protocol_name, 42}} = MacroProtocol.build(42, [:a, :b], [])
    assert {:error, :invalid_protocol_roles} = MacroProtocol.build(:P, :roles, [])
    assert {:error, :invalid_protocol_steps} = MacroProtocol.build(:P, [:a, :b], :steps)
    assert {:error, :invalid_protocol_options} = MacroProtocol.build(:P, [:a, :b], [], %{})
    assert {:error, :invalid_protocol_options} = MacroProtocol.build(:P, [:a, :b], [], [42])
    assert {:error, :invalid_protocol_step} = MacroProtocol.build(:P, [:a, :b], [42])
    assert {:error, :invalid_protocol_choices} = MacroProtocol.build(:P, [:a, :b], [], choices: :choices)
    assert {:error, :invalid_protocol_choice} = MacroProtocol.build(:P, [:a, :b], [], choices: [42])
  end

  test "every protocol validation branch has dedicated terminal and LSP output" do
    reasons = protocol_failure_cases()

    Enum.each(reasons, fn {run, expected_title, expected_body, expected_hint} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "protocol.cure", "")
      output = Renderer.plain(diagnostic, registry, width: 80)
      normalized_output = String.replace(output, ~r/\s+/, " ")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_protocol_validation
      assert diagnostic.title == expected_title
      assert normalized_output =~ String.replace(expected_body, ~r/\s+/, " ")
      assert output =~ "Hint: " <> expected_hint

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
      assert lsp["message"] == expected_title <> "\n\n" <> expected_body
    end)
  end

  defp protocol_failure_cases do
    empty_step = %{sender: :client, receiver: :server}
    self_step = %{sender: :client, receiver: :client, message: :ping}
    unknown_step = %{sender: :client, receiver: :elsewhere, message: :ping}
    wrong_branch = [[%{sender: :server, receiver: :client, message: :no}]]

    [
      {fn -> MacroProtocol.build(42, [:client, :server], []) end, "Protocol name is invalid",
       "A protocol name must be an atom or text, but this definition uses `42`.",
       "Use a stable protocol name such as `Provisioning`"},
      {fn -> MacroProtocol.build(:P, :roles, []) end, "Protocol roles are malformed",
       "A protocol's roles must be written as a list containing its two endpoint names.",
       "Provide exactly two distinct atom role names"},
      {fn -> MacroProtocol.build(:P, [:a], []) end, "Protocol needs exactly two roles",
       "This two-party protocol declares 1 role, but it must declare exactly two.",
       "Keep exactly two distinct role names"},
      {fn -> MacroProtocol.build(:P, [:client, "server"], []) end, "Protocol role name is invalid",
       "Every protocol role must be an atom so generated endpoint names remain stable.",
       "Use atom role names such as `client` and `server`"},
      {fn -> MacroProtocol.build(:P, [:client, :client], []) end, "Protocol role is repeated",
       "Both endpoints have the same role name, so sends and receives cannot identify opposite parties.",
       "Give the two endpoints distinct role names"},
      {fn -> MacroProtocol.build(:P, [:client, :server], :steps) end, "Protocol steps are malformed",
       "A protocol's message flow must be a list of ordered send steps.",
       "Provide a list of steps with `sender`, `receiver`, and `message`"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [42]) end, "Protocol step is malformed",
       "Every protocol step needs both a sender and a receiver from this protocol.",
       "Provide `sender`, `receiver`, and `message` for this step"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [unknown_step]) end, "Protocol step uses an unknown role",
       "The step from `client` to `elsewhere` names an endpoint outside this protocol.",
       "Choose both endpoints from the protocol's two declared roles"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [self_step]) end, "Protocol step sends to itself",
       "The `client` endpoint is both sender and receiver in this step.",
       "Send each message from one role to the other"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [empty_step]) end, "Protocol message is missing",
       "This step has no message for its sender to transmit to its receiver.",
       "Add a message declaration to this protocol step"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [], %{}) end, "Protocol options are malformed",
       "Protocol options must be a keyword list containing optional choices and timeout settings.",
       "Use keyword options such as `choices: [...]` or `timeout: 1000`"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [], choices: :choices) end, "Protocol choices are malformed",
       "The protocol's choices must be a list of branching decisions.",
       "Provide a list of choices with `decider` and non-empty `branches`"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [], choices: [42]) end, "Protocol choice is malformed",
       "Every protocol choice needs the role that decides it and its possible branches.",
       "Provide `decider` and a non-empty `branches` list"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [], choices: [%{decider: :elsewhere, branches: [[]]}]) end,
       "Protocol choice has an unknown decider",
       "The `elsewhere` role decides this choice but is not an endpoint in the protocol.",
       "Choose one of the protocol's two roles as the decider"},
      {fn -> MacroProtocol.build(:P, [:client, :server], [], choices: [%{decider: :client, branches: []}]) end,
       "Protocol choice has no valid branches",
       "The choice decided by `client` needs a non-empty list of protocol-step branches.",
       "Provide at least one branch beginning with a send from the decider"},
      {fn ->
         MacroProtocol.build(:P, [:client, :server], [], choices: [%{decider: :client, branches: wrong_branch}])
       end, "Protocol choice cannot be projected",
       "Every branch decided by `client` must begin with that role sending a message, so the other endpoint can observe the choice.",
       "Start every branch with a message sent by `client`"}
    ]
  end
end
