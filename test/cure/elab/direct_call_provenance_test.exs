defmodule Cure.Elab.DirectCallProvenanceTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  test "a macro-generated call retains its invocation and definition frames in the trusted summary" do
    source = """
    mod CallProvenance
      fn id(value: Int) -> Int = value

      macro Wrapped
        syntax wrapped <value: Code> becomes id(value)

      fn run() -> Int = wrapped 42
    """

    assert {:ok, env} = Program.elaborate(source, file: "call_provenance.cure")

    assert %{calls: [call]} = Env.direct_call_summary(env, :run)
    assert call.callee == :"CallProvenance#id"
    assert call.provenance.caller == :"CallProvenance#run"
    assert is_integer(call.provenance.core_path)

    assert [%Cure.Diagnostic.ProvenanceFrame{} = frame] = call.provenance.macro_expansion
    assert frame.name == "wrapped"
    assert frame.invocation.start_line == 7
    assert frame.definition.start_line == 5
  end

  test "authored call spans are diagnostic and do not change semantic summary identity" do
    first = """
    mod AuthoredCall
      fn id(value: Int) -> Int = value
      fn run() -> Int = id(42)
    """

    moved = """
    mod AuthoredCall


      fn id(value: Int) -> Int = value
      fn run() -> Int = id(42)
    """

    assert {:ok, first_env} = Program.elaborate(first, file: "first.cure")
    assert {:ok, moved_env} = Program.elaborate(moved, file: "moved.cure")

    first_summary = Env.direct_call_summary(first_env, :run)
    moved_summary = Env.direct_call_summary(moved_env, :run)

    assert first_summary.summary_hash == moved_summary.summary_hash
    refute hd(first_summary.calls).provenance.source_span == hd(moved_summary.calls).provenance.source_span
  end
end
