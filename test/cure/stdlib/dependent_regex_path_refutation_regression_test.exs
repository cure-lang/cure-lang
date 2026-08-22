defmodule Cure.Stdlib.DependentRegexPathRefutationRegressionTest do
  use ExUnit.Case, async: false

  test "recursive path refutation rejects unrelated child destination indices" do
    source = ~S'''
    mod RegexPathRefutationRegression
      use Std.Core
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn recurse(
        depth: Nat,
        n: Nat,
        machine: PatternMachine(n),
        input: List(Char),
        after_input: List(Char),
        state: ThreadState(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy,
        failure_destinations: List(MachineState(n)),
        failure: LookaroundPathFailure(depth, n, machine, input, after_input, state, history, capture_context, policy, failure_destinations, failure_destinations),
        {@erased candidates: List(MachineState(n))},
        suffix: MachineStateCursorSuffix(n, failure_destinations, candidates),
        path: LookaroundAcceptingPath(depth, n, machine, candidates, input, after_input, state, history, policy)
      ) -> Unit = ()

      fn probe(
        depth: Nat,
        n: Nat,
        machine: PatternMachine(n),
        input: List(Char),
        after_input: List(Char),
        state: ThreadState(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy,
        destinations: List(MachineState(n)),
        failure: LookaroundPathFailure(depth, n, machine, input, after_input, state, history, capture_context, policy, destinations, destinations),
        candidates: List(MachineState(n)),
        path: LookaroundAcceptingPath(depth, n, machine, candidates, input, after_input, state, history, policy)
      ) -> Unit = match failure
        LookaroundPathDestinationActiveRejected(char, rest, destination, routine, constraints, _, _, _, _, child_failure, _, _) -> match path
          LookaroundAcceptedNextActive(_, _, _, _, _, _, _, _, _, _, _, _, child_destinations, child_suffix, child_path) -> recurse(
            depth,
            n,
            machine,
            rest,
            after_input,
            ThreadActive(destination),
            history_push_bounded(history, char),
            append_routine(capture_context, routine),
            policy,
            child_destinations,
            child_failure,
            child_suffix,
            child_path
          )
          LookaroundAcceptedNow() -> ()
          LookaroundAcceptedNextAccepted(_, _, _, _, _, _, _, _, _, _, _, _, _, _) -> ()
        LookaroundPathExhausted(_, _, _, _) -> ()
        LookaroundPathStepExhausted(_, _, _, _, _, _) -> ()
        LookaroundPathAcceptedWithInput(_) -> ()
        LookaroundPathDestinationAcceptedRejected(_, _, _, _, _, _, _, _, _, _, _) -> ()
    end
    '''

    assert {:error, {:codegen_error, {:source_context, {:index_mismatch, _details}, context}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert context.checking == :probe
    assert context.expression_category == :pattern_match
  end
end
