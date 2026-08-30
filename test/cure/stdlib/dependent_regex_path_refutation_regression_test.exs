defmodule Cure.Stdlib.DependentRegexPathRefutationRegressionTest do
  use ExUnit.Case, async: false

  test "selected atomic transitions retain the child origin certificate" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "type AtomicPathSearchOrigin"
    assert source =~ "child_origin_canonical: AtomicPathSearchOrigin"

    assert Regex.match?(
             ~r/AtomicPathActiveChildSelectionPackageActive : [^\n]*child_selected_whole_equivalence: Equivalent\(List\(LookaroundAdmittedState\(n\)\), child_whole, child_selected_whole\)\) -> \(@erased child_origin_canonical: AtomicPathSearchOrigin/,
             source
           )

    assert source =~
             "child_selected_whole_equivalence, child_origin_canonical, _, _, _, _, _) ->\n" <>
               "      match child_selected_whole_equivalence"

    assert source =~ "AtomicPathSearchOriginActive(_, _, _, _) -> continuation"
  end

  test "cursor suffixes publish a canonical non-empty whole decomposition" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "type LookaroundAdmittedNonempty"
    assert source =~ "fn lookaround_admitted_cursor_suffix_nonempty"

    assert source =~
             "child_failure_nonempty_equivalence: Equivalent(\n" <>
               "      List(LookaroundAdmittedState(n)),\n" <>
               "      child_whole,\n" <>
               "      Cons(child_failure_head, child_failure_tail)\n" <>
               "    )"

    assert source =~
             "LookaroundAdmittedStateCursorSuffixDrop(dropped, prior) -> match lookaround_admitted_cursor_suffix_nonempty(prior)"

    assert source =~ "lookaround_admitted_state_cons_equivalent(dropped, prior_equivalence)"
  end

  test "active-child alignment rewrites through the erased non-empty package" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "type AtomicPathActiveChildAlignmentCase"
    assert source =~ "atomic_path_active_child_alignment_from_nonempty"
    assert source =~ "match failure_nonempty"
    assert source =~ "LookaroundAdmittedNonemptyPacked(_, _, equality) -> match equality"
  end

  test "active-child destination exhaustion has a construction-site consumer" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~
             "fn atomic_path_tail_active_child_destinations_exhausted_excludes_selected_suffix"

    assert source =~
             "atomic_path_active_child_destinations_exhausted_excludes_aligned_trace"
  end

  test "active-child failure dispatch keeps destination exhaustion at its construction site" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "fn atomic_path_tail_active_child_failure_dispatch"
    assert source =~ "AtomicPathDestinationsExhausted(_, _, _, _, _, _)"
    assert source =~ "atomic_path_tail_active_child_destinations_exhausted_excludes_selected_suffix"
  end

  test "active-child failure dispatch accounts for every indexed failure kind" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(source, "fn atomic_path_tail_active_child_failure_dispatch(", parts: 2)

    [body | _] = String.split(body, "\n  ##", parts: 2)

    for constructor <- [
          "AtomicPathInputExhausted(_, _)",
          "AtomicPathExactAcceptedWithInput(_, _, _, _)",
          "AtomicPathDestinationsExhausted(_, _, _, _, _, _)",
          "AtomicPathDestinationRejected("
        ] do
      assert body =~ constructor,
             "active-child dispatcher must account for #{constructor}"
    end
  end

  test "active-child selection consumer accepts a proof result directly" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(source, "fn atomic_path_active_child_selection_package_consume(", parts: 2)

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "continuation: result"
    refute body =~ "continuation: () -> result"
    assert body =~ "-> continuation"
  end

  test "active-child destination tails use the indexed failure dispatcher" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(source, "fn atomic_path_tail_active_child_destinations_exhausted_excludes_selected_suffix(",
        parts: 2
      )

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "atomic_path_tail_active_child_failure_dispatch"
    refute body =~ "atomic_path_active_child_selection_package_consume"
  end

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
        path: LookaroundAcceptingPath(depth, n, machine, capture_context, candidates, input, after_input, state, history, policy)
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
        path: LookaroundAcceptingPath(depth, n, machine, capture_context, candidates, input, after_input, state, history, policy)
      ) -> Unit = match failure
        LookaroundPathDestinationActiveRejected(_, char, child_char, child_rest, destination, routine, _, _, _, _, _, child_failure, _, _) -> match path
          LookaroundAcceptedNextActive(_, _, _, _, _, _, _, _, _, _, _, _, _, _, child_destinations, _, child_suffix, child_path) -> recurse(
            depth,
            n,
            machine,
            Cons(child_char, child_rest),
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
          LookaroundAcceptedNextAccepted(_, _, _, _, _, _, _, _, _, _, _, _) -> ()
        LookaroundPathExhausted(_, _, _, _, _, _) -> ()
        LookaroundPathStepExhausted(_, _, _, _, _, _, _, _) -> ()
        LookaroundPathAcceptedWithInput(_, _, _) -> ()
        LookaroundPathDestinationActiveRejectedEmpty(_, _, _, _, _, _, _, _, _, _, _, _) -> ()
        LookaroundPathDestinationAcceptedRejected(_, _, _, _, _, _, _, _, _, _, _, _) -> ()
    end
    '''

    assert {:error, {:codegen_error, {:source_context, {:index_mismatch, _details}, context}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert context.checking == :probe
    assert context.expression_category == :pattern_match
  end

  test "destination rejection equations are indexed by the failure state" do
    source = ~S'''
    mod RegexPathFailureStateEquationRegression
      use Std.Core
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn consume_equation(
        depth: Nat,
        n: Nat,
        machine: PatternMachine(n),
        char: Char,
        rest: List(Char),
        after_input: List(Char),
        source: Bounded(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy,
        destinations: List(MachineState(n)),
        @erased equation: Equivalent(
          List(MachineState(n)),
          destinations,
          lookaround_machine_destinations(
            depth,
            n,
            machine,
            ThreadActive(source),
            char,
            rest,
            after_input,
            history,
            capture_context,
            policy
          )
        )
      ) -> Unit = ()

      fn probe(
        depth: Nat,
        n: Nat,
        machine: PatternMachine(n),
        char: Char,
        rest: List(Char),
        after_input: List(Char),
        source: Bounded(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy,
        destinations: List(MachineState(n)),
        remaining: List(MachineState(n)),
        failure: LookaroundPathFailure(
          depth,
          n,
          machine,
          Cons(char, rest),
          after_input,
          ThreadActive(source),
          history,
          capture_context,
          policy,
          destinations,
          remaining
        )
      ) -> Unit = match failure
        LookaroundPathExhausted(_, _, _, _, _, _) -> ()
        LookaroundPathStepExhausted(_, _, _, _, _, _, _, _) -> ()
        LookaroundPathAcceptedWithInput(_, _, _) -> ()
        LookaroundPathDestinationActiveRejectedEmpty(_, _, _, _, _, _, _, _, _, _, _, _) -> ()
        LookaroundPathDestinationActiveRejected(_, _, _, _, _, _, _, _, _, _, _, _, _, _) -> ()
        LookaroundPathDestinationAcceptedRejected(_, branch_char, branch_rest, _, _, _, _, _, _, _, _, equation) ->
          consume_equation(
            depth,
            n,
            machine,
            branch_char,
            branch_rest,
            after_input,
            source,
            history,
            capture_context,
            policy,
            destinations,
            equation
          )
    end
    '''

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "destination rejection retains the canonical child origin" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(source, "AtomicPathDestinationRejected :", parts: 2)

    [body | _] = String.split(body, "-> AtomicPathRefutation", parts: 2)
    assert body =~ "child_origin_canonical: AtomicPathSearchOrigin"
    refute source =~ "type AtomicPathOriginWitness"
  end

  test "accepting-path rejection exposes its canonical transition destination" do
    source = ~S'''
    mod RegexPathCanonicalRejectionRegression
      use Std.Core
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn consume(
        depth: Nat,
        n: Nat,
        machine: PatternMachine(n),
        char: Char,
        rest: List(Char),
        after_input: List(Char),
        source: Bounded(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy,
        failure: LookaroundPathFailure(
          depth,
          n,
          machine,
          Cons(char, rest),
          after_input,
          ThreadActive(source),
          history,
          capture_context,
          policy,
          lookaround_machine_destinations(
            depth,
            n,
            machine,
            ThreadActive(source),
            char,
            rest,
            after_input,
            history,
            capture_context,
            policy
          ),
          lookaround_machine_destinations(
            depth,
            n,
            machine,
            ThreadActive(source),
            char,
            rest,
            after_input,
            history,
            capture_context,
            policy
          )
        )
      ) -> Unit = ()

      fn probe(
        depth: Nat,
        n: Nat,
        machine: PatternMachine(n),
        char: Char,
        rest: List(Char),
        after_input: List(Char),
        source: Bounded(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy
      ) -> Unit = match lookaround_accepting_path(
        depth,
        n,
        machine,
        Cons(char, rest),
        after_input,
        ThreadActive(source),
        history,
        capture_context,
        policy
      )
        LookaroundAcceptingPathRejectedStep(_, _, _, _, failure) -> consume(
          depth,
          n,
          machine,
          char,
          rest,
          after_input,
          source,
          history,
          capture_context,
          policy,
          failure
        )
        LookaroundAcceptingPathFoundActive(_, _, _, _, _, _, _) -> ()
        LookaroundAcceptingPathFoundAccepted(_, _, _) -> ()
    end
    '''

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "accepted destination tails fold arbitrary sibling suffixes" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(source, "fn atomic_path_tail_rejection_excludes_selected_suffix(", parts: 2)

    [body | _] = String.split(body, "\n  ##", parts: 2)

    assert body =~ "atomic_path_rejected_tail_fold_to_accepted("
    assert body =~ "_tail_selected_suffix"
  end

  test "rejected tails dispatch active-child failures through the generic fold" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "fn atomic_path_rejected_tail_fold_to_active("

    [_prefix, body] =
      String.split(source, "fn atomic_path_rejected_tail_fold_to_active(", parts: 2)

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "atomic_path_tail_active_child_rejection_excludes_selected_suffix_base("
  end

  test "active-child later siblings use the indexed recursive tail fold" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(source, "fn atomic_path_active_child_rejection_excludes_aligned_trace(", parts: 2)

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "atomic_path_active_child_rejection_head_excludes_trace("
  end

  test "active-child destination rejection has a named construction-site consumer" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~
             "fn atomic_path_active_child_rejection_excludes_destination_rejected("

    [_prefix, body] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_excludes_aligned_trace(",
        parts: 2
      )

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "atomic_path_active_child_rejection_head_excludes_trace("

    [_prefix, head_body] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_head_excludes_trace(",
        parts: 2
      )

    [head_body | _] = String.split(head_body, "\n  ##", parts: 2)
    assert head_body =~ "atomic_path_active_child_rejection_excludes_destination_rejected("

    [_prefix, helper_body] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_excludes_destination_rejected(",
        parts: 2
      )

    [helper_body | _] = String.split(helper_body, "\n  ##", parts: 2)
    assert helper_body =~ "atomic_path_active_child_rejection_tail_fold("
  end

  test "active-child singleton rejection consumes the indexed head contradiction" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "fn atomic_path_active_child_rejection_head_excludes_trace"

    [_prefix, body] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_excludes_aligned_trace(",
        parts: 2
      )

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "atomic_path_active_child_rejection_head_excludes_trace("
  end

  test "active-child head consumer does not retain the removed weak origin witness" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, active_body] =
      String.split(source, "fn atomic_path_active_child_rejection_head_excludes_trace(", parts: 2)

    [active_body | _] = String.split(active_body, "\n  ##", parts: 2)

    refute active_body =~ "AtomicPathOriginWitness"
    assert active_body =~ "failure_suffix: LookaroundAdmittedStateCursorSuffix"
  end

  test "active-child head consumer discharges terminal child failures" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~
             "fn atomic_path_active_child_rejection_head_input_exhausted_excludes_trace("

    assert source =~
             "@erased _failure: AtomicPathRefutation(\n" <>
               "      depth,\n" <>
               "      n,\n" <>
               "      machine,\n" <>
               "      Nil(),"

    assert source =~ "AtomicPathFailureInputExhausted()"

    assert source =~
             "fn atomic_path_active_child_rejection_head_exact_accepted_excludes_trace("

    assert source =~ "AtomicPathFailureExactAccepted()"
  end

  test "erased nested terminal traces can call the exhaustion eliminator" do
    source = ~S'''
    mod RegexErasedNestedTerminalRegression
      use Std.Core
      use Std.Decision
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn probe(
        {depth: Nat},
        {n: Nat},
        @erased machine: PatternMachine(n),
        @erased after_input: List(Char),
        @erased state: Bounded(n),
        @erased history: List(Char),
        @erased capture_context: List(EvidenceInstruction),
        @erased policy: NewlinePolicy,
        @erased scope_depth: Nat,
        @erased prefix_mode: Bool,
        @erased reversed_prefix: List(Char),
        @erased candidate_current: List(LookaroundAdmittedState(n)),
        @erased matched: List(Char),
        @erased remaining_input: List(Char),
        @erased routine: List(ExtendedInstruction),
        @erased path: AtomicSelectedPathTrace(
          depth,
          n,
          machine,
          Nil(),
          after_input,
          ThreadActive(state),
          history,
          capture_context,
          policy,
          scope_depth,
          prefix_mode,
          reversed_prefix,
          candidate_current,
          matched,
          remaining_input,
          routine
        )
      ) -> Empty = atomic_path_input_exhaustion_excludes_trace_erased(path)

      fn exact_probe(
        {depth: Nat},
        {n: Nat},
        @erased machine: PatternMachine(n),
        @erased char: Char,
        @erased rest: List(Char),
        @erased after_input: List(Char),
        @erased history: List(Char),
        @erased capture_context: List(EvidenceInstruction),
        @erased policy: NewlinePolicy,
        @erased scope_depth: Nat,
        @erased reversed_prefix: List(Char),
        @erased candidate_current: List(LookaroundAdmittedState(n)),
        @erased matched: List(Char),
        @erased remaining_input: List(Char),
        @erased routine: List(ExtendedInstruction),
        @erased failure: AtomicPathRefutation(
          depth,
          n,
          machine,
          Cons(char, rest),
          after_input,
          ThreadAccepted(),
          history,
          capture_context,
          policy,
          scope_depth,
          False(),
          reversed_prefix,
          Nil(),
          Nil(),
          AtomicPathFailureExactAccepted()
        ),
        @erased path: AtomicSelectedPathTrace(
          depth,
          n,
          machine,
          Cons(char, rest),
          after_input,
          ThreadAccepted(),
          history,
          capture_context,
          policy,
          scope_depth,
          False(),
          reversed_prefix,
          candidate_current,
          matched,
          remaining_input,
          routine
        )
      ) -> Empty = atomic_path_exact_failure_excludes_trace_erased(failure, path)
    end
    '''

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "active-child head has a recursive active-child construction consumer" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~
             "fn atomic_path_active_child_rejection_head_active_excludes_trace("

    [_prefix, body] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_head_active_excludes_trace(",
        parts: 2
      )

    [body | _] = String.split(body, "\n  ##", parts: 2)
    assert body =~ "AtomicSelectedTransitionActive"
    assert body =~ "AtomicPathDestinationRejected"
    assert body =~ "atomic_path_input_exhaustion_excludes_trace_erased(child_trace)"
  end

  test "active-child head active consumer type-checks at its indexed construction site" do
    source = ~S'''
    mod RegexActiveChildHeadConstructionRegression
      use Std.Core
      use Std.Decision
      use Std.Regex.Core
      use Std.Regex.Runtime

      fn probe(
        {depth: Nat},
        {n: Nat},
        machine: PatternMachine(n),
        char: Char,
        after_input: List(Char),
        source: Bounded(n),
        history: List(Char),
        capture_context: List(EvidenceInstruction),
        policy: NewlinePolicy,
        scope_depth: Nat,
        prefix_mode: Bool,
        reversed_prefix: List(Char),
        active_state: Bounded(n),
        active_routine: List(EvidenceInstruction),
        active_constraints: List(BoundaryConstraint),
        active_assertion_routine: List(ExtendedInstruction),
        active_assertion_markers: List(EvidenceInstruction),
        active_nested_decisions: List(LookaroundNestedDecision),
        {@erased failure_whole: List(LookaroundAdmittedState(n))},
        {@erased failure_remaining: List(LookaroundAdmittedState(n))},
        @erased failure: AtomicPathRefutation(
          depth,
          n,
          machine,
          Cons(char, Nil()),
          after_input,
          ThreadActive(source),
          history,
          capture_context,
          policy,
          scope_depth,
          prefix_mode,
          reversed_prefix,
          failure_whole,
          Cons(LookaroundAdmittedActive(active_state, active_routine, active_constraints, active_assertion_routine, active_assertion_markers, active_nested_decisions), failure_remaining),
          AtomicPathFailureDestinationRejected()
        ),
        {@erased selected_remaining: List(LookaroundAdmittedState(n))},
        {matched: List(Char)},
        {remaining_input: List(Char)},
        {selected_routine: List(ExtendedInstruction)},
        @erased path: AtomicSelectedPathTrace(
          depth,
          n,
          machine,
          Cons(char, Nil()),
          after_input,
          ThreadActive(source),
          history,
          capture_context,
          policy,
          scope_depth,
          prefix_mode,
          reversed_prefix,
          Cons(LookaroundAdmittedActive(active_state, active_routine, active_constraints, active_assertion_routine, active_assertion_markers, active_nested_decisions), selected_remaining),
          matched,
          remaining_input,
          selected_routine
        )
      ) -> Empty = atomic_path_active_child_rejection_head_active_excludes_trace(
        machine,
        char,
        after_input,
        source,
        history,
        capture_context,
        policy,
        scope_depth,
        prefix_mode,
        reversed_prefix,
        active_state,
        active_routine,
        active_constraints,
        active_assertion_routine,
        active_assertion_markers,
        active_nested_decisions,
        failure,
        path
      )
    end
    '''

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "singleton active-child exhaustion is wired to the specialized head consumer" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(
        source,
        "fn atomic_path_tail_active_child_exhaustion_excludes_selected_suffix(",
        parts: 2
      )

    [body | _] = String.split(body, "\n  ##", parts: 2)

    assert body =~ "atomic_path_active_child_rejection_head_active_excludes_trace("
  end

  test "singleton active-child rejection descends through the nested exhausted leaf" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, body] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_singleton_active_excludes_trace(",
        parts: 2
      )

    [body | _] = String.split(body, "\n  ##", parts: 2)

    assert body =~ ") -> Empty = atomic_path_active_child_rejection_head_active_excludes_trace("
    assert body =~ "child_failure,\n    child_path"
  end

  test "singleton child alignment carries the indexed nested trace through sibling tails" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "type AtomicPathCursorLocation"
    assert source =~ "fn atomic_path_active_child_rejection_singleton_aligned_excludes_trace("

    [_prefix, base_body] =
      String.split(
        source,
        "fn atomic_path_tail_active_child_rejection_excludes_selected_suffix_base(",
        parts: 2
      )

    [base_body | _] = String.split(base_body, "\n  ##", parts: 2)

    assert base_body =~ "@erased child_path: AtomicSelectedPathTrace("
    assert base_body =~ "atomic_path_active_child_rejection_singleton_aligned_excludes_trace("
    assert base_body =~ "atomic_path_failed_selected_child_suffix("
    assert base_body =~ "child_selected_origin_canonical,"
    refute base_body =~ "child_selected_whole_equivalence: Equivalent("

    [_prefix, fold_body] =
      String.split(source, "fn atomic_path_rejected_tail_fold_to_active(", parts: 2)

    [fold_body | _] = String.split(fold_body, "\n  ##", parts: 2)

    assert fold_body =~ "@erased child_path: AtomicSelectedPathTrace("
    assert fold_body =~ "child_selected_suffix,\n            child_path,"
  end

  test "atomic path rejection has a recursive proof-only kind witness" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    assert source =~ "type LookaroundAdmittedStateCaptureContext"
    assert source =~ "type AtomicPathSearchOriginAlignment"
    assert source =~ "fn atomic_path_search_origin_alignment("
    assert source =~ "fn atomic_path_failed_selected_child_cursor_alignment("
    assert source =~ "fn atomic_path_active_child_rejection_canonical_dispatch("

    [_prefix, canonical_dispatch] =
      String.split(
        source,
        "fn atomic_path_active_child_rejection_canonical_dispatch(",
        parts: 2
      )

    [canonical_dispatch | _] = String.split(canonical_dispatch, "\n  ##", parts: 2)

    assert canonical_dispatch =~ "atomic_path_failed_selected_child_cursor_alignment("
    assert canonical_dispatch =~ "atomic_path_active_child_alignment_from_canonical("

    [_prefix, active_fold] =
      String.split(source, "fn atomic_path_rejected_tail_fold_to_active(", parts: 2)

    [active_fold | _] = String.split(active_fold, "\n  ##", parts: 2)

    assert active_fold =~ "child_failure_origin_canonical: AtomicPathSearchOrigin("
    assert active_fold =~ "child_selected_origin_canonical: AtomicPathSearchOrigin("
    assert active_fold =~ "child_failure_origin_equivalence,"
    refute active_fold =~ "child_selected_whole_equivalence: Equivalent("

    [_prefix, failure_dispatch] =
      String.split(
        source,
        "fn atomic_path_tail_active_child_failure_dispatch(",
        parts: 2
      )

    [failure_dispatch | _] = String.split(failure_dispatch, "\n  ##", parts: 2)

    assert failure_dispatch =~ "child_kind: AtomicPathFailureKind"
    assert failure_dispatch =~ "atomic_path_failed_selected_child_suffix("
    assert failure_dispatch =~ "atomic_path_active_child_rejection_canonical_current_dispatch("
    assert failure_dispatch =~ "AtomicSelectedTransitionActive("
    assert failure_dispatch =~ "atomic_path_active_child_rejection_singleton_active_excludes_trace_erased("
    assert failure_dispatch =~ "AtomicSelectedTransitionAccepted("
    assert failure_dispatch =~ "atomic_path_accepted_child_rejection_singleton_excludes_trace_erased(child_failure)"
    refute failure_dispatch =~ "child_selected_whole_equivalence: Equivalent("
    assert source =~ "AtomicPathSearchOriginActiveEmpty :"
    assert source =~ "type AtomicPathNoEvidence"
    assert source =~ "AtomicPathNoInputExhausted :"
    assert source =~ "AtomicPathNoExactAcceptedWithInput :"
    assert source =~ "AtomicPathNoDestinationsExhausted :"

    [_prefix, constructor] =
      String.split(source, "AtomicPathNoDestinationRejected :", parts: 2)

    [constructor | _] = String.split(constructor, "\n\n", parts: 2)

    assert constructor =~ "child_context_alignment: LookaroundAdmittedStateCaptureContext("
    assert constructor =~ "child_origin_equivalence: Equivalent("
    assert constructor =~ "child_origin_canonical: AtomicPathSearchOrigin("
    assert constructor =~ "child_suffix: LookaroundAdmittedStateCursorSuffix("
    assert constructor =~ "child_evidence: AtomicPathNoEvidence("
    assert constructor =~ "tail_suffix: LookaroundAdmittedStateCursorSuffix("
    assert constructor =~ "tail_evidence: AtomicPathNoEvidence("
  end

  test "atomic path evaluators publish recursive rejection evidence at construction sites" do
    source = File.read!(Path.expand("../../../lib/std_deps/regex/regex_runtime.cure", __DIR__))

    [_prefix, root] = String.split(source, "type AtomicPathRootRefutation", parts: 2)
    [root | _] = String.split(root, "\n\n", parts: 2)
    assert root =~ "evidence: AtomicPathNoEvidence("
    assert root =~ "origin_equivalence: Equivalent("
    assert root =~ "origin_canonical: AtomicPathSearchOrigin("

    [_prefix, search] = String.split(source, "type AtomicPathSearchResult", parts: 2)
    [search | _] = String.split(search, "\n\n", parts: 2)
    assert search =~ "AtomicPathSearchNo :"
    assert search =~ "skipped_evidence: AtomicPathSkippedPrefixEvidence("
    assert search =~ "AtomicPathSearchCommit :"
    assert search =~ "cause: AtomicPathCommitCause("
    assert search =~ "origin_canonical: AtomicPathSearchOrigin("
    assert search =~ "evidence: AtomicPathNoEvidence("

    [_prefix, members] = String.split(source, "type AtomicPathMembersResult", parts: 2)
    [members | _] = String.split(members, "\n\n", parts: 2)
    assert members =~ "AtomicPathMembersNo :"
    assert members =~ "AtomicPathMembersEscapedNo :"
    assert members =~ "skipped_evidence: AtomicPathSkippedPrefixEvidence("
    assert members =~ "AtomicPathMembersCommit :"
    assert members =~ "cause: AtomicPathCommitCause("
    assert members =~ "origin_canonical: AtomicPathSearchOrigin("
    assert members =~ "evidence: AtomicPathNoEvidence("

    [_prefix, tail_fold] =
      String.split(source, "fn atomic_lookaround_routine_tail_after_failure(", parts: 2)

    [tail_fold | _] = String.split(tail_fold, "\n\n", parts: 2)
    assert tail_fold =~ "child_evidence: AtomicPathNoEvidence("
    assert tail_fold =~ "tail_evidence) -> AtomicPathMembersNo("

    assert tail_fold =~
             "AtomicPathNoDestinationRejected(child_context_alignment, child_prefix, child_origin_equivalence, child_origin_canonical, child_suffix, child_evidence, tail_suffix, tail_origin_equivalence, tail_evidence)"

    [_prefix, root_projection] =
      String.split(source, "fn atomic_path_members_root_to_search(", parts: 2)

    [root_projection | _] = String.split(root_projection, "\n\n", parts: 2)

    assert root_projection =~
             "AtomicPathMembersEscapedNo(skipped, tail_current, skipped_evidence, origin, origin_equivalence, origin_canonical, witness, suffix, kind, failure, evidence)"

    assert root_projection =~
             "AtomicPathSearchNo(skipped, whole, tail_current, skipped_evidence, origin, origin_equivalence, origin_canonical, witness, suffix, kind, failure, evidence)"

    assert source =~ "type AtomicPathCommitCause("
    assert source =~ "AtomicPathCommitAfterFailure :"
    assert source =~ "AtomicPathCommitFromChild :"
    assert source =~ "AtomicPathCommitPastRejected :"
    assert source =~ "AtomicPathCommitPastEscaped :"
    assert source =~ "type AtomicPathSkippedPrefixEvidence("
    assert source =~ "AtomicPathSkippedRejectedCons :"
    assert source =~ "AtomicPathEscapedCommitOne :"
    assert source =~ "AtomicPathEscapedCommitCons :"
    assert source =~ "type AtomicPathFailurePrefixEvidence("
    assert source =~ "AtomicPathFailureAtRoot :"
    assert source =~ "AtomicPathFailureAfterSkipped :"

    [_prefix, skipped_rejected] =
      String.split(source, "AtomicPathSkippedRejectedCons :", parts: 2)

    [skipped_rejected | _] = String.split(skipped_rejected, "\n\n", parts: 2)
    assert skipped_rejected =~ "child_prefix: AtomicPathFailurePrefixEvidence("
    assert source =~ "type AtomicPathStrictCursorSuffix("
    assert source =~ "AtomicPathStrictCursorSuffixDrop :"
    assert source =~ "fn atomic_path_cons_cannot_be_suffix_of_its_tail("
    assert source =~ "fn atomic_path_strict_cursor_suffix_excludes_reverse("

    [_prefix, cursor_location] =
      String.split(source, "type AtomicPathCursorLocation", parts: 2)

    [cursor_location | _] = String.split(cursor_location, "\n\n", parts: 2)

    assert cursor_location =~
             "AtomicPathCursorLocationLeftAfter : (marker: AtomicPathStrictCursorSuffix("

    [_prefix, rejection] =
      String.split(source, "AtomicPathDestinationRejected :", parts: 2)

    [rejection | _] = String.split(rejection, "\n", parts: 2)
    assert rejection =~ "child_prefix: AtomicPathFailurePrefixEvidence("

    [_prefix, no_rejection] =
      String.split(source, "AtomicPathNoDestinationRejected :", parts: 2)

    [no_rejection | _] = String.split(no_rejection, "\n", parts: 2)
    assert no_rejection =~ "child_prefix: AtomicPathFailurePrefixEvidence("

    [_prefix, after_failure] =
      String.split(source, "fn atomic_lookaround_routine_after_failure(", parts: 2)

    [after_failure | _] = String.split(after_failure, "\n\n", parts: 2)

    refute after_failure =~ "child_origin_equivalence, AtomicPathOriginWitnessNone()"
    assert after_failure =~ "child_origin_equivalence, child_origin_canonical, child_witness"
  end
end
