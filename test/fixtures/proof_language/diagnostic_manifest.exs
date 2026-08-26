%{
  E109: %{
    key: :proof_chain_syntax,
    variants: [
      :empty_chain,
      :missing_relation,
      :missing_right_side,
      :missing_because,
      :first_step_previous,
      :unreachable_proof_statement
    ],
    labels: [:construct, :step, :observed]
  },
  E110: %{
    key: :proof_chain_mismatch,
    variants: [:adjacent_endpoints, :wrong_justification, :unfinished_justification],
    labels: [:previous_step, :current_step, :justification, :residual_goal]
  },
  E111: %{
    key: :rewrite_failed,
    variants: [:no_occurrence, :ambiguous_occurrence, :invalid_occurrence, :bad_target, :reverse_only],
    labels: [:command, :theorem, :goal, :occurrences]
  },
  E112: %{
    key: :simplification_failed,
    variants: [:inadmissible_rule, :proof_mismatch, :residual_goal, :resource_guard],
    labels: [:command, :rule, :before_goal, :after_goal]
  },
  E113: %{
    key: :induction_failed,
    variants: [
      :non_inductive_subject,
      :missing_case,
      :duplicate_case,
      :unknown_case,
      :impossible_case,
      :wrong_case_fields,
      :unavailable_hypothesis
    ],
    labels: [:subject, :case, :constructor_declaration, :hypothesis]
  },
  E114: %{
    key: :defining_equation_unavailable,
    variants: [:unknown_equation, :inaccessible_equation, :friendly_name_collision],
    labels: [:equation_use, :function_definition, :candidate_equations]
  },
  E115: %{
    key: :named_argument_mismatch,
    variants: [:unknown_label, :duplicate_label, :positional_after_named, :ambiguous_label, :missing_label],
    labels: [:call, :argument, :parameter_declaration]
  }
}
