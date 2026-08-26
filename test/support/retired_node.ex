defmodule Cure.TestSupport.RetiredNode do
  @moduledoc false
  # Launder a deliberately-retired / ill-typed Core node past Elixir's set-
  # theoretic type checker. The retirement + rejection tests pass node shapes
  # intentionally ABSENT from a function's clause union — to prove the RUNTIME
  # rejects them (FunctionClauseError) — which the compiler's type inference
  # would otherwise pre-flag as "incompatible types given to …". Returning
  # `term()` makes the value's shape opaque at the call site (a cross-module call
  # uses the callee's @spec, not the argument's inferred shape), so the check is
  # deferred to runtime — which is exactly what these tests exercise.
  @spec opaque(term()) :: term()
  def opaque(node), do: node
end
