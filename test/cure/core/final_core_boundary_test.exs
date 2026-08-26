defmodule Cure.Core.FinalCoreBoundaryTest do
  @moduledoc """
  Two ways a Final-Core grammar violation used to slip past `Validator`.

  ## The builtin-op admission path never scanned anything

  `Kernel.check_def/2` has two admission branches. The generic one runs `infer_sort`, `check`,
  and then `run_final_core_validator` over both the declared type and the body — `validator_test.exs`
  pins that "a violating node in the declared TYPE is caught too". The builtin-op branch
  (`%{builtin_op: op, type: type_term}`) only confirmed the declared type was a valid sort, and
  never reached the validator at all. Any clause set to `:reject` — including ones already
  rejecting in `release_config/0` — was silently unenforced on that path.

  Reproduced below with a `qualified_syms` violation rather than a hole, because a hole in type
  position does not kernel-typecheck: only `check/3` admits one, never `infer/2`. The violation
  has to be something the kernel would otherwise accept, or the test proves nothing about the
  bypass.

  ## The fail-closed fallback only descended one list deep

  `Validator.children/1`'s fallback clause is documented to "descend CONSERVATIVELY into every
  element that is itself a term-tuple or a list of them, so a forbidden node buried in an unknown
  wrapper cannot escape the walker (fail-closed)". `validator_unknown_node_test.exs` proves that
  for a subterm sitting directly in a list. But `term_children/1`'s list clause was
  `Enum.filter(xs, &is_tuple/1)`, keeping only elements that are themselves tuples — an element
  that is itself a *list* was filtered out rather than descended into. An unrecognized node whose
  field is a list of lists of subterms hid its contents from the walker entirely, one nesting
  level below where the earlier fix reached.
  """

  # async: false — the first test writes `:cure, :final_core_config`, the process-independent
  # global key `Kernel.check_def/2` reads, and every other `test/cure/core/` suite calls
  # `check_def`. Same rationale `validator_test.exs` gives for staying serial.
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel, Validator}

  test "a builtin-op def's declared type crosses the Final-Core boundary" do
    {:ok, env0} = Cure.Elab.Program.elaborate("mod M\nend\n")

    env =
      env0
      |> Env.add_def(:natty, {:type, 0}, {:data, :Nat, [], []})
      |> Env.add_def(:myop, {:global, :natty}, nil)
      |> Env.register_builtin_op(:myop, :some_op)

    cfg = Map.put(Validator.wave0_config(), :qualified_syms, :reject)
    Application.put_env(:cure, :final_core_config, cfg)
    on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

    # The clause fires when the validator scans that type term directly, so the gap was
    # `check_def`'s wiring, not an inert predicate.
    assert {:error, direct} = Validator.validate({:global, :natty}, cfg)
    assert Enum.any?(direct, &(&1.clause == :qualified_syms))

    assert {:error, {:final_core_violation, rejections}} = Kernel.check_def(env, :myop)
    assert Enum.any?(rejections, &(&1.clause == :qualified_syms))
  end

  test "a hole nested two lists deep inside an unrecognized node does not escape the walker" do
    node = {:futuretag, [[{:hole, "h"}]]}

    assert {:error, diags} = Validator.validate(node, Validator.release_config())

    assert Enum.any?(diags, &(&1.clause == :no_hole)),
           "the doubly-nested hole must be discovered and rejected; got #{inspect(diags)}"
  end
end
