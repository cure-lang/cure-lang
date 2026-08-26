defmodule Cure.Elab.PiGradeSourceTest do
  @moduledoc """
  Slice 6: the def's **Pi binder is the single source of truth** for parameter
  quantities.

  Before this slice Cure stored each quantity twice and the two disagreed:
  `wrap_binders/3` hardcoded `ω` on every `:pi` and `:lam`, while the real vector
  lived in the def's `quantities`. An erased implicit or a demoted `where`-dict had
  `quantities: [:erased, …]` and a Pi/λ that said `ω` — the `ctor-spelling value
  dichotomy` class, one level up. Nothing re-checked the stored λ against the stored
  Π, so the lie was silent.

  Idris keeps the quantity on the Pi and nowhere else: `lcheck`'s `App` reads `rigf`
  off the callee's normalised type (`LinearCheck.idr:283`), and `eraseArgs` is a
  DERIVED projection of that type (`findErasedFrom`, `TTImp/Elab/Utils.idr:39-49`).

  This slice makes the stored Pi and λ carry the real grade, keeps them in agreement
  across `demote_unused_dicts/3`, and adds the assertion that would have caught the
  whole class: `Kernel.check` the final λ against the final Π before `Env.add_def`.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Eval, Context, Kernel}
  alias Cure.Elab.Program

  # Grades along a Π (or λ) spine, outermost first.
  defp pi_grades({:pi, g, _dom, cod}), do: [g | pi_grades(cod)]
  defp pi_grades(_), do: []

  defp lam_grades({:lam, g, _dom, body}), do: [g | lam_grades(body)]
  defp lam_grades(_), do: []

  @dict_src """
  mod C4
    interface Eqs(a)
      fn eqs(x: a, y: a) -> Bool
    implementation Eqs for Int
      fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    fn ignore({a: Type}, x: a) -> a where Eqs(a) = x
    fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
  end
  """

  describe "the Pi binder carries the real grade, matching quantities" do
    test "an erased implicit is erased on the Pi, not omega" do
      src = "mod I\n  fn id({a: Type}, x: a) -> a = x\nend\n"
      {:ok, env} = Program.semantic_result(Program.elaborate(src))
      d = Env.get_def(env, :id)

      assert d.quantities == [:erased, :unrestricted]
      assert pi_grades(d.type) == d.quantities
      assert lam_grades(d.body) == d.quantities
    end

    test "a demoted where-dict is erased on BOTH the Pi and the lambda" do
      {:ok, env} = Program.elaborate(@dict_src)
      d = Env.get_def(env, :ignore)

      # {a} erased, x present, dict demoted to erased.
      assert d.quantities == [:erased, :unrestricted, :erased]

      assert pi_grades(d.type) == d.quantities,
             "Pi grades #{inspect(pi_grades(d.type))} must match quantities #{inspect(d.quantities)}"

      assert lam_grades(d.body) == d.quantities
    end

    test "a USED where-dict stays present on the Pi" do
      {:ok, env} = Program.elaborate(@dict_src)
      d = Env.get_def(env, :same)

      # {a} erased, x present, y present, dict USED -> present.
      assert d.quantities == [:erased, :unrestricted, :unrestricted, :unrestricted]
      assert pi_grades(d.type) == d.quantities
      assert lam_grades(d.body) == d.quantities
    end

    test "an all-explicit function is all-omega on the Pi (unchanged)" do
      src = "mod P\n  fn add(x: Int, y: Int) -> Int = x\nend\n"
      {:ok, env} = Program.semantic_result(Program.elaborate(src))
      d = Env.get_def(env, :add)

      assert d.quantities == [:unrestricted, :unrestricted]
      assert pi_grades(d.type) == [:unrestricted, :unrestricted]
    end
  end

  describe "the stored lambda kernel-checks against the stored Pi" do
    # This is the assertion the slice adds, exercised from outside: whatever the
    # elaborator stored must be internally coherent — a λ whose grades match the type
    # it is stored under. If Pi and λ disagreed on any binder's grade, the graded
    # `Conv` (slice 2+3) would make this `Kernel.check` fail with `:grade_mismatch`.
    test "a demoted-dict def stores a coherent (λ : Π) pair" do
      {:ok, env} = Program.elaborate(@dict_src)
      d = Env.get_def(env, :ignore)

      ctx = Context.empty(env)
      assert :ok == Kernel.check(ctx, d.body, Eval.eval(d.type, Context.env(ctx)))
    end

    test "an erased-implicit def stores a coherent (λ : Π) pair" do
      {:ok, env} = Program.elaborate("mod I\n  fn id({a: Type}, x: a) -> a = x\nend\n")
      d = Env.get_def(env, :id)

      ctx = Context.empty(env)
      assert :ok == Kernel.check(ctx, d.body, Eval.eval(d.type, Context.env(ctx)))
    end
  end

  describe "the slice-6 grade assertion does not re-reject valid bodies (regression, adversarial review F1)" do
    # The first cut of slice 6 asserted grade-agreement by re-running a full
    # `Kernel.check` of the λ against the Π — but in a context that, unlike
    # `build_context/2`, did NOT whnf the binder types. A parameter whose type is a
    # δ-unfoldable ALIAS then reached the kernel as an opaque `{:vneutral,{:nglobal}}`
    # rather than its `{:vdata}` head, so a `match` on it failed with
    # `:case_scrutinee_not_data` — even though the body already type-checked against
    # the same type via the whnf'd `build_context`. The grade check must compare the
    # Pi/λ grade spines STRUCTURALLY, never re-check the body.
    test "a function matching on a type-alias parameter still elaborates" do
      src = """
      mod Demo
        typealias IntList = List(Int)
        fn is_empty2(xs: IntList) -> Bool =
          match xs
            [] -> true
            [_ | _] -> false
      end
      """

      assert {:ok, env} = Program.semantic_result(Program.elaborate(src))
      d = Env.get_def(env, :is_empty2)
      # And the grade is still recorded honestly (one explicit param, omega).
      assert d.quantities == [:unrestricted]
      assert pi_grades(d.type) == [:unrestricted]
    end

    test "an alias-typed match with a where-dict (demotion path) still elaborates" do
      src = """
      mod Demo2
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
        typealias IntList = List(Int)
        fn first_or({a: Type}, xs: IntList, d: Int) -> Int where Eqs(Int) =
          match xs
            [] -> d
            [h | _] -> h
      end
      """

      assert {:ok, _env} = Program.semantic_result(Program.elaborate(src))
    end
  end

  describe "the implicit-app slot iterator handles a linear/affine explicit param" do
    # `bidir_app_slot/5` (the implicit-insertion application path, taken whenever a
    # callee has a leading implicit `{...}`) only had @erased clauses for : and
    # :unrestricted domain grades; @linear a : (@affine or :) explicit param made it
    # RAISE `FunctionClauseError` rather than elaborate. The plain-application path
    # (`solve_arg/3`) already treats `grade in [:unrestricted, :linear, :affine]`
    # as "consume one supplied argument"; this brings the implicit path to parity.
    # Linearity itself is enforced later in `relevance.ex`, so consuming the slot
    # here launders nothing (the usage checker still counts occurrences).
    test "a callee with a leading implicit AND a linear explicit param is applied" do
      # `use_box` has an implicit `{t}` (solved from `x`), an ω param `x`, and a
      # LINEAR `c` consumed once. The call `use_box(y, c)` goes through the
      # implicit-app path and feeds `c` into the linear slot — the case that used
      # to raise. `{t}` is genuinely solvable here, so this is a clean positive.
      src = """
      mod CallLinearImplicit
        type Box = MkBox
        fn use_box({t: Type}, x: t, @linear c : Box) -> Box = c
        fn g(y: Int, @linear c : Box) -> Box = use_box(y, c)
      end
      """

      assert {:ok, _env} = Program.semantic_result(Program.elaborate(src))
    end

    test "linearity is STILL enforced through the implicit-app path (drop rejects)" do
      # The fix consumes the linear slot like an ω slot at the elaboration stage;
      # usage is counted later in relevance.ex. Guard that the fix did not launder
      # linearity: a body that DROPS the linear param must still be rejected, even
      # when reached via the implicit-app path.
      src = """
      mod DropLinearImplicit
        type Box = MkBox
        fn use_box({t: Type}, x: t, @linear c : Box) -> Box = MkBox
        fn g(y: Int, @linear c : Box) -> Box = use_box(y, c)
      end
      """

      assert {:error, {:usage_violation, %{declared: :linear}}} = Program.semantic_result(Program.elaborate(src))
    end
  end

  describe "obligation (1): plain `match` refines the linear reply capability (roadblock #2 CLOSED)" do
    # The handoff-brief §5 obligation-(1) shape: a `reply` eliminator with a leading
    # implicit `{r}` and a LINEAR reply capability whose value arg is typed by the
    # large-elimination `ReplyOf(r)`, driven by a handler that replies once per path.
    #
    # This was reach-pinned to REJECT on roadblock #2 — dependent `match` refined the
    # RETURN/motive but not the SIBLING `cap : ReplyCap(r)`, so `v : ReplyOf(r)` never
    # reduced. That gap is now CLOSED: motive-generalization refines scrutinee-
    # dependent siblings (work-order item A for `with r`, item C wiring plain `match`
    # to the same machinery), so this now elaborates and the linear `cap` is consumed
    # exactly once. Drop/dup remain rejected (see linear_sibling_refinement_test.exs).
    test "reply(cap, R0): plain-match handler refines cap and elaborates" do
      src = """
      mod ReplyLinear
        type Reply0 = R0
        type Reply1 = R1a | R1b
        type Req = GetCount | SetName(Reply0) | Ping

        fn ReplyOf(r: Req) -> Type = match r
          GetCount()  -> Reply0
          SetName(_)  -> Reply1
          Ping()      -> Reply1

        type ReplyCap(r: Req) indices ()
          MkCap : ReplyCap(r)

        type Replied = Done

        fn reply({r: Req}, @linear cap : ReplyCap(r), v: ReplyOf(r)) -> Replied =
          match cap
            MkCap() -> Done

        fn handle(r: Req, @linear cap : ReplyCap(r)) -> Replied = match r
          GetCount()  -> reply(cap, R0)
          SetName(_)  -> reply(cap, R1a)
          Ping()      -> reply(cap, R1b)
      end
      """

      assert {:ok, _env} = Program.semantic_result(Program.elaborate(src))
    end
  end
end
