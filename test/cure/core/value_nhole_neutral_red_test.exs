defmodule Cure.Core.ValueNholeNeutralRedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Value

  # FINDING A (lib/cure/core/value.ex:42 `@type neutral`, :107 `neutral?/1`):
  # `Eval.eval({:hole, id}, _env)` (eval.ex:104) produces `{:vneutral, {:nhole,
  # id}}`, and `Conv.conv_neutral?/4` (conv.ex:208/258) and
  # `Quote.reify_neutral/3` (quote.ex:112) all already treat `{:nhole, id}` as a
  # first-class neutral head. But `Value.neutral?/1` has no clause for it, so it
  # falls through to the catch-all `neutral?(_), do: false` — meaning a value
  # the evaluator legitimately produces is reported as NOT a well-formed
  # neutral/value by the module whose entire job is to answer that question.
  test "a {:nhole, id} neutral (as produced by Eval.eval/2 for {:hole, id}) is recognised as neutral" do
    assert Value.neutral?({:nhole, "x"})
  end

  test "a {:vneutral, {:nhole, id}} value (as produced by Eval.eval/2 for {:hole, id}) is recognised as a value" do
    assert Value.value?({:vneutral, {:nhole, "x"}})
  end
end
