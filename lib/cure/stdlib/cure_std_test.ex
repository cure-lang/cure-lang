defmodule :cure_std_test do
  @moduledoc """
  Runtime helpers for `Std.Test.forall_shrunk/3`.

  When a property fails, walk the shrink candidates in aggressive-first order
  and pick the smallest value that still makes the property return `false`.

  Returns a `Std.Result`: `{:ok, :unit}` when every sample satisfied the property,
  `{:error, minimal}` carrying the minimised counterexample when one did not.

  It used to return the bare atom `:ok` and raise
  `{:property_failed_with_shrunk, minimal}`, under an `@extern` postulating
  `∀t. (Atom -> t) -> (t -> Bool) -> Int -> t`. Neither branch inhabited `t`,
  and the raise made the postulated totality false. The type is now
  `Result(Unit, t)` and both branches produce a value.

  The tags are the OTP-compatible dependent-pipeline erasure:
  `Ok(v)` → `{:ok, v}`, `Error(e)` → `{:error, e}`.
  """

  def forall_shrunk(gen, property, runs) when is_function(gen) and is_function(property) do
    case find_counterexample(gen, property, runs) do
      :all_pass ->
        {:ok, :unit}

      {:failed, value} ->
        {:error, shrink_loop(value, property)}
    end
  end

  # Zero or fewer runs: nothing to falsify, so vacuously pass. `runs: Int` admits
  # negatives, so this must not be a bare `0` clause.
  defp find_counterexample(_gen, _property, n) when n <= 0, do: :all_pass

  defp find_counterexample(gen, property, n) when n > 0 do
    value = gen.(:unit)

    # `safe_invoke` treats a raising property as `false`: a property that blows
    # up on a drawn value has not been shown to hold, so that value is a
    # counterexample. Without this the function raises, contradicting its
    # `Result`/totality contract. The shrink loop already does the same.
    case safe_invoke(property, value) do
      true -> find_counterexample(gen, property, n - 1)
      _ -> {:failed, value}
    end
  end

  defp shrink_loop(value, property) do
    candidates =
      try do
        :cure_std_gen.shrink(value)
      rescue
        _ -> []
      end

    failing =
      Enum.find(candidates, fn cand ->
        # A candidate still fails unless the property holds (`true`). This must
        # agree with `find_counterexample`, which treats any non-`true` return as
        # a failure — otherwise a property that returns a non-boolean would
        # shrink to nothing and report the raw first draw as the counterexample.
        safe_invoke(property, cand) != true
      end)

    case failing do
      nil -> value
      better -> shrink_loop(better, property)
    end
  end

  defp safe_invoke(f, v) do
    try do
      f.(v)
    rescue
      _ -> false
    catch
      _, _ -> false
    end
  end
end
