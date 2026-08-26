defmodule Antigen.Backend.StreamData do
  @moduledoc "The StreamData backend — the ONLY module allowed to reference StreamData."
  # `stream_data` is a `:test`-only dep (mix.exs), so in dev/prod compiles the
  # module is absent. That is by design — this backend is swappable and only the
  # test suite drives it — so silence the expected "undefined" warnings here
  # rather than pulling the dep into every environment.
  @compile {:no_warn_undefined, StreamData}
  @behaviour Antigen.Backend

  @impl true
  def interp({:return, x}), do: StreamData.constant(x)
  def interp({:member_of, xs}), do: StreamData.member_of(xs)
  def interp({:integer, lo, hi}), do: StreamData.integer(lo..hi)
  def interp({:one_of, gs}), do: StreamData.one_of(Enum.map(gs, &interp/1))
  def interp({:frequency, ws}), do: StreamData.frequency(Enum.map(ws, fn {w, g} -> {w, interp(g)} end))
  def interp({:bind, g, f}), do: StreamData.bind(interp(g), fn x -> interp(f.(x)) end)
  def interp({:sized, f}), do: StreamData.sized(fn n -> interp(f.(n)) end)
  def interp({:resize, n, g}), do: StreamData.resize(interp(g), n)
  def interp({:tagged, _tag, g}), do: interp(g)

  # Deferred construction: `fun.()` (which builds the sub-generator's reified AST)
  # and its `interp` run only when generation descends here, so a recursive
  # generator unfolds one sampled path at a time. `bind` over a constant is the
  # StreamData idiom for "don't build this until asked".
  def interp({:lazy, fun}), do: StreamData.bind(StreamData.constant(nil), fn _ -> interp(fun.()) end)

  @impl true
  def sample(native, count), do: Enum.take(native, count)

  # StreamData's own `__reduce__` caps generation size at this value; the seeded
  # path replicates the cap via `StreamData.scale/2` so its value sequence matches
  # a normal (os-timestamp-seeded) enumeration started from the same seed.
  @max_size 100

  @doc """
  Deterministically draw `count` values from `descr` using the integer `seed` — the
  reproducibility primitive for `mix antigen --seed N`.

  Unlike `Enum.take/2` on `interp(descr)` (whose `Enumerable` impl reseeds from
  `:os.timestamp/0` every enumeration, so runs cannot be replayed), this drives the
  public `StreamData.check_all/3` with an explicit `initial_seed`, accumulating each
  generated value. `check_all` ramps size unbounded, so the generator is wrapped in
  `StreamData.scale/2` to reinstate StreamData's normal `#{@max_size}` size cap —
  making the produced sequence identical to what a same-seed enumeration would yield.
  Same `seed` ⇒ same sequence; different `seed` ⇒ (with overwhelming probability) a
  different one.
  """
  @spec sample_seeded(term(), non_neg_integer(), integer()) :: [term()]
  def sample_seeded(descr, count, seed) when is_integer(seed) and is_integer(count) and count >= 0 do
    key = {:antigen_sample_seeded, make_ref()}
    Process.put(key, [])
    capped = StreamData.scale(interp(descr), fn size -> min(size, @max_size) end)

    try do
      StreamData.check_all(
        capped,
        [initial_seed: {seed, 0, 0}, initial_size: 1, max_runs: count, max_run_time: :infinity],
        fn value ->
          Process.put(key, [value | Process.get(key)])
          {:ok, nil}
        end
      )

      key |> Process.get() |> Enum.reverse()
    after
      Process.delete(key)
    end
  end

  @doc """
  Check a reified Antigen generator with StreamData's shrinking engine.

  The callback must return `true`/`:ok` for success or `false`/an error term
  for failure. Keeping this adapter here preserves the project's rule that no
  test or production module references StreamData directly.
  """
  @spec check_all(term(), keyword(), (term() -> boolean() | :ok | term())) :: :ok | term()
  def check_all(descr, opts \\ [], property) when is_function(property, 1) do
    defaults = [initial_seed: {101, 102, 103}, initial_size: 1, max_runs: 100, max_run_time: :infinity]

    result =
      StreamData.check_all(interp(descr), Keyword.merge(defaults, opts), fn value ->
        case property.(value) do
          true -> {:ok, nil}
          :ok -> {:ok, nil}
          false -> {:error, {:property_failed, value}}
          error -> {:error, error}
        end
      end)

    case result do
      {:ok, _metadata} -> :ok
      error -> error
    end
  end
end
