defmodule Cure.Stdlib.PreloadStickyTest do
  # async: false — mutates the global code table (loads/sticks a throwaway module).
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Preload

  @throwaway :"Cure.Std.PreloadStickyProbe"

  # A minimal, valid BEAM binary for @throwaway: -module(...). with no exports.
  defp probe_binary do
    forms = [
      {:attribute, 1, :module, @throwaway},
      {:attribute, 1, :export, []}
    ]

    {:ok, @throwaway = mod, binary} = :compile.forms(forms, [:return_errors])
    {mod, binary}
  end

  test "a stuck stdlib module refuses load_binary, and Preload's own tolerance holds against the real canonical stdlib" do
    {mod, binary} = probe_binary()

    # Load then stick it, mimicking the C1 startup stanza.
    # NB: `:code.stick_mod/1` returns `true` (not `:ok`) — pattern-match on `true`.
    {:module, ^mod} = :code.load_binary(mod, ~c"nofile", binary)
    true = :code.stick_mod(mod)

    try do
      assert :code.is_sticky(mod)

      # A second load is refused with :sticky_directory -- the raw OTP-level
      # property `Preload`'s `load_if_present/2` tolerance branch
      # (`{:error, _reason} -> :ok`) depends on. This probe is deliberately
      # synthetic (a throwaway `Cure.Std.*`-shaped name with no `lib/std/*.cure`
      # declaration and no `.beam` file on disk) so proving it does not risk any
      # shared canonical module: `Preload.stdlib_modules/1` discovers modules
      # solely from real `lib/std/*.cure` declarations (or, as a packaged-release
      # fallback, real `.beam` files already on disk), so this in-memory-only
      # probe can never be reached by `Preload.preload/1`'s own discovery for
      # ANY `kind` -- it exists purely to pin the raw `:code` semantics, not to
      # drive Preload's own module-iteration code.
      assert {:error, :sticky_directory} = :code.load_binary(mod, ~c"nofile", binary)
    after
      :code.unstick_mod(mod)
      :code.purge(mod)
      :code.delete(mod)
    end

    # The end-to-end claim -- that a `Preload.preload/1` pass tolerates hitting
    # an already-stuck module without raising -- is exercised for real here:
    # `kind: :all` walks every real canonical `Cure.Std.*` module (all stuck by
    # `test/test_helper.exs`'s C1 stanza before any test ran), the same call
    # shape used at every production `preload(kind: :all)` site in this suite.
    assert Preload.preload(kind: :all) == :ok
  end
end
