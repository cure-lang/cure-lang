defmodule Antigen.Assays.ReflexivityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Reflexivity, as: A
  alias Antigen.Generators.Forcing, as: G

  test "reports no infection now the hole is fixed (the forcing pair's globals stay uncertified)" do
    # `certified_env_of` runs the real certifier, which post-fix correctly refuses
    # to certify the diverging cycle. δ never unfolds, `conv(t, t')` terminates
    # within budget, so there is no non-normalization to flag. The assay remains a
    # standing probe: it would fire again if any future hole certified a diverging
    # global (see conv_fuel_test for the mechanism under manual certification).
    assert :ok == A.run(G.forcing_pair())
  end
end
