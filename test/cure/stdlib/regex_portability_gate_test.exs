defmodule Cure.Stdlib.RegexPortabilityGateTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.PortableClosure

  test "the declared cure_regex runtime closure is portable" do
    root = Application.fetch_env!(:cure, :stdlib_beam_dir)
    assert {:ok, report} = PortableClosure.audit(root, package: "cure_regex")

    assert report.roots == ["Std.Regex"]
    assert "Std.Regex" in report.modules
    refute Enum.any?(report.modules, &String.contains?(&1, ".Syntax.Parser"))
    assert report.forbidden == []
    assert report.nifs == []
  end

  test "the forbidden capability classifier names portability hazards" do
    assert PortableClosure.forbidden_mfa?({:re, :run, 3}) == :host_regex_or_parser
    assert PortableClosure.forbidden_mfa?({:ets, :lookup, 2}) == :ets_or_process_global_state
    assert PortableClosure.forbidden_mfa?({:erlang, :spawn, 3}) == :process
    assert PortableClosure.forbidden_mfa?({:erlang, :open_port, 2}) == :port
    assert PortableClosure.forbidden_mfa?({:erlang, :nif_error, 1}) == :nif
    refute PortableClosure.forbidden_mfa?({:erlang, :+, 2})
  end
end
