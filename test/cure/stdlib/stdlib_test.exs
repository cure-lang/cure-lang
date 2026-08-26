defmodule Cure.StdlibTest do
  use ExUnit.Case, async: false

  # These are PURE CONSUMER tests: every assertion checks a runtime result the
  # canonical `Cure.Std.*` beam already produces. Under C1 the canonical stdlib
  # is loaded and made STICKY at suite startup (see `test/test_helper.exs`), so
  # this test must not self-compile a stdlib module — a fresh compile would try to
  # load over the sticky canonical name and fail with `:sticky_directory`, and
  # even absent stickiness it would clobber the shared slot other tests depend on.
  # Resolve the sticky canonical directly instead of building our own.
  defp std(name) do
    module = String.to_atom("Cure.Std." <> Macro.camelize(name))
    {:module, ^module} = :code.ensure_loaded(module)
    module
  end

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it erases
  # to the tagged pair `{:String, code_points}`. A BEAM caller of a compiled Cure
  # function speaks the erased language: neither an Elixir binary nor a bare
  # charlist is a Cure `String`, and only `Std.String`'s own private externs work
  # at `List(Char)`.
  defp cure_string(text), do: {:String, String.to_charlist(text)}

  # A `where Equatable(t)` function (e.g. `List.contains`) is elaborated in the
  # dictionary-passing model Idris/Agda use: the resolved `Equatable` instance is
  # threaded as a trailing runtime argument. At the element type `Int`, that
  # dictionary is the single-field record `Equatable(==)` — emitted as a tagged
  # tuple whose field is the *curried* `==` method (the callee applies it one
  # argument at a time). A BEAM caller of a generic constrained function supplies
  # this dictionary exactly as an internal Cure caller would; the tag itself is
  # inert (the callee projects field 1 positionally).
  defp equatable_int_dict do
    {:module, _} = :code.ensure_loaded(:"Cure.Std.Equatable")
    eq = fn a -> fn b -> apply(:"Cure.Std.Equatable", :"__impl_Equatable_Std.Int#Int_==", [a, b]) end end
    {:"Std.Equatable#Equatable", eq}
  end

  # ============================================================================
  # Std.Math
  # ============================================================================

  describe "Std.Math" do
    setup do
      %{m: std("math")}
    end

    test "abs", %{m: m} do
      assert m.abs(-5) == 5
      assert m.abs(5) == 5
      assert m.abs(0) == 0
    end

    test "sqrt", %{m: m} do
      assert m.sqrt(16.0) == 4.0
      assert m.sqrt(0.0) == 0.0
    end

    test "pow", %{m: m} do
      assert m.pow(2.0, 10.0) == 1024.0
    end

    test "log functions", %{m: m} do
      assert_in_delta m.log(1.0), 0.0, 0.001
      assert_in_delta m.log2(8.0), 3.0, 0.001
      assert_in_delta m.log10(100.0), 2.0, 0.001
    end

    test "ceil and floor", %{m: m} do
      assert m.ceil(3.2) == 4.0
      assert m.floor(3.9) == 3.0
    end

    test "round", %{m: m} do
      assert m.round(3.6) == 4
      assert m.round(3.4) == 3
    end

    test "pi", %{m: m} do
      assert_in_delta m.pi(), 3.14159, 0.001
    end

    test "max and min", %{m: m} do
      assert m.max(3, 7) == 7
      assert m.max(7, 3) == 7
      assert m.min(3, 7) == 3
      assert m.min(7, 3) == 3
    end

    test "clamp", %{m: m} do
      assert m.clamp(5, 1, 10) == 5
      assert m.clamp(-5, 1, 10) == 1
      assert m.clamp(15, 1, 10) == 10
    end

    test "sign", %{m: m} do
      assert m.sign(5) == 1
      assert m.sign(-5) == -1
      assert m.sign(0) == 0
    end

    test "negate", %{m: m} do
      assert m.negate(5) == -5
      assert m.negate(-3) == 3
    end

    test "is_even and is_odd", %{m: m} do
      assert m.is_even(4) == true
      assert m.is_even(3) == false
      assert m.is_odd(3) == true
      assert m.is_odd(4) == false
    end

    test "safe_div", %{m: m} do
      assert m.safe_div(10, 3) == 3
      assert m.safe_div(10, 0) == 0
    end
  end

  # ============================================================================
  # Std.Io
  # ============================================================================

  describe "Std.Io" do
    setup do
      %{m: std("io")}
    end

    test "int_to_string", %{m: m} do
      assert m.int_to_string(42) == cure_string("42")
      assert m.int_to_string(-1) == cure_string("-1")
    end

    test "atom_to_string", %{m: m} do
      assert m.atom_to_string(:hello) == cure_string("hello")
    end

    test "println returns unit", %{m: m} do
      assert m.println(cure_string("test")) == :unit
    end

    test "print returns unit", %{m: m} do
      assert m.print(cure_string("test")) == :unit
    end
  end

  # ============================================================================
  # Std.Core
  # ============================================================================

  describe "Std.Core -- utility functions" do
    setup do
      %{m: std("core")}
    end

    test "identity", %{m: m} do
      assert m.identity(42) == 42
      assert m.identity(:hello) == :hello
    end

    test "compose", %{m: m} do
      double = fn x -> x * 2 end
      inc = fn x -> x + 1 end
      f = m.compose(double, inc)
      assert f.(3) == 8
    end

    test "pipe", %{m: m} do
      assert m.pipe(5, fn x -> x * 3 end) == 15
    end

    test "apply", %{m: m} do
      assert m.apply(fn x -> x + 10 end, 5) == 15
    end

    test "const", %{m: m} do
      always_42 = m.const(42)
      assert always_42.(:anything) == 42
    end
  end

  describe "Std.Core -- boolean operations" do
    setup do
      %{m: std("core")}
    end

    test "bool_not", %{m: m} do
      assert m.bool_not(true) == false
      assert m.bool_not(false) == true
    end

    test "bool_and", %{m: m} do
      assert m.bool_and(true, true) == true
      assert m.bool_and(true, false) == false
      assert m.bool_and(false, true) == false
    end

    test "bool_or", %{m: m} do
      assert m.bool_or(false, false) == false
      assert m.bool_or(true, false) == true
      assert m.bool_or(false, true) == true
    end

    test "bool_xor", %{m: m} do
      assert m.bool_xor(true, false) == true
      assert m.bool_xor(false, true) == true
      assert m.bool_xor(true, true) == false
      assert m.bool_xor(false, false) == false
    end
  end

  describe "Std.Core -- comparison operations" do
    # `eq`/`ne`/`lt`/`le`/`gt`/`ge` no longer exist as named helpers: the
    # operators `==`/`!=`/`<`/`<=`/`>`/`>=` are the surface (equality is
    # structural; ordering routes through `Std.Comparable`). Only the
    # ordering-derived combinators `min`/`max`/`clamp` remain, now carrying a
    # `where Comparable(t)` constraint. Because that constraint compiles to an
    # interface-dictionary parameter, they can't be called directly from Elixir
    # at the surface arity — the dictionary is resolved by the elaborator at the
    # Cure call site. So exercise them through a small Cure program instead.
    defp run_core_fn(body) do
      src = """
      mod ComparisonProbe
        use Std.Core
        fn probe() -> Int = #{body}
      """

      {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
      result = mod.probe()
      # `ComparisonProbe` is an ad-hoc, non-canonical module name (never in the
      # sticky canonical set), so evicting it directly is safe and clobbers nothing.
      :code.purge(mod)
      :code.delete(mod)
      result
    end

    test "min and max" do
      assert run_core_fn("min(3, 7)") == 3
      assert run_core_fn("max(3, 7)") == 7
    end

    test "clamp" do
      assert run_core_fn("clamp(5, 1, 10)") == 5
      assert run_core_fn("clamp(-5, 1, 10)") == 1
      assert run_core_fn("clamp(15, 1, 10)") == 10
    end
  end

  describe "Std.Core -- Result type" do
    setup do
      %{m: std("core")}
    end

    test "ok and error constructors", %{m: m} do
      assert m.ok(5) == {:ok, 5}
      assert m.error(:bad) == {:error, :bad}
    end

    test "is_ok and is_error", %{m: m} do
      assert m.is_ok({:ok, 5}) == true
      assert m.is_ok({:error, :bad}) == false
      assert m.is_error({:error, :bad}) == true
      assert m.is_error({:ok, 5}) == false
    end

    test "unwrap_ok", %{m: m} do
      assert m.unwrap_ok({:ok, 42}, 0) == 42
      assert m.unwrap_ok({:error, :bad}, 0) == 0
    end

    test "unwrap_error", %{m: m} do
      assert m.unwrap_error({:error, :bad}, :default) == :bad
      assert m.unwrap_error({:ok, 42}, :default) == :default
    end

    test "map_ok", %{m: m} do
      assert m.map_ok({:ok, 5}, fn x -> x * 2 end) == {:ok, 10}
      assert m.map_ok({:error, :bad}, fn x -> x * 2 end) == {:error, :bad}
    end

    test "map_error", %{m: m} do
      assert m.map_error({:error, :bad}, fn _ -> :worse end) == {:error, :worse}
      assert m.map_error({:ok, 5}, fn _ -> :worse end) == {:ok, 5}
    end

    test "and_then", %{m: m} do
      assert m.and_then({:ok, 5}, fn x -> {:ok, x + 1} end) == {:ok, 6}
      assert m.and_then({:error, :bad}, fn x -> {:ok, x + 1} end) == {:error, :bad}
    end

    test "or_else", %{m: m} do
      assert m.or_else({:ok, 5}, fn _ -> {:ok, 0} end) == {:ok, 5}
      assert m.or_else({:error, :bad}, fn _ -> {:ok, 0} end) == {:ok, 0}
    end
  end

  describe "Std.Core -- Option type" do
    setup do
      %{m: std("core")}
    end

    test "some and none constructors", %{m: m} do
      assert m.some(42) == {:some, 42}
      assert m.none() == :none
    end

    test "is_some and is_none", %{m: m} do
      assert m.is_some({:some, 42}) == true
      assert m.is_some(:none) == false
      assert m.is_none(:none) == true
      assert m.is_none({:some, 42}) == false
    end

    test "unwrap", %{m: m} do
      assert m.unwrap({:some, 42}, 0) == 42
      assert m.unwrap(:none, 0) == 0
    end

    test "map_option", %{m: m} do
      assert m.map_option({:some, 5}, fn x -> x * 2 end) == {:some, 10}
      assert m.map_option(:none, fn x -> x * 2 end) == :none
    end

    test "flat_map_option", %{m: m} do
      assert m.flat_map_option({:some, 5}, fn x -> {:some, x * 2} end) == {:some, 10}
      assert m.flat_map_option(:none, fn x -> {:some, x * 2} end) == :none
    end

    test "option_or", %{m: m} do
      assert m.option_or({:some, 42}, 0) == 42
      assert m.option_or(:none, 0) == 0
    end
  end

  # ============================================================================
  # Std.List
  # ============================================================================

  describe "Std.List" do
    setup do
      %{m: std("list")}
    end

    test "length", %{m: m} do
      assert m.length([]) == 0
      assert m.length([1, 2, 3]) == 3
    end

    test "is_empty", %{m: m} do
      assert m.is_empty([]) == true
      assert m.is_empty([1]) == false
    end

    test "head", %{m: m} do
      assert m.head([1, 2, 3], 0) == 1
      assert m.head([], 0) == 0
    end

    test "tail", %{m: m} do
      assert [_, _] = m.tail([1, 2, 3])
      assert m.tail([]) == []
    end

    test "last", %{m: m} do
      assert m.last([1, 2, 3], 0) == 3
      assert m.last([], 0) == 0
    end

    test "cons", %{m: m} do
      assert [_, _, _] = m.cons(0, [1, 2])
      assert m.cons(0, [1, 2]) == [0, 1, 2]
    end

    test "append", %{m: m} do
      assert m.append([1, 2], [3, 4]) == [1, 2, 3, 4]
      assert m.append([], [1]) == [1]
      assert m.append([1], []) == [1]
    end

    test "concat", %{m: m} do
      assert m.concat([[1, 2], [3], [4, 5]]) == [1, 2, 3, 4, 5]
      assert m.concat([]) == []
    end

    test "reverse", %{m: m} do
      assert m.reverse([1, 2, 3]) == [3, 2, 1]
      assert m.reverse([]) == []
    end

    test "map", %{m: m} do
      assert m.map([1, 2, 3], fn x -> x * 2 end) == [2, 4, 6]
      assert m.map([], fn x -> x end) == []
    end

    test "filter", %{m: m} do
      assert m.filter([1, 2, 3, 4], fn x -> rem(x, 2) == 0 end) == [2, 4]
      assert m.filter([], fn _ -> true end) == []
    end

    test "foldl", %{m: m} do
      # sum via fold
      assert m.foldl([1, 2, 3], 0, fn x -> fn a -> a + x end end) == 6
    end

    test "foldr", %{m: m} do
      # cons via foldr builds the list in order
      result = m.foldr([1, 2, 3], [], fn x -> fn acc -> [x | acc] end end)
      assert result == [1, 2, 3]
    end

    test "flat_map", %{m: m} do
      assert m.flat_map([1, 2, 3], fn x -> [x, x * 10] end) == [1, 10, 2, 20, 3, 30]
    end

    test "zip_with", %{m: m} do
      result = m.zip_with([1, 2, 3], [10, 20, 30], fn a -> fn b -> a + b end end)
      assert result == [11, 22, 33]
    end

    test "nth", %{m: m} do
      assert m.nth([10, 20, 30], 0, -1) == 10
      assert m.nth([10, 20, 30], 2, -1) == 30
      assert m.nth([10, 20, 30], 5, -1) == -1
    end

    test "take", %{m: m} do
      assert m.take([1, 2, 3, 4, 5], 3) == [1, 2, 3]
      assert m.take([1, 2], 5) == [1, 2]
      assert m.take([1, 2, 3], 0) == []
    end

    test "drop", %{m: m} do
      assert m.drop([1, 2, 3, 4, 5], 2) == [3, 4, 5]
      assert m.drop([1, 2], 5) == []
      assert m.drop([1, 2, 3], 0) == [1, 2, 3]
    end

    test "contains", %{m: m} do
      dict = equatable_int_dict()
      assert m.contains([1, 2, 3], 2, dict) == true
      assert m.contains([1, 2, 3], 5, dict) == false
      assert m.contains([], 1, dict) == false
    end

    test "find", %{m: m} do
      assert m.find([1, 2, 3, 4], fn x -> x > 2 end, -1) == 3
      assert m.find([1, 2], fn x -> x > 5 end, -1) == -1
    end

    test "any", %{m: m} do
      assert m.any([1, 2, 3], fn x -> x > 2 end) == true
      assert m.any([1, 2, 3], fn x -> x > 5 end) == false
    end

    test "all", %{m: m} do
      assert m.all([1, 2, 3], fn x -> x > 0 end) == true
      assert m.all([1, 2, 3], fn x -> x > 1 end) == false
    end

    test "sum", %{m: m} do
      assert m.sum([1, 2, 3, 4, 5]) == 15
      assert m.sum([]) == 0
    end

    test "product", %{m: m} do
      assert m.product([1, 2, 3, 4]) == 24
      assert m.product([]) == 1
    end

    test "count", %{m: m} do
      assert m.count([1, 2, 3, 4, 5], fn x -> x > 2 end) == 3
    end
  end

  # ============================================================================
  # Std.String
  # ============================================================================

  describe "Std.String" do
    setup do
      %{m: std("string")}
    end

    test "length", %{m: m} do
      assert m.length(cure_string("hello")) == 5
      assert m.length(cure_string("")) == 0
    end

    test "is_empty", %{m: m} do
      assert m.is_empty(cure_string("")) == true
      assert m.is_empty(cure_string("x")) == false
    end

    test "concat", %{m: m} do
      assert m.concat(cure_string("hello"), cure_string(" world")) == cure_string("hello world")
    end

    test "from_int and from_atom", %{m: m} do
      assert m.from_int(42) == cure_string("42")
      assert m.from_atom(:hello) == cure_string("hello")
    end

    test "to_int", %{m: m} do
      assert m.to_int(cure_string("42")) == 42
    end

    test "existing and explicitly unsafe atom conversion", %{m: m} do
      assert m.to_existing_atom(cure_string("hello")) == :hello
      assert m.unsafe_to_atom(cure_string("hello")) == :hello
    end

    test "split", %{m: m} do
      # `split/2` is one-shot: `List(String)`, so each element is a nominal pair.
      assert m.split(cure_string("a,b,c"), cure_string(",")) == [
               cure_string("a"),
               cure_string("b,c")
             ]
    end

    test "repeat", %{m: m} do
      assert m.repeat(cure_string("ab"), 3) == cure_string("ababab")
    end

    test "trim", %{m: m} do
      assert m.trim(cure_string("  hello  ")) == cure_string("hello")
    end

    test "reverse", %{m: m} do
      assert m.reverse(cure_string("hello")) == cure_string("olleh")
      assert m.reverse(cure_string("")) == cure_string("")
    end
  end

  # Std.Pair was retired with the unified-tuple work (#23): `pair.cure` no
  # longer exists — a pair is the flat surface `Tuple(A, B)`, and its
  # combinators live on `Tuple`. The former Std.Pair describe block was removed.

  # ============================================================================
  # Std.System
  # ============================================================================

  describe "Std.System" do
    setup do
      %{m: std("system")}
    end

    test "timestamp_ms returns integer", %{m: m} do
      ts = m.timestamp_ms()
      assert is_integer(ts)
      assert ts > 0
    end

    # `Std.System.self/0` was deleted in `1f53615a` (the dependent-core
    # migration): a bare `Pid` carries no mailbox type, so process identity now
    # lives in the typed process algebra as `Std.Otp.self({m: Type}) ->
    # Effect(Pid(m))`. Pin the deletion so the untyped entry cannot come back.
    test "self is no longer an untyped Std.System entry", %{m: m} do
      refute function_exported?(m, :self, 0)
    end

    test "node returns atom", %{m: m} do
      assert is_atom(m.node())
    end

    test "otp_version returns a String", %{m: m} do
      # `:erlang.system_info(:otp_release)` answers a bare charlist; nominal
      # `String` erases to `{:String, chars}`, so the wrapper must rebuild it.
      assert {:String, chars} = m.otp_version()
      assert Enum.all?(chars, &is_integer/1)
      assert chars != []
    end

    test "cpu_count returns positive integer", %{m: m} do
      count = m.cpu_count()
      assert is_integer(count)
      assert count > 0
    end
  end
end
