defmodule Cure.Stdlib.DependentRegexAtomicTest do
  use ExUnit.Case, async: false

  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexAtomic
      use Std.Regex

      fn ordinary_group() -> Option(String) = parse_full(/((?:a|ab)c)/, "abc")
      fn atomic_group() -> Option(String) = parse_full(/((?>a|ab)c)/, "abc")
      fn outer_alternative() -> Option(String) = parse_full(/((?>a|ab)c|abc)/, "abc")
      fn nested_atomic() -> Option(String) = parse_full(/((?>(?>a|ab)c|ab)c)/, "abc")
      fn nullable_atomic() -> Option(String) = parse_full(/((?>a*)a)/, "a")
      fn ordinary_plus() -> Option(String) = parse_full(/(a+a)/, "aa")
      fn possessive_plus() -> Option(String) = parse_full(/(a++a)/, "aa")
      fn ordinary_star() -> Option(String) = parse_full(/(a*a)/, "aa")
      fn possessive_star() -> Option(String) = parse_full(/(a*+a)/, "aa")
      fn ordinary_optional() -> Option(String) = parse_full(/(a?a)/, "a")
      fn possessive_optional() -> Option(String) = parse_full(/(a?+a)/, "a")
      fn ordinary_bounded() -> Option(String) = parse_full(/(a{2,3}a)/, "aaa")
      fn possessive_bounded() -> Option(String) = parse_full(/(a{2,3}+a)/, "aaa")
      fn ordinary_at_least() -> Option(String) = parse_full(/(a{2,}a)/, "aaa")
      fn possessive_at_least() -> Option(String) = parse_full(/(a{2,}+a)/, "aaa")
      fn ordinary_prefix() -> Option(Tuple(String, String)) = parse_prefix(/(a*a)/, "aa")
      fn possessive_prefix() -> Option(Tuple(String, String)) = parse_prefix(/(a*+a)/, "aa")

      fn direct_atomic() -> Bool =
        let a = AtomicRuntimeLeaf(PatternPredicate(fn(char) -> char == 'a'))
        let b = AtomicRuntimeLeaf(PatternPredicate(fn(char) -> char == 'b'))
        let c = AtomicRuntimeLeaf(PatternPredicate(fn(char) -> char == 'c'))
        let ab = AtomicRuntimeConcat(a, b)
        let choice = AtomicRuntimeAlternate(a, ab, false)
        let plan = AtomicRuntimeConcat(AtomicRuntimeScope(choice), c)
        let machine = atomic_runtime_machine_from_plan(plan)
        atomic_runtime_accepts(thompson_state_count(atomic_plan_compilation(plan)), machine, subject_initial_position(), Std.String.characters("abc"), [])

      fn direct_nested_atomic() -> Bool =
        let a = AtomicRuntimeLeaf(PatternPredicate(fn(char) -> char == 'a'))
        let b = AtomicRuntimeLeaf(PatternPredicate(fn(char) -> char == 'b'))
        let c = AtomicRuntimeLeaf(PatternPredicate(fn(char) -> char == 'c'))
        let inner = AtomicRuntimeScope(AtomicRuntimeAlternate(a, AtomicRuntimeConcat(a, b), false))
        let left = AtomicRuntimeConcat(inner, c)
        let right = AtomicRuntimeConcat(a, b)
        let outer = AtomicRuntimeScope(AtomicRuntimeAlternate(left, right, false))
        let plan = AtomicRuntimeConcat(outer, c)
        let machine = atomic_runtime_machine_from_plan(plan)
        atomic_runtime_accepts(thompson_state_count(atomic_plan_compilation(plan)), machine, subject_initial_position(), Std.String.characters("abc"), [])

      fn commitment_depth_relation() -> Bool = match atomic_commit_disposition(Z(), Z())
        AtomicCommitBlocks(_) -> match atomic_commit_disposition(Z(), S(Z()))
          AtomicCommitEscapes(_) -> match atomic_commit_disposition(S(Z()), Z())
            AtomicCommitBlocks(_) -> match atomic_commit_disposition(S(Z()), S(Z()))
              AtomicCommitBlocks(_) -> true
              AtomicCommitEscapes(_) -> false
            AtomicCommitEscapes(_) -> false
          AtomicCommitBlocks(_) -> false
        AtomicCommitEscapes(_) -> false

    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "atomic groups commit to their first successful exit", %{runtime_module: module} do
    assert apply(module, :ordinary_group, []) == {:some, cure_string(~c"abc")}
    assert apply(module, :atomic_group, []) == :none
    assert apply(module, :outer_alternative, []) == {:some, cure_string(~c"abc")}
    assert apply(module, :nested_atomic, []) == {:some, cure_string(~c"abc")}
    assert apply(module, :nullable_atomic, []) == :none
  end

  test "possessive quantifiers do not backtrack", %{runtime_module: module} do
    assert apply(module, :ordinary_plus, []) == {:some, cure_string(~c"aa")}
    assert apply(module, :possessive_plus, []) == :none
    assert apply(module, :ordinary_star, []) == {:some, cure_string(~c"aa")}
    assert apply(module, :possessive_star, []) == :none
    assert apply(module, :ordinary_optional, []) == {:some, cure_string(~c"a")}
    assert apply(module, :possessive_optional, []) == :none
    assert apply(module, :ordinary_bounded, []) == {:some, cure_string(~c"aaa")}
    assert apply(module, :possessive_bounded, []) == :none
    assert apply(module, :ordinary_at_least, []) == {:some, cure_string(~c"aaa")}
    assert apply(module, :possessive_at_least, []) == :none
  end

  test "prefix parsing observes atomic commitment", %{runtime_module: module} do
    assert apply(module, :ordinary_prefix, []) ==
             {:some, {cure_string(~c"aa"), cure_string([])}}

    assert apply(module, :possessive_prefix, []) == :none
  end

  test "runtime atomic plan commits independently of literal expansion", %{runtime_module: module} do
    refute apply(module, :direct_atomic, [])
    assert apply(module, :direct_nested_atomic, [])
    assert apply(module, :commitment_depth_relation, [])
  end
end
