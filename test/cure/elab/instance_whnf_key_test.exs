defmodule Cure.Elab.InstanceWhnfKeyTest do
  @moduledoc """
  Phase 1: the coherence key of an instance head is computed by whnf-ing the
  elaborated Core head, so a transparent type synonym files under the same key
  as the type it unfolds to (via the kernel's δ-reduction, not surface spelling).

  Note: the instance-method bodies use `a == b` rather than the primitive
  `Std.Builtin.int_eq`/`struct_eq` spelling — surface-callable builtins land in a
  later task. `==` already lowers correctly (Int → int_eq, Color → struct_eq), so
  these programs compile today and exercise exactly the coherence KEY this task
  changes.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "an instance for a transparent synonym collides with the underlying type" do
    src = """
    mod M
      use Std.Equatable
      typealias MyInt = Int
      implementation Equatable for MyInt
        fn `==`(a: MyInt, b: MyInt) -> Bool = a == b
    end
    """

    # Std.Equatable already provides `Equatable for Int`. Registering a second
    # anonymous instance for `MyInt` (which whnf's to Int) must collide.
    assert {:error, {:overlapping_instance, %{interface: :Equatable, head: :"Std.Int#Int"}}} =
             Program.elaborate(src)
  end

  test "an instance for a genuine data type registers under its family name" do
    src = """
    mod M
      use Std.Equatable
      type Color = Red | Green | Blue
      implementation Equatable for Color
        fn `==`(a: Color, b: Color) -> Bool = a == b
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # A CHAIN of transparent synonyms must resolve to the underlying type's key, not just a
  # single hop. `MyInt2 -> MyInt -> Int` are all non-recursive, so each certifies the moment it
  # is elaborated and the certified δ-gate in `whnf_value` unfolds the whole chain — exactly what
  # the dispatch classifier does on demand. Registration keying `MyInt2` under `:"Std.Int#Int"`
  # (and so colliding with `Std.Equatable`'s `Int` instance) is the observable proof the two paths agree,
  # which is why Finding 1's claimed registration/dispatch certification asymmetry does not arise
  # for any surface-reachable synonym.
  test "a two-hop transparent synonym chain collides under the underlying type" do
    src = """
    mod M
      use Std.Equatable
      typealias MyInt = Int
      typealias MyInt2 = MyInt
      implementation Equatable for MyInt2
        fn `==`(a: MyInt2, b: MyInt2) -> Bool = a == b
    end
    """

    assert {:error, {:overlapping_instance, %{interface: :Equatable, head: :"Std.Int#Int"}}} =
             Program.elaborate(src)
  end

  # A non-primitive head shape (here a function type `(Int) -> Int`) whnf's to a `{:vpi, …}`
  # Value, not an atom. The head-atom reader must map it to a descriptive ATOM (`:Function`);
  # returning the raw Core tuple instead crashed `mangled_name`'s string interpolation with
  # `Protocol.UndefinedError (String.Chars not implemented for Tuple)`. Successful elaboration is
  # the proof the coherence key is a well-typed atom for a higher-order head.
  #
  # The body is the structural primitive `struct_eq`, not `a == b`: under the sole-route
  # `==` (Task 2.6) an operator lowers to the `Equatable` method for the operand's head, and a
  # function-type operand has no structurally-comparable `==` to dispatch to (functions are not
  # structurally equal). Spelling `struct_eq` directly keeps the test's subject — the coherence
  # KEY of a higher-order head — while giving the method a body that stands on its own.
  test "a function-type head yields an atom key, not a raw Core term" do
    src = """
    mod M
      use Std.Equatable
      typealias IntToInt = (Int) -> Int
      implementation Equatable for IntToInt
        fn `==`(a: IntToInt, b: IntToInt) -> Bool = Std.Builtin.struct_eq(IntToInt, a, b)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
