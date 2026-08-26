defmodule Cure.Elab.ErasesDecoratorTest do
  @moduledoc """
  `@erases(<class>)` — an opaque FFI carrier declares the Erlang guard that recognises
  its erasure. An `opaque type` has no constructors, so its runtime shape cannot be
  inferred; it is asserted by the author of the sealed `unsafe` module. Spec §3.1.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive
  alias Cure.Elab.Program

  test "an @erases class is recorded on the opaque family" do
    src = """
    mod M
      @erases(:pid)
      opaque type Handle
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert %{opaque: true, erasure: :pid} = Inductive.get_family(env, :Handle)
  end

  test "an opaque type without @erases has no declared erasure" do
    src = """
    mod M
      opaque type Handle
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert %{opaque: true, erasure: nil} = Inductive.get_family(env, :Handle)
  end

  test "an unrecognised erasure class is a compile error" do
    src = """
    mod M
      @erases(:banana)
      opaque type Handle
    end
    """

    assert {:error, error} = Program.elaborate(src, file: "erasure.cure")
    assert {:unknown_erasure_class, :Handle, :banana} = Program.semantic_error(error)

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "erasure.cure", src)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.code == "E102"
    assert diagnostic.primary.span.start_line == 2
    assert diagnostic.primary.span.start_column == 11
    assert diagnostic.primary.span.end_column == 18
    assert rendered =~ "2 |   @erases(:banana)"
    assert rendered =~ "^^^^^^^ this runtime class is not supported"
    assert rendered =~ "Hint: Choose one of"
  end

  test "every malformed erasure form has a stable contextual rendering" do
    cases = [
      {"unknown.cure", "@erases(:banana)", "opaque type Handle",
       """
       -- UNKNOWN ERASURE CLASS `BANANA` [E102] -------------------------- unknown.cure

       `banana` is not a supported runtime class for opaque type `Handle`. Supported
       classes: pid, reference, integer, float, binary, atom, boolean, list.

       at unknown.cure:2:11
       2 |   @erases(:banana)
         |   ---------------- this is the complete erasure declaration
         |           ^^^^^^^ this runtime class is not supported
       3 |   opaque type Handle
         |               ------ this type receives the erasure declaration

       Hint: Choose one of pid, reference, integer, float, binary, atom, boolean, list
       """},
      {"missing.cure", "@erases()", "opaque type Handle",
       """
       -- ERASURE CLASS IS MISSING [E102] -------------------------------- missing.cure

       `@erases` on `Handle` needs exactly one atom naming the runtime class of this
       opaque carrier.

       at missing.cure:2:3
       2 |   @erases()
         |   ^^^^^^^^^ add one supported erasure class inside these parentheses
       3 |   opaque type Handle
         |               ------ this type receives the erasure declaration

       Hint: Add one of pid, reference, integer, float, binary, atom, boolean, list
       """},
      {"many.cure", "@erases(:pid, :reference)", "opaque type Handle",
       """
       -- ERASURE DECLARATION HAS TOO MANY CLASSES [E102] ------------------- many.cure

       `@erases` on `Handle` accepts one runtime class, but this declaration supplies
       2. One opaque carrier must have one unambiguous runtime representation.

       at many.cure:2:3
       2 |   @erases(:pid, :reference)
         |   ^^^^^^^^^^^^^^^^^^^^^^^^^ keep exactly one erasure class
       3 |   opaque type Handle
         |               ------ this type receives the erasure declaration

       Hint: Keep exactly one of pid, reference, integer, float, binary, atom, boolean, list
       """},
      {"bare.cure", "@erases(pid)", "opaque type Handle",
       """
       -- ERASURE CLASS MUST BE AN ATOM [E102] ------------------------------ bare.cure

       `@erases` on `Handle` expects an atom such as `:pid`; a bare name is not an
       erasure-class declaration.

       at bare.cure:2:11
       2 |   @erases(pid)
         |   ------------ this is the complete erasure declaration
         |           ^^^ write the runtime class as an atom
       3 |   opaque type Handle
         |               ------ this type receives the erasure declaration

       Hint: Write the class as an atom, for example `:pid`
       """},
      {"constructed.cure", "@erases(:pid)", "type Colour = Red | Green",
       """
       -- CONSTRUCTED TYPE CANNOT DECLARE AN ERASURE CLASS [E102] ---- constructed.cure

       `Colour` has constructors, so its runtime representation is already determined
       by those constructors. `@erases` is only valid on a constructor-less `opaque
       type`.

       at constructed.cure:2:3
       2 |   @erases(:pid)
         |   ^^^^^^^^^^^^^ remove this erasure declaration
       3 |   type Colour = Red | Green
         |        ------ this type receives the erasure declaration

       Hint: Remove `@erases`, or make this a constructor-less `opaque type`
       """}
    ]

    Enum.each(cases, fn {file, decorator, declaration, expected} ->
      source = "mod M\n  #{decorator}\n  #{declaration}\nend\n"
      assert {:error, error} = Program.elaborate(source, file: file)
      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, file, source)

      assert Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80) ==
               expected |> String.trim_leading() |> String.trim_trailing()
    end)

    repaired_sources = [
      "mod M\n  @erases(:pid)\n  opaque type Handle\nend\n",
      "mod M\n  type Colour = Red | Green\nend\n"
    ]

    Enum.each(repaired_sources, fn source ->
      assert {:ok, _env} = Program.elaborate(source, file: "repaired_erasure.cure")
    end)
  end

  test "the unrecognised-class error names the admissible set (spec §4 item 2)" do
    error = {:unknown_erasure_class, :Handle, :banana}
    message = Cure.Compiler.Errors.format_error(error, "test.cure")

    for class <- [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list] do
      assert message =~ Atom.to_string(class),
             "the rendered message must name every admissible class; missing #{class}:\n#{message}"
    end
  end

  test "@erases on a type WITH constructors is a compile error" do
    src = """
    mod M
      @erases(:pid)
      type Colour = Red | Green
    end
    """

    assert {:error, error} = Program.elaborate(src)
    assert {:erases_on_non_opaque, :Colour} = Program.semantic_error(error)
  end

  # A malformed `@erases(...)` shape must not be silently treated as "no erasure
  # declared" — that would let a typo (missing colon, wrong arity) through with zero
  # diagnostic, and the carrier would fail much later inside union discrimination with
  # an unrelated `:unsupported`-class message instead of naming the real cause.
  test "@erases() with no argument is a compile error, not a silently-absent declaration" do
    src = """
    mod M
      @erases()
      opaque type Handle
    end
    """

    assert {:error, error} = Program.elaborate(src)
    assert {:unknown_erasure_class, :Handle, _} = Program.semantic_error(error)
  end

  test "@erases with more than one argument is a compile error" do
    src = """
    mod M
      @erases(:pid, :reference)
      opaque type Handle
    end
    """

    assert {:error, error} = Program.elaborate(src)
    assert {:unknown_erasure_class, :Handle, _} = Program.semantic_error(error)
  end

  test "@erases(bare_identifier) without the atom colon is a compile error" do
    src = """
    mod M
      @erases(pid)
      opaque type Handle
    end
    """

    assert {:error, error} = Program.elaborate(src)
    assert {:unknown_erasure_class, :Handle, _} = Program.semantic_error(error)
  end
end
