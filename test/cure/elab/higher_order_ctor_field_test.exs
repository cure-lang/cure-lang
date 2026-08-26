defmodule Cure.Elab.HigherOrderCtorFieldTest do
  @moduledoc """
  A constructor field may itself be a FUNCTION type when parenthesised:
  `MkPid : ((m) -> Response) -> Pid(m)`. The `parse_type_atom` grammar the GADT
  ctor-signature parser uses is deliberately arrow-free (so the ctor's own arrow
  chain separates fields), but a `(...)`-GROUPED function type is unambiguous — the
  `)` bounds it — so it is now absorbed as a single field. Needed for the OTP
  metatheory obligation (2): a process handle that CARRIES its handler.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a parenthesised function-typed constructor field parses and elaborates" do
    src = """
    mod HofCtor
      type Response = Ack
      type Msg = Inc | Dec
      type Pid(m: Type) indices ()
        MkPid : ((m) -> Response) -> Pid(m)
      fn spawn_actor({m: Type}, handler: (m) -> Response) -> Pid(m) = MkPid(handler)
      fn post({m: Type}, p: Pid(m), msg: m) -> Response = match p
        MkPid(h) -> h(msg)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a multi-arrow parenthesised field: ((a) -> (b) -> c)" do
    src = """
    mod HofCtor2
      type A = MkA
      type B = MkB
      type C = MkC
      type Box(x: Type) indices ()
        MkBox : ((A) -> (B) -> C) -> Box(x)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a plain parenthesised (non-function) field type is unchanged" do
    src = """
    mod PlainParen
      type A = MkA
      type Box indices ()
        MkBox : (A) -> Box
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
