defmodule Cure.REPLTest do
  # async: false -- the `describe "definitions"` block loads the shared
  # `:"Cure.Repl.Session"` BEAM module into the VM, which is process-global.
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Cure.REPL
  alias Cure.REPL.Session

  describe "input classification" do
    test "complete inputs" do
      assert :complete = REPL.__classify_input__("1 + 1")
      assert :complete = REPL.__classify_input__("foo(bar)")
      assert :complete = REPL.__classify_input__("[1, 2, 3]")
    end

    test "lines ending with continuation tokens" do
      assert :continue = REPL.__classify_input__("if x > 0 then")
      assert :continue = REPL.__classify_input__("fn(x) ->")
      assert :continue = REPL.__classify_input__("let x =")
      assert :continue = REPL.__classify_input__("if x > 0 then y else")
    end

    test "match-style with pipe" do
      assert :continue = REPL.__classify_input__("match x |")
    end

    test "trailing comma and open paren" do
      assert :continue = REPL.__classify_input__("f(a,")
      assert :continue = REPL.__classify_input__("f(")
    end

    test "lone block-opening keywords are continuations" do
      for kw <-
            ~w(match pickup if case cond try fn do let mod rec type interface implementation proto impl proof actor fsm) do
        assert :continue = REPL.__classify_input__(kw),
               "expected lone #{inspect(kw)} to be classified as continuation"
      end
    end

    test "trailing whitespace after a continuation token still continues" do
      assert :continue = REPL.__classify_input__("if x > 0 then  ")
      assert :continue = REPL.__classify_input__("match  ")
    end
  end

  describe "multiline auto-detection" do
    test "`match foo` (scrutinee, no arms) is treated as incomplete" do
      assert REPL.__incomplete__?("match foo", "match foo")
    end

    test "a balanced complete expression is not incomplete" do
      refute REPL.__incomplete__?("1 + 1", "1 + 1")
      refute REPL.__incomplete__?("foo(bar)", "foo(bar)")
    end

    test "unbalanced brackets keep us continuing" do
      assert REPL.__incomplete__?("[1, 2,", "[1, 2,")
      assert REPL.__incomplete__?("f(a", "f(a")
    end

    test "submitting `match foo` accumulates instead of dispatching" do
      state = REPL.__submit__(REPL.__new_state__(), "match foo")
      assert state.input_buffer == ["match foo"]
      # The prompt counter is only bumped on dispatch.
      assert state.n == 1
    end

    test "submitting a lone `if` accumulates instead of dispatching" do
      state = REPL.__submit__(REPL.__new_state__(), "if")
      assert state.input_buffer == ["if"]
    end

    test "a match nested in a function header remains open for indented arms" do
      line = "fn choose(x: Bool) -> Int = match x"
      state = REPL.__submit__(REPL.__new_state__(), line)
      assert state.input_buffer == [line]
      assert state.n == 1
    end

    test "indented clauses and blank lines remain buffered until explicit submission" do
      state =
        REPL.__new_state__()
        |> REPL.__submit__("fn choose(x: Bool) -> Int = match x")
        |> REPL.__submit__("  True() -> 1")
        |> REPL.__submit__("")
        |> REPL.__submit__("  False() -> 0")

      assert state.input_buffer == [
               "fn choose(x: Bool) -> Int = match x",
               "  True() -> 1",
               "",
               "  False() -> 0"
             ]

      {state, stdout, stderr} = submit_capture(state, ";;")
      assert state.input_buffer == []
      assert stdout =~ "defined choose/1"
      assert stderr == ""
    end

    test "proof authoring keywords are continuation cues" do
      for line <- ["proof chain", "induction n", "have step", "because p", "rewrite using p", "simplify"] do
        assert :continue = REPL.__classify_input__(line)
      end

      assert :continue = REPL.__classify_input__("case S(k, ih) =>")
    end
  end

  describe "force-newline (Alt+Enter)" do
    test "appends the line to input_buffer even on a complete expression" do
      state = REPL.__continue__(REPL.__new_state__(), "1 + 1")
      assert state.input_buffer == ["1 + 1"]
      assert state.n == 1
    end

    test "force-newline on an empty fresh prompt is a no-op" do
      state = REPL.__continue__(REPL.__new_state__(), "")
      assert state.input_buffer == []
    end

    test "force-newline composes with subsequent submit to dispatch" do
      state =
        REPL.__new_state__()
        |> REPL.__continue__("let a = 1")
        |> REPL.__continue__("let b = a + 1")

      assert state.input_buffer == ["let a = 1", "let b = a + 1"]

      # A bare `b` would normally be classified as :complete, but
      # because the input_buffer is non-empty it joins and dispatches.
      {state, stdout, _stderr} = submit_capture(state, "b")
      assert state.input_buffer == []
      assert stdout =~ "=> 2"
    end
  end

  describe "error_device option" do
    test "defaults to :stderr so the standalone REPL keeps stream separation" do
      state = REPL.__new_state__()

      assert state.error_device == :stderr

      captured =
        capture_io(:stderr, fn ->
          REPL.__render_reason_error__(state, "kaboom")
        end)

      assert captured =~ "COMMAND FAILED [E098]"
      assert captured =~ "repl failed: kaboom"
      refute captured =~ "error: --"
    end

    test ":stdio routes diagnostics through the group leader" do
      state = REPL.__new_state__(error_device: :stdio)

      captured =
        capture_io(fn ->
          REPL.__render_reason_error__(state, "kaboom")
        end)

      assert captured =~ "COMMAND FAILED [E098]"
    end

    test "line-based warnings retain authored source and caret context" do
      state = REPL.__new_state__()
      source = "fn first() = 1\nfn second() = 2\n"

      warning =
        {:compiler_warning,
         %{
           file: "session.cure",
           line: 2,
           message: "this definition is unused"
         }}

      captured =
        capture_io(:stderr, fn ->
          REPL.__render_reason_error__(state, warning, "session.cure", source)
        end)

      assert captured =~ "COMPILER WARNING [W000]"
      assert captured =~ "fn second() = 2"
      assert captured =~ "^"
      assert captured =~ "this definition is unused"
    end

    test "evaluation failures render the synthesized source instead of a blank evidence line" do
      {_state, _stdout, stderr} = submit_capture(REPL.__new_state__(), "missing_repl_name")

      assert stderr =~ "missing_repl_name"
      assert stderr =~ "repl/Repl.M1.cure"
      assert stderr =~ "^"
      refute stderr =~ ~r/\d+ \|\s*\n\s*\^/
    end
  end

  describe "definitions" do
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "fn submission installs the definition and prints `defined name/arity`" do
      {state, stdout, _stderr} =
        submit_capture(REPL.__new_state__(), "fn add(a: Int, b: Int) -> Int = a + b")

      assert [%{key: {:fn, "add", 2, :public}}] = state.defs
      assert stdout =~ "defined add/2"
      assert function_exported?(Session.module_atom(), :add, 2)
    end

    test "follow-up expression can call the user-defined function" do
      state =
        REPL.__new_state__()
        |> submit("fn add(a: Int, b: Int) -> Int = a + b")

      {_state, stdout, _stderr} = submit_capture(state, "add(2, 3)")
      assert stdout =~ "=> 5"
    end

    test "proof decorators and generated defining equations survive session inlining" do
      state = REPL.__new_state__() |> submit(":use Std.Equivalent")

      state =
        state
        |> submit("type Nat3 = Z3 | S3(Nat3)")
        |> submit("fn add3(x: Nat3, y: Nat3) -> Nat3 = match x\n  Z3() -> y\n  S3(k) -> S3(add3(k, y))")

      theorem =
        "@lemma\nfn add3_succ_eq(k: Nat3, y: Nat3) -> Equivalent(Nat3, add3(S3(k), y), S3(add3(k, y))) = add3.S3(k, y)"

      {state, stdout, stderr} = submit_capture(state, theorem)
      assert stderr == ""
      assert stdout =~ "defined add3_succ_eq/2"

      {_state, stdout, stderr} = submit_capture(state, "add3(S3(Z3()), S3(Z3()))")
      assert stdout =~ "{:S3, {:S3, :Z3}}"
      assert stderr == ""
    end

    test "redefining a function replaces the previous entry in place" do
      state =
        REPL.__new_state__()
        |> submit("fn answer() -> Int = 1")
        |> submit("fn other() -> Int = 2")

      assert [%{key: {:fn, "answer", 0, :public}}, %{key: {:fn, "other", 0, :public}}] =
               state.defs

      {state, stdout, _stderr} = submit_capture(state, "fn answer() -> Int = 42")

      assert stdout =~ "redefined answer/0"

      assert [%{key: {:fn, "answer", 0, :public}, source: "fn answer() -> Int = 42"}, _other] =
               state.defs

      {_state, stdout, _stderr} = submit_capture(state, "answer()")
      assert stdout =~ "=> 42"
    end

    test ":reset clears defs and unloads the session module" do
      state =
        REPL.__new_state__()
        |> submit("fn ping() -> Int = 1")

      assert [_] = state.defs
      assert :code.is_loaded(Session.module_atom())

      state = REPL.__submit__(state, ":reset")

      assert state.defs == []
      refute :code.is_loaded(Session.module_atom())
    end

    test ":defs command lists installed definitions" do
      state =
        REPL.__new_state__()
        |> submit("fn foo(x: Int) -> Int = x")
        |> submit("type Color = Red | Green")

      {_state, stdout, _stderr} = submit_capture(state, ":defs")

      assert stdout =~ "session definitions (2)"
      assert stdout =~ "foo/1"
      assert stdout =~ "type Color"
    end

    test ":t uses the dependent elaborator and prints the inferred type" do
      {_state, stdout, stderr} = submit_capture(REPL.__new_state__(), ":t 1 + 2")

      assert stdout =~ "1 + 2 : Int"
      assert stderr == ""
    end

    test ":t can inspect expressions using session definitions" do
      state =
        REPL.__new_state__()
        |> submit("fn add(a: Int, b: Int) -> Int = a + b")

      {_state, stdout, stderr} = submit_capture(state, ":type add(2, 3)")
      assert stdout =~ "add(2, 3) : Int"
      assert stderr == ""
    end

    test ":effects distinguishes pure expressions" do
      {_state, stdout, stderr} = submit_capture(REPL.__new_state__(), ":effects 1 + 2")
      assert stdout =~ "1 + 2 : pure"
      assert stderr == ""
    end

    test ":printdef prints the authored session definition" do
      state = submit(REPL.__new_state__(), "fn double(x: Int) -> Int = x + x")
      {_state, stdout, stderr} = submit_capture(state, ":printdef double")
      assert stdout =~ "fn double(x: Int) -> Int = x + x"
      assert stderr == ""
    end

    test ":total reports the kernel certificate for a session function" do
      state = submit(REPL.__new_state__(), "fn identity(x: Int) -> Int = x")
      {_state, stdout, stderr} = submit_capture(state, ":total identity")
      assert stdout =~ "identity/1 is total"
      assert stderr == ""
    end

    test ":apropos searches stdlib declaration names" do
      {_state, stdout, stderr} = submit_capture(REPL.__new_state__(), ":apropos map")
      assert stdout =~ "Std.List.map/2"
      assert stderr == ""
    end

    test ":holes reports typed goals retained from session definitions" do
      {state, stdout, stderr} =
        submit_capture(REPL.__new_state__(), "fn unfinished() -> Int = ?")

      assert stdout =~ "defined unfinished/0 (with holes)"
      assert stderr == ""
      assert [%{goal: _, context: []}] = state.holes

      {_state, stdout, stderr} = submit_capture(state, ":holes")
      assert stdout =~ "unfinished"
      assert stdout =~ "Int"
      assert stderr == ""
    end
  end

  describe "bare `use` sugar" do
    # Regression for the prod REPL: a bare `use Std.List` used to
    # compile as an expression body, collapse to `:undefined`, and
    # leave the user staring at `=> :undefined`. Now it routes
    # through the `:use` meta-command and shows the real
    # "imported ..." message.
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "a bare `use Std.List` installs the import like `:use Std.List`" do
      {state, stdout, _stderr} =
        submit_capture(REPL.__new_state__(), "use Std.List")

      assert stdout =~ "imported Std.List"
      assert "Std.List" in state.uses
      refute stdout =~ ":undefined"
    end

    test "strips a leading `Cure.` prefix like the meta-command does" do
      {state, stdout, _stderr} =
        submit_capture(REPL.__new_state__(), "use Cure.Std.List")

      assert stdout =~ "imported Std.List"
      assert "Std.List" in state.uses
    end

    test "multi-item `use Std.{List, Map}` routes through the meta-command path" do
      # The meta-command does not currently destructure the brace
      # form, but sending it through the right dispatcher surfaces a
      # sensible error instead of silently evaluating to :undefined.
      {_state, stdout, stderr} =
        submit_capture(REPL.__new_state__(), "use Std.{List, Map}")

      refute stdout =~ ":undefined"
      assert stdout <> stderr =~ ~r/imported|no stdlib module/
    end

    test "leaves genuine expressions like `useful_thing(1)` alone" do
      # `useful_thing` is not a `use` statement; it must still reach
      # the evaluator (which will error on the unresolved name).
      {_state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), "useful_thing(1)")

      # Either a type/compile error is surfaced, or (if the env
      # happens to resolve it) the evaluator runs; the only thing we
      # assert is that we did NOT short-circuit into :use.
      refute stderr =~ "no stdlib module"
    end
  end

  describe ":let meta-command" do
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "installs the bound value as a zero-arg session fn" do
      {state, stdout, _stderr} =
        submit_capture(REPL.__new_state__(), ":let answer = 42")

      assert [%{key: {:fn, "answer", 0, :public}, source: "fn answer() = 42"}] =
               state.defs

      assert stdout =~ "pinned answer/0"
      assert function_exported?(Session.module_atom(), :answer, 0)
      # `apply/3` keeps the dynamic call off the compiler's radar so it does
      # not warn about `:"Cure.Repl.Session"` (which is defined at runtime).
      assert 42 = apply(Session.module_atom(), :answer, [])
    end

    test "let-bound value is reachable from a follow-up expression" do
      state =
        REPL.__new_state__()
        |> submit(":let a = 1")
        |> submit(":let b = a() + 1")

      {_state, stdout, _stderr} = submit_capture(state, "b()")
      assert stdout =~ "=> 2"
    end

    test "redefining a pinned binding replaces the entry in place" do
      state =
        REPL.__new_state__()
        |> submit(":let x = 1")

      {state, stdout, _stderr} = submit_capture(state, ":let x = 99")

      assert stdout =~ "redefined x/0"

      assert [%{key: {:fn, "x", 0, :public}, source: "fn x() = 99"}] = state.defs

      {_state, stdout, _stderr} = submit_capture(state, "x()")
      assert stdout =~ "=> 99"
    end

    test "rejects invalid identifiers" do
      {state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), ":let 1bad = 42")

      assert state.defs == []
      assert stderr =~ "invalid binding name"
    end

    test "reports a usage error on missing '='" do
      {state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), ":let foo")

      assert state.defs == []
      assert stderr =~ "usage: :let name = expr"
    end

    test "reports a usage error on an empty right-hand side" do
      {state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), ":let foo =")

      assert state.defs == []
      assert stderr =~ "usage: :let name = expr"
    end

    test ":defs lists pinned let bindings alongside explicit declarations" do
      state =
        REPL.__new_state__()
        |> submit(":let pi = 3.14")
        |> submit("fn square(x: Int) -> Int = x * x")

      {_state, stdout, _stderr} = submit_capture(state, ":defs")

      assert stdout =~ "session definitions (2)"
      assert stdout =~ "pi/0"
      assert stdout =~ "square/1"
    end
  end

  describe ":edit meta-command" do
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "runs $EDITOR and dispatches its contents as a fresh submission" do
      script_path = write_editor_stub("fn pinned() -> Int = 7")
      System.put_env("EDITOR", script_path)

      try do
        {state, stdout, _stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stdout =~ "defined pinned/0"
        assert [%{key: {:fn, "pinned", 0, :public}}] = state.defs
        assert state.input_buffer == []
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end

    test "an empty editor buffer clears input_buffer and reports the no-op" do
      script_path = write_editor_stub("")
      System.put_env("EDITOR", script_path)

      try do
        {state, stdout, _stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stdout =~ "empty buffer"
        assert state.input_buffer == []
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end

    test "a multi-line editor buffer evaluates the whole body, not just the first line" do
      # Regression test: the old evaluator spliced the source inline after
      # `fn main() = `, which left every line past the first at
      # column 0 -- siblings of `mod` instead of body statements of
      # `main/0`. Indenting the body under `main/0` lets the parser read
      # the whole thing as a block, so the REPL prints the result of the
      # final expression instead of only the first.
      script_path = write_editor_stub("let a = 1\nlet b = a + 1\nb")
      System.put_env("EDITOR", script_path)

      try do
        {_state, stdout, _stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stdout =~ "=> 2"
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end

    test "a non-zero editor exit discards the buffer without submitting" do
      # The script exits non-zero *after* overwriting the tmp file, so we
      # verify the guard triggers on exit_code alone.
      script_path =
        write_editor_stub_raw("""
        #!/bin/sh
        echo 'fn would_define() -> Int = 1' > "$1"
        exit 3
        """)

      System.put_env("EDITOR", script_path)

      try do
        {state, _stdout, stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stderr =~ "editor exited with status 3"
        assert state.defs == []
        assert state.input_buffer == []
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end
  end

  describe "stdlib preload options (Cure.toml [compiler] stdlib_path)" do
    # Regression: setting `[compiler] stdlib_path` in Cure.toml had no
    # effect in the REPL -- only `$CURE_LIB` did -- so loading a file that
    # `use`d a stdlib module raised `:missing_stdlib_module`. The REPL now
    # threads the project's stdlib_path into the preload, like the CLI.
    @tag :tmp_dir
    test "injects :stdlib_ebin from [compiler] stdlib_path", %{tmp_dir: tmp} do
      ebin = Path.join(tmp, "ebin")

      File.write!(Path.join(tmp, "Cure.toml"), """
      [project]
      name = "demo"
      version = "0.1.0"

      [compiler]
      type_check = false
      stdlib_path = "#{ebin}"
      """)

      opts = REPL.__stdlib_preload_opts__([kind: :all], tmp)

      assert Keyword.get(opts, :stdlib_ebin) == ebin
      # Base opts are preserved.
      assert Keyword.get(opts, :kind) == :all
    end

    @tag :tmp_dir
    test "falls back to $CURE_LIB when stdlib_path is absent", %{tmp_dir: tmp} do
      previous = System.get_env("CURE_LIB")

      try do
        System.put_env("CURE_LIB", "/fallback/ebin")

        File.write!(Path.join(tmp, "Cure.toml"), """
        [project]
        name = "demo"
        version = "0.1.0"

        [compiler]
        type_check = false
        """)

        opts = REPL.__stdlib_preload_opts__([kind: :all], tmp)
        assert Keyword.get(opts, :stdlib_ebin) == "/fallback/ebin"
      after
        restore_env("CURE_LIB", previous)
      end
    end

    @tag :tmp_dir
    test "omits :stdlib_ebin when neither Cure.toml nor $CURE_LIB is set", %{tmp_dir: tmp} do
      previous = System.get_env("CURE_LIB")

      try do
        System.delete_env("CURE_LIB")
        # `tmp` has no Cure.toml, so project load fails and CURE_LIB is unset.
        opts = REPL.__stdlib_preload_opts__([kind: :all], tmp)
        refute Keyword.has_key?(opts, :stdlib_ebin)
        assert Keyword.get(opts, :kind) == :all
      after
        restore_env("CURE_LIB", previous)
      end
    end
  end

  defp restore_env(key, nil), do: System.delete_env(key)
  defp restore_env(key, val), do: System.put_env(key, val)

  # Feed `line` through the REPL pipeline, silencing any captured IO. Used
  # for setup steps whose stdout/stderr is not the subject of the
  # assertion.
  defp submit(state, line) do
    {next_state, _stdout, _stderr} = submit_capture(state, line)
    next_state
  end

  # Feed `line` through the REPL pipeline and return the updated state
  # along with the captured stdout and stderr.
  defp submit_capture(state, line) do
    parent = self()
    ref = make_ref()

    stderr =
      capture_io(:stderr, fn ->
        stdout =
          capture_io(fn ->
            send(parent, {ref, REPL.__submit__(state, line)})
          end)

        send(parent, {ref, :stdout, stdout})
      end)

    next_state =
      receive do
        {^ref, %Cure.REPL{} = s} -> s
      after
        0 -> raise "submit_capture/2 did not produce a REPL state"
      end

    stdout =
      receive do
        {^ref, :stdout, s} -> s
      after
        0 -> ""
      end

    {next_state, stdout, stderr}
  end

  # Write an executable shell script that overwrites its first argument
  # (the REPL's temp file) with `content`. Returns the script path.
  defp write_editor_stub(content) when is_binary(content) do
    write_editor_stub_raw("""
    #!/bin/sh
    cat > "$1" <<'CURE_REPL_EDITOR_STUB_EOF'
    #{content}
    CURE_REPL_EDITOR_STUB_EOF
    """)
  end

  defp write_editor_stub_raw(script) when is_binary(script) do
    path =
      Path.join(
        System.tmp_dir!(),
        "cure-repl-edit-stub-#{System.unique_integer([:positive])}.sh"
      )

    File.write!(path, script)
    File.chmod!(path, 0o755)
    path
  end
end
