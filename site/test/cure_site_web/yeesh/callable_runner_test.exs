defmodule CureSiteWeb.Yeesh.CallableRunnerTest do
  use ExUnit.Case, async: true

  alias CureSiteWeb.Yeesh.CallableRunner

  describe "run/2" do
    test "returns `:completed` with captured output when the fun finishes" do
      assert {:completed, output} =
               CallableRunner.run(fn ->
                 IO.puts("hello")
                 IO.write("world")
               end)

      # Newlines are normalised to CRLF by `Yeesh.IOServer` for
      # xterm.js compatibility; assert the semantic content without
      # being pedantic about trailing whitespace.
      assert output =~ "hello"
      assert output =~ "world"
    end

    test "returns `:completed` with empty output for a silent fun" do
      assert {:completed, ""} = CallableRunner.run(fn -> :ok end)
    end

    test "surfaces an `:interactive` tuple when the fun calls IO.gets" do
      assert {:interactive, io_server, task_pid, output, prompt} =
               CallableRunner.run(fn ->
                 IO.puts("before")
                 _ = IO.gets("name> ")
                 IO.puts("after")
               end)

      assert is_pid(io_server)
      assert is_pid(task_pid)
      assert Process.alive?(io_server)
      assert Process.alive?(task_pid)
      assert output =~ "before"
      assert prompt == "name> "

      # The caller is responsible for cleanup when it receives an
      # `:interactive` result -- ensure `stop/1` is well-behaved.
      ref = Process.monitor(io_server)
      :ok = CallableRunner.stop(io_server)
      assert_receive {:DOWN, ^ref, :process, ^io_server, _}, 500
    end

    test "rescues exceptions raised inside the fun" do
      assert {:completed, output} =
               CallableRunner.run(fn -> raise "kaboom" end)

      assert output =~ "INTERNAL COMPILER ERROR"
      assert output =~ "[E101]"
      refute output =~ "kaboom"
    end

    test "rejects non-zero-arity callables via the `is_function(fun, 0)` guard" do
      # Going through `apply/3` keeps the static type checker happy
      # while still exercising the runtime guard on `run/2`.
      assert_raise FunctionClauseError, fn ->
        apply(CallableRunner, :run, [fn _ -> :ok end])
      end
    end
  end

  describe "stop/1" do
    test "is a no-op for an already-dead server" do
      {:completed, _} = CallableRunner.run(fn -> :ok end)
      # After a `:completed` result the runner has already stopped the
      # server, so calling `stop/1` on a random dead pid must not crash.
      dead = spawn(fn -> :ok end)
      ref = Process.monitor(dead)
      assert_receive {:DOWN, ^ref, :process, ^dead, _}, 100
      assert :ok = CallableRunner.stop(dead)
    end
  end
end
