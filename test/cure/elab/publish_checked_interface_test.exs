defmodule Cure.Elab.PublishCheckedInterfaceTest do
  @moduledoc """
  `publish_checked_interface/1` decides whether a checked module is the
  canonical interface for its `source_path`. Living under a stdlib source
  directory is not enough to establish that, because a path is also the
  *documentation* home of every fence in its `##` comments: `mix cure.check.docs`
  compiles those fences with `file:` set to the file they were written in, so
  diagnostics anchor to the right line of the right document.

  Such a snippet is a different module with different content at the same path.
  Publishing it as canonical overwrites the interface memo with an entry keyed
  by the snippet's hash -- which no lookup for the real module can ever match --
  and writes the snippet's interface into the real module's on-disk artifact.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @stdlib_path Path.expand("lib/std/core.cure")

  test "a documentation snippet does not publish itself as the module it is documented in" do
    cache_key = {Program, :module_interface, @stdlib_path}
    real_hash = :crypto.hash(:sha256, File.read!(@stdlib_path))

    assert {:ok, _} = Program.module_interface("Std.Core", @stdlib_path)

    assert {:cached, ^real_hash, _} = :persistent_term.get(cache_key, :missing),
           "the premise of this test: the memo is keyed by the real file's hash"

    # Exactly what the doc gate does with a fence written in `lib/std/core.cure`:
    # compile it as its own module, attributed to the file that documents it.
    snippet = """
    mod DocSnippetProbe
      use Std.Core

      fn probe(x: Int) -> Int = x + 1
    """

    Cure.Compiler.compile_string(snippet, file: @stdlib_path)

    assert {:cached, ^real_hash, _} = :persistent_term.get(cache_key, :missing),
           "a snippet attributed to #{@stdlib_path} must not replace that path's canonical interface"
  end
end
