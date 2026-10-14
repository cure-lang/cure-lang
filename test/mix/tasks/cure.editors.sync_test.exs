defmodule Mix.Tasks.Cure.Editors.SyncTest do
  use ExUnit.Case, async: true

  alias Mix.Tasks.Cure.Editors.Sync

  test "the editor grammars are in sync with the lexer and the stdlib" do
    assert Sync.check() == []
  end

  describe "vocabulary/1" do
    test "derives keywords from the lexer, without contextual words and literals" do
      vocab = Sync.vocabulary()

      assert "match" in vocab.keywords
      assert "band" in vocab.word_operators
      refute "proof" in vocab.keywords
      refute "true" in vocab.keywords
      assert "requires" in vocab.contextual
    end

    test "derives containers from the stdlib macros that take a module name" do
      assert Enum.all?(~w(actor app fsm sup proof), &(&1 in Sync.vocabulary().containers))
    end
  end
end
