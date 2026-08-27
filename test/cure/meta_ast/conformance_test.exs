defmodule Cure.MetaAST.ConformanceTest do
  use ExUnit.Case, async: true

  alias Cure.MetaAST.Conformance

  # A canonical leaf node used as a stand-in subterm throughout.
  defp var(name), do: {:variable, [scope: :local], name}

  describe "conformant AST (a node in meta is legal under decision D)" do
    test "scalars in meta and subterms in children is conformant" do
      ast =
        {:pattern_match, [line: 1, col: 1],
         [
           var("x"),
           {:match_arm, [line: 2],
            [
              {:pattern, [], [{:literal, [subtype: :integer], 0}]},
              {:body, [], [{:literal, [subtype: :integer], 1}]}
            ]}
         ]}

      assert Conformance.conformant?(ast)
      assert Conformance.violations(ast) == []
      assert Conformance.meta_nonnodes(ast) == []
    end

    test "a canonical node parked in a meta value is NOT a structural violation" do
      # This is the whole point of Option D: `param` keeps its type in meta and the
      # walker will descend it. No :bad_shape / :node_child here.
      ast = {:param, [type: var("Nat")], ["x"]}

      assert Conformance.conformant?(ast)
      assert Conformance.violations(ast) == []
      assert Conformance.meta_nonnodes(ast) == []
    end

    test "primitives and empty children are conformant" do
      assert Conformance.conformant?({:nil_lit, [], []})
      assert Conformance.conformant?(42)
      assert Conformance.conformant?(:ok)
      assert Conformance.conformant?("string")
    end
  end

  describe "INV-C.2 — the node-tag vocabulary reached in meta" do
    test "a node stored under a meta key is collected by tag" do
      ast = {:param, [type: var("Nat")], ["x"]}
      assert Conformance.meta_node_tags(ast) == MapSet.new([:variable])
    end

    test "nodes nested deeper in meta are all collected" do
      # param whose type is a function_call over two variables, all in meta.
      ty = {:function_call, [callee: var("Vec")], [var("n"), var("a")]}
      ast = {:param, [type: ty], ["x"]}

      assert Conformance.meta_node_tags(ast) ==
               MapSet.new([:function_call, :variable])
    end

    test "a node's own subterms in CHILDREN do not count as meta tags" do
      # The scrutinee/arm live in children — not reached via a meta value — so they
      # are not part of the meta vocabulary.
      ast = {:pattern_match, [line: 1], [var("x")]}
      assert Conformance.meta_node_tags(ast) == MapSet.new()
    end

    test "scalars in meta contribute no tags" do
      ast = {:thing, [name: "f", scope: :local, arity: 2], [var("x")]}
      assert Conformance.meta_node_tags(ast) == MapSet.new()
    end
  end

  describe "INV-C.1 — guard-matching non-nodes in meta (must be empty)" do
    test "a keyword-headed node in meta is a genuine node, not a danger" do
      ast = {:param, [type: var("Nat")], ["x"]}
      assert Conformance.meta_nonnodes(ast) == []
    end

    test "a {atom, non-keyword-list, _} tuple in meta is flagged as a danger" do
      # `{:weird, [1, 2, 3], :x}` matches Metastatic's `is_list`-second descent guard
      # but is not a canonical node — descending it would treat opaque data as a
      # subterm. INV-C.1 catches it.
      ast = {:param, [type: {:weird, [1, 2, 3], :x}], ["p"]}

      assert [%{tag: :weird, node: {:weird, [1, 2, 3], :x}}] = Conformance.meta_nonnodes(ast)
    end

    test "opaque data with a non-list second element is safe (no danger)" do
      # MFA / group_ref shapes have an atom second element, so the guard never enters
      # them — they are legitimate opaque leaves in meta.
      ast = {:extern, [target: {:erlang, :length, 1}, ref: {:group_ref, :core, 1}], ["x"]}
      assert Conformance.meta_nonnodes(ast) == []
      assert Conformance.conformant?(ast)
    end
  end

  describe "INV-A — :bad_shape (non-canonical tuple hiding a node), meta or children" do
    test "named_implicit_pat (4-tuple) in a child slot" do
      ast = {:named_implicit_pat, [line: 1], "k", var("m")}
      assert [%{kind: :bad_shape, tag: :named_implicit_pat, arity: 4}] = Conformance.violations(ast)
    end

    test "named_dom (name where meta belongs)" do
      ast = {:named_dom, "x", var("Nat")}
      assert [%{kind: :bad_shape, tag: :named_dom, arity: 3}] = Conformance.violations(ast)
    end

    test "arrow_chain / group / builtin (2-tuples)" do
      assert [%{kind: :bad_shape, tag: :arrow_chain, arity: 2}] =
               Conformance.violations({:arrow_chain, [var("A"), var("B")]})

      assert [%{kind: :bad_shape, tag: :group}] = Conformance.violations({:group, [var("x")]})
      assert [%{kind: :bad_shape, tag: :builtin}] = Conformance.violations({:builtin, var("Int")})
    end

    test "a bad_shape tuple hiding a node inside a META value is still flagged" do
      # INV-A applies in meta too: a decorator holding a `{:group, [node]}` hides its
      # subterm from the walker regardless of slot.
      ast = {:container, [decorator: {:group, [var("x")]}], [var("body")]}

      assert MapSet.member?(Conformance.violation_buckets(ast), {:bad_shape, :group, nil})
    end
  end

  describe "INV-B — :node_child (canonical node whose children slot is a bare node)" do
    test "a single node in the children slot instead of a one-element list" do
      ast = {:wrapper, [line: 1], var("inner")}

      assert [%{kind: :node_child, tag: :wrapper, key: nil}] = Conformance.violations(ast)
      refute Conformance.conformant?(ast)
    end

    test "gadt_ctor's bare arrow_chain child is a non-list children slot" do
      ast = {:gadt_ctor, [name: "C"], {:arrow_chain, [var("A"), var("B")]}}
      assert [%{kind: :node_child, tag: :gadt_ctor, key: nil}] = Conformance.violations(ast)
    end

    test "subterms under a bare-node child are still descended for deeper defects" do
      ast = {:wrapper, [], {:arrow_chain, [{:another, [], var("x")}]}}

      buckets = Conformance.violation_buckets(ast)
      assert MapSet.member?(buckets, {:node_child, :wrapper, nil})
      # the inner :another also has a bare-node child — reached despite the outer flag
      assert MapSet.member?(buckets, {:node_child, :another, nil})
    end
  end

  describe "no false positives on opaque leaf data" do
    test "an MFA tuple in a child slot is not a node and is not flagged" do
      ast = {:extern_call, [], [{:erlang, :length, 1}, var("xs")]}
      assert Conformance.conformant?(ast)
    end

    test "a decorator argument holding only atoms/ints is not flagged" do
      ast = {:container, [], [{:group_ref, :core, 1}, var("body")]}
      assert Conformance.conformant?(ast)
    end

    test "trivia (comment) wide tuples are ignored" do
      assert Conformance.conformant?({:comment, "note", 1, 2, 3})
      assert Conformance.conformant?({:doc_comment, "doc", 1})
    end

    test "a leaf node's scalar value in the children slot is not a node_child" do
      assert Conformance.conformant?({:variable, [scope: :local], "x"})
      assert Conformance.conformant?({:literal, [subtype: :integer], 42})
    end

    test "an opaque non-list children slot (holds no node) is not a node_child" do
      ast = {:extern_ref, [], {:erlang, :length, 1}}
      assert Conformance.conformant?(ast)
    end
  end

  describe "reporting" do
    test "violation_buckets collapses repeated occurrences to distinct buckets" do
      ast =
        {:mod, [],
         [
           {:wrapper, [], var("x")},
           {:wrapper, [], var("y")},
           {:group, [var("z")]}
         ]}

      assert Conformance.violation_buckets(ast) ==
               MapSet.new([
                 {:node_child, :wrapper, nil},
                 {:bad_shape, :group, nil}
               ])
    end

    test "describe renders both structural kinds" do
      ast =
        {:mod, [],
         [
           {:wrapper, [], var("x")},
           {:arrow_chain, [var("A"), var("B")]}
         ]}

      out = ast |> Conformance.violations() |> Conformance.describe()
      assert out =~ "node_child"
      assert out =~ "bad_shape"
      assert Conformance.describe([]) == "no MetaAST-conformance violations"
    end
  end

  describe "against the real parser" do
    alias Cure.Compiler.{Lexer, Parser}

    test "a parsed function's type positions land in the meta vocabulary, not as violations" do
      {:ok, toks} = Lexer.tokenize("mod M\n  fn f(x: Nat) -> Nat = x\n", emit_events: false)
      {:ok, ast} = Parser.parse(toks, emit_events: false)

      # Nat (param type + return type) is a :variable node reached in meta.
      assert MapSet.member?(Conformance.meta_node_tags(ast), :variable)
      # and it is sound: no guard-matching non-node in meta.
      assert Conformance.meta_nonnodes(ast) == []
    end
  end

  describe "boundary canonicalization to_conformant/1" do
    test "lifts meta-borne subterms into child wrapper nodes" do
      param_type = {:variable, [scope: :local], "Nat"}
      param = {:param, [type: param_type], ["x"]}

      conformant = Conformance.to_conformant(param)

      assert {:param, [], [{:type_wrapper, [], [{:variable, [scope: :local], "Nat"}]}, "x"]} =
               conformant
    end
  end
end
