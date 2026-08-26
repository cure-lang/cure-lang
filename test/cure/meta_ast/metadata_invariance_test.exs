defmodule Cure.MetaAST.MetadataInvarianceTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Erase, Program}
  alias Cure.MetaAST.{Metadata, SourceDecorator}

  @accepted_programs [
    {"dependent Sigma",
     "mod SigmaInvariant\n  type Nat = Z | S(Nat)\n  fn first(p: Sigma(x: Nat, Nat)) -> Nat = p.1\nend\n"},
    {"function Pi alias",
     "mod PiInvariant\n  type Nat = Z | S(Nat)\n  type Endo = (Nat) -> Nat\n  fn apply(f: Endo, x: Nat) -> Nat = f(x)\nend\n"},
    {"refinement",
     "mod RefineInvariant\n  use Std.Nat\n  use Std.Bool\n  use Std.Proof.IntMath\n  fn keep(x: Int, positive: IsTrue(x > 0)) -> {n: Int | n > 0} = x\nend\n"},
    {"union", "mod UnionInvariant\n  fn keep(x: Int | Bool) -> Int | Bool = x\nend\n"},
    {"record and field projection",
     "mod RecordInvariant\n  rec Point\n    x: Int\n    y: Int\n  fn first(p: Point) -> Int = p.x\nend\n"},
    {"annotated call", "mod CallInvariant\n  fn id(x: Int) -> Int = x\n  fn answer() -> Int = id(42)\nend\n"},
    {"constructor pattern",
     "mod PatternInvariant\n  type Maybe = None | Some(Int)\n  fn value(m: Maybe) -> Int = match m\n    None() -> 0\n    Some(x) -> x\nend\n"},
    {"guarded branches",
     "mod GuardInvariant\n  fn sign(n: Int) -> Int = match n\n    x when x > 0 -> 1\n    x -> 0\nend\n"},
    {"multi-clause branches", "mod ClauseInvariant\n  fn sign(n: Int) -> Int\n    | 0 -> 0\n    | _ -> -1\nend\n"},
    {"interface descriptor",
     "mod InterfaceInvariant\n  interface Sized(a)\n    fn size(value: a) -> Int\n  fn keep(x: Int) -> Int = x\nend\n"},
    {"syntax macro expansion",
     "mod MacroInvariant\n  macro Identity\n    syntax identity <value: Code> becomes value\n  fn keep(x: Int) -> Int = identity x\nend\n"}
  ]

  @rejected_programs [
    {"unknown value", "mod RejectName\n  fn bad() -> Int = missing\n"},
    {"annotation mismatch", "mod RejectAnnotation\n  fn bad() -> Int = true\n"},
    {"record field", "mod RejectRecord\n  rec R\n    x: Int\n  fn bad(r: R) -> Int = r.missing\nend\n"},
    {"branch mismatch",
     "mod RejectBranch\n  type Maybe = None | Some(Int)\n  fn bad(m: Maybe) -> Int = match m\n    None() -> 0\n    Some(x) -> true\nend\n"},
    {"positivity", "mod RejectPositivity\n  type Nat = Z | S(Nat)\n  type Bad = MkBad((Bad) -> Nat)\nend\n"},
    {"relevance",
     "mod RejectRelevance\n  type Nat = Z | S(Nat)\n  type SNat indices (n: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(n) -> SNat(S(n))\n  type NV indices (n: Nat)\n    vz : NV(Z)\n    vs : SNat(n) -> NV(S(n))\n  fn bad({n: Nat}, value: NV(n)) -> Nat = n\nend\n"},
    {"totality",
     "mod RejectTotality\n  type Dec = Dcoupled | Causal\n  type Sig = CSig | ESig\n  type SVDesc = SVNil | SVCons(Sig, SVDesc)\n  fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)\n  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)\n    prim : SF(as, bs, Causal)\n    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))\nend\n"},
    {"coverage",
     "mod RejectCoverage\n  fn bad(value: Int | Bool) -> Int = match value\n    integer: Int -> integer\nend\n"}
  ]

  test "recursive source decoration preserves an accepted program verdict and semantics" do
    source = "mod Invariance\n  fn id(x: Int) -> Int = x\n"
    {ast, decorated} = parse_pair(source)
    stripped = Metadata.strip_diagnostics(decorated)

    assert Metadata.semantic_equal?(ast, stripped)
    assert {:ok, plain_env} = Program.check_ast(ast)
    assert {:ok, decorated_env} = Program.check_ast(decorated)
    assert {:ok, stripped_env} = Program.check_ast(stripped)
    assert plain_env == decorated_env
    assert plain_env == stripped_env

    module = Program.module_atom(ast)

    function =
      Enum.find_value(plain_env.defs, fn {_key, %{name: name}} ->
        if String.ends_with?(to_string(name), "#id"), do: name
      end)

    assert function
    assert {:ok, plain_forms} = Emit.compile_forms(plain_env, module, [function])
    assert {:ok, decorated_forms} = Emit.compile_forms(decorated_env, module, [function])
    assert {:ok, stripped_forms} = Emit.compile_forms(stripped_env, module, [function])
    assert plain_forms == decorated_forms
    assert plain_forms == stripped_forms

    plain_def =
      Enum.find_value(plain_env.defs, fn {_key, %{name: name} = definition} -> if name == function, do: definition end)

    decorated_def =
      Enum.find_value(decorated_env.defs, fn {_key, %{name: name} = definition} ->
        if name == function, do: definition
      end)

    stripped_def =
      Enum.find_value(stripped_env.defs, fn {_key, %{name: name} = definition} ->
        if name == function, do: definition
      end)

    assert Erase.erase(plain_env, plain_def.body) == Erase.erase(decorated_env, decorated_def.body)
    assert Erase.erase(plain_env, plain_def.body) == Erase.erase(stripped_env, stripped_def.body)
  end

  test "recursive source decoration preserves a rejected program category" do
    source = "mod InvarianceReject\n  fn bad() -> Int = missing_name\n"
    {ast, decorated} = parse_pair(source)
    stripped = Metadata.strip_diagnostics(decorated)

    assert {:error, original} = Program.check_ast(ast)
    assert {:error, decorated_error} = Program.check_ast(decorated)
    assert {:error, stripped_error} = Program.check_ast(stripped)

    assert Program.semantic_error(original) |> error_head() ==
             error_head(Program.semantic_error(decorated_error))

    assert Program.semantic_error(original) |> error_head() ==
             error_head(Program.semantic_error(stripped_error))
  end

  test "semantic hashes are identical for plain, decorated, and stripped ASTs" do
    source = "mod HashInvariant\n  fn id(x: Int) -> Int = x\nend\n"
    {plain, decorated} = parse_pair(source)
    stripped = Metadata.strip_diagnostics(decorated)

    assert semantic_digest(plain) == semantic_digest(decorated)
    assert semantic_digest(plain) == semantic_digest(stripped)
  end

  test "source roles nested in structural metadata maps are stripped recursively" do
    span =
      Cure.Diagnostic.Span.new(
        source_id: "clause.cure",
        path: "clause.cure",
        start_byte: 0,
        end_byte: 1,
        start_line: 1,
        start_column: 1,
        end_line: 1,
        end_column: 2
      )

    clause = %{
      params: [],
      guard: nil,
      body: [],
      source_info: %Cure.MetaAST.SourceInfo{whole: span, operator: span}
    }

    assert Metadata.strip_diagnostics(clause) == %{params: [], guard: nil, body: []}
  end

  test "computed-macro hygiene is invariant under recursive source decoration" do
    generated =
      {:tuple, [],
       [
         {:fresh_name, [], "temporary"},
         {:variable, [scope: :local], "temporary"}
       ]}

    decorated = SourceDecorator.decorate(generated)
    stripped = Metadata.strip_diagnostics(decorated)

    {plain_hygienic, plain_counter} = Parser.freshen_generated(generated)
    {decorated_hygienic, decorated_counter} = Parser.freshen_generated(decorated)
    {stripped_hygienic, stripped_counter} = Parser.freshen_generated(stripped)

    assert plain_counter == decorated_counter
    assert plain_counter == stripped_counter
    assert Metadata.semantic_equal?(plain_hygienic, decorated_hygienic)
    assert Metadata.semantic_equal?(plain_hygienic, stripped_hygienic)

    assert {:tuple, _, [{:variable, _, "temporary$0"}, {:variable, _, "temporary"}]} =
             decorated_hygienic
  end

  test "source decoration is inert across representative surface families" do
    Enum.each(@accepted_programs, fn {family, source} ->
      {plain, decorated} = parse_pair(source)
      stripped = Metadata.strip_diagnostics(decorated)

      assert Metadata.semantic_equal?(plain, decorated), family
      assert Metadata.semantic_equal?(plain, stripped), family

      assert {:ok, plain_env} = Program.check_ast(plain), family
      assert {:ok, decorated_env} = Program.check_ast(decorated), family
      assert {:ok, stripped_env} = Program.check_ast(stripped), family
      assert semantic_env(plain_env) == semantic_env(decorated_env), family
      assert semantic_env(plain_env) == semantic_env(stripped_env), family
      assert diagnostic_leaks(plain_env) == []
      assert diagnostic_leaks(decorated_env) == []
      assert diagnostic_leaks(stripped_env) == []

      assert Program.check_ast_elixir_core(plain) == {:ok, plain_env}, family
      assert Program.check_ast(plain, diagnostic_metadata: :sentinel) == {:ok, plain_env}, family

      module = Program.module_atom(plain)
      functions = owned_functions(plain_env, module)
      assert functions != [], "#{family} did not expose an emitted function"
      assert {:ok, plain_forms} = Emit.compile_forms(plain_env, module, functions), family
      assert {:ok, decorated_forms} = Emit.compile_forms(decorated_env, module, functions), family
      assert {:ok, stripped_forms} = Emit.compile_forms(stripped_env, module, functions), family
      assert normalize_form_vars(plain_forms) == normalize_form_vars(decorated_forms), family
      assert normalize_form_vars(plain_forms) == normalize_form_vars(stripped_forms), family
      assert diagnostic_leaks(plain_forms) == []
      assert diagnostic_leaks(decorated_forms) == []
      assert diagnostic_leaks(stripped_forms) == []
    end)
  end

  test "source decoration preserves exact semantic rejection reasons across surface families" do
    Enum.each(@rejected_programs, fn {family, source} ->
      {plain, decorated} = parse_pair(source)
      stripped = Metadata.strip_diagnostics(decorated)

      assert {:error, plain_error} = Program.check_ast(plain), family
      assert {:error, decorated_error} = Program.check_ast(decorated), family
      assert {:error, stripped_error} = Program.check_ast(stripped), family

      plain_reason = Program.semantic_error(plain_error)
      assert Metadata.semantic_equal?(plain_reason, Program.semantic_error(decorated_error)), family
      assert Metadata.semantic_equal?(plain_reason, Program.semantic_error(stripped_error)), family
    end)
  end

  defp parse_pair(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "invariance.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "invariance.cure", emit_events: false)
    {ast, SourceDecorator.decorate(ast)}
  end

  defp semantic_digest(ast) do
    ast
    |> Metadata.semantic_key()
    |> :erlang.term_to_binary([:deterministic])
    |> then(&:crypto.hash(:sha256, &1))
  end

  defp owned_functions(env, module) do
    prefix = module |> to_string() |> String.trim_leading("Cure.") |> Kernel.<>("#")

    env.defs
    |> Enum.flat_map(fn
      {_key, %{name: name}} -> if String.starts_with?(to_string(name), prefix), do: [name], else: []
      _ -> []
    end)
    |> Enum.uniq()
  end

  # BEAM abstract forms contain globally fresh synthetic variable atoms. Compare
  # their alpha-normalized shape so only semantic emission differences matter.
  defp normalize_form_vars(forms) do
    {normalized, _names} = normalize_form_vars(forms, %{})
    normalized
  end

  defp normalize_form_vars({:var, line, name}, names) do
    case Map.fetch(names, name) do
      {:ok, normalized} ->
        {{:var, line, normalized}, names}

      :error ->
        normalized = :"_v#{map_size(names)}"
        {{:var, line, normalized}, Map.put(names, name, normalized)}
    end
  end

  defp normalize_form_vars(tuple, names) when is_tuple(tuple) do
    {items, names} = tuple |> Tuple.to_list() |> normalize_form_vars(names)
    {List.to_tuple(items), names}
  end

  defp normalize_form_vars(items, names) when is_list(items),
    do: Enum.map_reduce(items, names, &normalize_form_vars/2)

  defp normalize_form_vars(value, names), do: {value, names}

  @diagnostic_keys [
    :source_info,
    :span,
    :construct_span,
    :name_span,
    :callee_span,
    :source_provenance,
    :expansion_provenance
  ]

  defp diagnostic_leaks(term), do: diagnostic_leaks(term, [])

  defp diagnostic_leaks(%Cure.MetaAST.SourceInfo{}, path), do: [Enum.reverse(path)]
  defp diagnostic_leaks(%Cure.Diagnostic.Span{}, path), do: [Enum.reverse(path)]
  defp diagnostic_leaks(%Cure.Diagnostic.ProvenanceFrame{}, path), do: [Enum.reverse(path)]

  defp diagnostic_leaks(term, path) when is_list(term) do
    term
    |> Enum.with_index()
    |> Enum.flat_map(fn
      {{key, _value}, index} when key in @diagnostic_keys -> [Enum.reverse([index, key | path])]
      {value, index} -> diagnostic_leaks(value, [index | path])
    end)
  end

  defp diagnostic_leaks(term, path) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.with_index()
    |> Enum.flat_map(fn {value, index} -> diagnostic_leaks(value, [index | path]) end)
  end

  defp diagnostic_leaks(term, path) when is_map(term) do
    term
    |> Map.delete(:__struct__)
    |> Enum.flat_map(fn
      # Trusted direct-call summaries intentionally retain diagnostic call-site
      # provenance for totality failures. Their semantic hash strips that
      # decoration, so they are not part of this surface-AST leak invariant.
      {:direct_call_summaries, _summaries} -> []
      {key, _value} when key in @diagnostic_keys -> [Enum.reverse([key | path])]
      {key, value} -> diagnostic_leaks(value, [key | path])
    end)
  end

  defp diagnostic_leaks(_term, _path), do: []

  # Direct-call provenance is intentionally diagnostic-rich, while the trusted
  # summary hash is its canonical semantic identity.
  defp semantic_env(env) do
    summaries = Map.new(env.direct_call_summaries, fn {name, summary} -> {name, summary.summary_hash} end)
    %{env | direct_call_summaries: summaries}
  end

  defp error_head({tag, _rest}) when is_atom(tag), do: tag
  defp error_head({tag, _, _}) when is_atom(tag), do: tag
  defp error_head(other), do: other
end
