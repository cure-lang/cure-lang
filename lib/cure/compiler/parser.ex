defmodule Cure.Compiler.Parser do
  @moduledoc """
  Pratt parser for the Cure programming language.

  Transforms a token list from `Cure.Compiler.Lexer` into a MetaAST tree
  using Metastatic's 3-tuple format `{type, keyword_meta, children_or_value}`.

  The parser is indentation-aware: `:indent`/`:dedent`/`:newline` tokens from
  the lexer drive block structure.

  ## Record syntax

  Two record syntactic forms share the same `TypeName{...}` opening:

  - **Construction** `Point{x: 1, y: 2}` -- emits
    `{:function_call, [name: "Point", record: true, ...], field_pairs}`
  - **Update** `Point{p | x: 1}` -- emits
    `{:record_update, [name: "Point", ...], [base_expr | field_pairs]}`

  Detection uses a probe: after consuming `{`, one expression is parsed and
  the next token is inspected. If it is `|`, the parser commits to update
  mode. Otherwise it rewinds (saves and restores `pos` and `errors`) and
  falls back to normal field-pair parsing.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:parser, :node_parsed, ast, meta}` -- after each top-level expression
  - `{:parser, :parse_complete, ast, meta}` -- when parsing finishes
  - `{:parser, :error, error, meta}` -- on parse errors

  ## Usage

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens)
  """

  alias Cure.Compiler.{MacroFamily, MacroRaw, Token}
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable, FixityScan, FixityResolver, Precedence}
  alias Cure.Compiler.Parser.Range
  alias Cure.Diagnostic.{ProvenanceFrame, Span}
  alias Cure.MetaAST.Metadata
  alias Cure.MetaAST.SourceInfo
  alias Cure.Diagnostic.ProofChainSyntaxProblem
  alias Cure.Pipeline.Events

  # -- Parser State ----------------------------------------------------------

  # `tokens` holds a *tuple*, not a list, so `peek/1` is O(1) `elem/2` rather
  # than an O(pos) `Enum.at/2` walk; `count` caches the arity so `peek/1` never
  # pays an O(n) `length/1`. Together these keep parsing linear in token count.
  # Always write it via `put_tokens/2` — never `%{state | tokens: some_list}`.
  defstruct [
    :tokens,
    :file,
    count: 0,
    pos: 0,
    errors: [],
    emit_events: false,
    edition: nil,
    seen_stmt?: false,
    builtin_macros: %{},
    builtin_computed_macros: %{},
    active_macros: %{},
    computed_macros: %{},
    fresh_counter: 0,
    literal_macros: %{},
    expansion_context: nil,
    # Dotted name of the `mod` whose body is being parsed, innermost last, or
    # `nil` at the top level. Lifted-module macros (`fsm`, `actor`, `sup`, `app`)
    # qualify their bare names against this so two modules can each declare a
    # `Worker` without colliding. See `qualify_lifted_module_name/2`.
    enclosing_module: nil,
    # Declaration-driven binding-power table the Pratt loop consults instead of
    # the static `Precedence` module. Seeded from the memoized built-in table
    # (`Std.Operators`) and extended with the current module's own
    # `precedencegroup`/`infix`/… decls (collected in the harvest pass). `nil`
    # in sub-parsers that build `%__MODULE__{}` directly — `fixity_table/1`
    # falls back to the built-in table there.
    fixity_table: nil,
    # Indent levels of the infix continuations currently open, innermost first.
    # A trailing (or leading) infix operator lets its operand sit on the next
    # line, and the lexer marks that line with an `:indent`/`:dedent` pair like
    # any other block. The pair is layout the operand introduced rather than a
    # block boundary, so the Pratt loop opens the level when it steps over the
    # `:indent` and closes it by dropping the matching `:dedent`.
    # Levels nest LIFO, and only the innermost is ever eligible to close, so an
    # operand containing a real block still hands that block its own `:dedent`.
    continuation_levels: []
  ]

  # Keywords that can open a new top-level definition. Used by the
  # synchronize_to_statement/1 recovery helper to know when to stop
  # skipping tokens after a parse error.
  @definition_keywords [
    :fn,
    :local,
    :mod,
    :rec,
    :type,
    :use,
    :sup,
    :proto,
    :impl,
    :interface,
    :implementation,
    :proof
  ]

  # Names parse_prefix/1's :identifier case already dispatches on via a
  # hard-coded clause (the soft-keyword forms sup/app/macro/with,
  # plus the assert_type/rewrite builtins). A local macro can never claim one
  # of these: the guarded macro-use clause is checked FIRST, so an unguarded
  # collision would silently disable the existing form for the rest of the
  # module with no error raised. Reserved names simply keep today's
  # soft-keyword behavior; they are never macro-usable.
  @reserved_macro_keywords ~w(assert_type rewrite with macro have)

  # Decorators that describe the *module*, not the declaration that follows.
  # A `@name(...)` in this set NEVER attaches to the next `fn`/`rec`/`type`;
  # it always parses as a standalone `{:decorator, ...}` node so downstream
  # stages (codegen, preload) can read it as module metadata. `@group(:g)`
  # replaces the historical marker-function hack for stdlib preload groups.
  @module_level_decorators ~w(group)

  # Maps a fixed operator token TYPE to the lexeme STRING it binds under in the
  # declaration-driven `FixityTable` (keyed on lexemes, as declared in
  # `Std.Operators`). Word operators keep their remapped token type but bind
  # under the spelled-out word. A generic `:operator` token carries its own
  # lexeme in `value` and is handled directly by `lexeme_of/1`. Any token type
  # absent here is not an operator and yields `:not_infix`.
  @token_lexemes %{
    pipe: "|>",
    melquiades: "<-|",
    or_op: "or",
    and_op: "and",
    eq: "==",
    neq: "!=",
    lt: "<",
    gt: ">",
    lte: "<=",
    gte: ">=",
    range: "..",
    range_inclusive: "..=",
    string_concat: "<>",
    plus: "+",
    minus: "-",
    star: "*",
    slash: "/",
    percent: "%",
    band_op: "band",
    bor_op: "bor",
    bxor_op: "bxor",
    bsl_op: "bsl",
    bsr_op: "bsr",
    dot: ".",
    assign: "=",
    not_op: "not",
    bnot_op: "bnot"
  }

  @type t :: %__MODULE__{}
  @type ast :: {atom(), keyword(), term()}
  @type result :: {ast(), t()}

  @doc """
  Apply the parser's hygiene protocol to AST produced by a computed macro.

  Computed macros use the same `fresh(...)` marker as `becomes` templates, but
  their result is produced after parsing and therefore cannot pass through the
  normal template expansion path. This entry point keeps the protocol shared
  and threads the caller's counter so nested and sibling expansions remain
  distinct. Only explicit generated markers are rewritten; syntax reflected
  from the use site remains opaque to the generated name mapping.
  """
  @spec freshen_generated(ast(), non_neg_integer()) :: {ast(), non_neg_integer()}
  def freshen_generated(ast, fresh_counter \\ 0) when is_integer(fresh_counter) and fresh_counter >= 0 do
    state = %__MODULE__{fresh_counter: fresh_counter}

    freshen(ast, state, false)
    |> then(fn {freshened, state} -> {freshened, state.fresh_counter} end)
  end

  # -- Public API ------------------------------------------------------------

  @doc """
  Parse a token list into a MetaAST.

  Returns `{:ok, ast}` on success or `{:error, errors}` on failure.
  If the source contains multiple top-level expressions, they are wrapped
  in a `{:block, meta, exprs}` node.

  ## Options

  - `:file` -- filename for metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  """
  @spec parse([Token.t()], keyword()) :: {:ok, ast()} | {:error, [term()]}
  def parse(tokens, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, true)
    edition = Keyword.get(opts, :edition, Cure.Edition.current())
    prelude? = Keyword.get(opts, :prelude_macros, true)
    supplied_macros = Keyword.get(opts, :builtin_macros)
    prelude_providers = Keyword.get(opts, :prelude_providers, [])
    imported_fixity = Keyword.get(opts, :imported_fixity, [])
    validate_fixity_cycles? = Keyword.get(opts, :validate_fixity_cycles, false)

    # The built-in fixity table (memoized). Both passes seed from it; the
    # authoritative pass layers the module's own decls on top (collected below).
    builtin_fixity = session_builtin_fixity_table()

    # Phase 1 (harvest): parse once with NO active macros, keep only the local
    # macro grammars. Use-sites may mis-parse here; we discard everything but
    # the {:macro_def, …} nodes and their (recovered) errors. This pass also
    # yields the module's `precedencegroup`/`infix`/… declaration nodes, which
    # parse context-free (no fixity table needed) — they feed the module table.
    harvest_exprs = harvest(tokens, file, builtin_fixity, edition)

    # Assemble the module's fixity table = built-in prelude base ∪ own(M) ∪ the
    # fixity of every module in M's transitive `use`-closure ∪ user `@prelude`
    # providers. A same-lexeme/different-group (or same-group/different-body)
    # clash is a hard PARSE error, raised here before the authoritative pass.
    %{fixity: own_fixity, uses: uses} = FixityScan.collect_module_facts(harvest_exprs)
    own_uses = Enum.map(uses, & &1.target)

    module_fixity =
      case FixityResolver.assemble(builtin_fixity, own_fixity, own_uses, prelude_providers,
             imported_fixity: imported_fixity
           ) do
        {:ok, table} ->
          case {validate_fixity_cycles?, FixityTable.cyclic_groups(table)} do
            {true, [_ | _] = groups} ->
              {:__fixity_error__,
               {:precedence_cycle, %{groups: groups, spans: FixityScan.group_spans(harvest_exprs, groups)}}}

            _ ->
              table
          end

        {:error, conflict} ->
          {:__fixity_error__, conflict}
      end

    active = harvest_active_macros(harvest_exprs)
    computed = harvest_computed_macros(harvest_exprs)
    literal = harvest_literal_macros(harvest_exprs)

    case module_fixity do
      {:__fixity_error__, reason} ->
        {:error, [reason]}

      %FixityTable{} = module_fixity ->
        # Phase 2 (authoritative): parse with the macro grammars seeded so use-sites expand.
        builtin_rules =
          cond do
            is_map(supplied_macros) -> supplied_macros
            prelude? -> prelude_macros()
            true -> %{}
          end

        # Rules the caller harvested from the modules this one `use`s. A macro is
        # only usable where its grammar is active, so a module that imports a
        # macro provider cannot be parsed correctly on its own: without these its
        # use-sites are silently not macro uses at all.
        #
        # They join the module's OWN macros rather than the ambient built-in set,
        # because that is what they are — grammar this module brought into scope
        # by naming its provider. The two seats are not interchangeable: the
        # built-in seat assumes a prelude macro always takes an argument, so a
        # nullary rule parked there could never fire. An imported macro must parse
        # exactly as the same macro defined locally would, and this is what makes
        # that true. A local rule still wins on a keyword collision.
        imported = Keyword.get(opts, :imported_macros, %{})
        active = merge_imported_rules(active, syntax_macro_rules(imported))
        computed = merge_imported_rules(computed, computed_macro_rules(imported))

        state = %__MODULE__{
          file: file,
          emit_events: emit?,
          edition: edition,
          builtin_macros: syntax_macro_rules(builtin_rules),
          builtin_computed_macros: computed_macro_rules(builtin_rules),
          active_macros: active,
          computed_macros: computed,
          # Local `literal` rules always apply. In the normal (non-self-harvest)
          # case, standard-library `literal` rules join them so a suffix like `ms`
          # expands in ANY file, exactly as `:syntax` macros are globally active via
          # `builtin_macros`. Local rules win on a suffix collision.
          literal_macros:
            cond do
              is_map(supplied_macros) -> literal
              prelude? -> Map.merge(prelude_literal_macros(), literal, fn _k, _p, l -> l end)
              true -> literal
            end,
          fixity_table: module_fixity
        }

        state = put_tokens(state, tokens)

        {exprs, state} = parse_program(state)

        ast =
          case exprs do
            [single] -> single
            many -> {:block, [line: 1, col: 1], many}
          end

        if emit? do
          Events.emit(:parser, :parse_complete, ast, Events.meta(file, 1))
        end

        case state.errors do
          [] -> {:ok, ast}
          errors -> {:error, Enum.reverse(errors)}
        end
    end
  end

  @doc """
  Run the table-independent harvest pass over `tokens`: a single `parse_program`
  seeded with `base`, with per-statement recovery. Returns the surviving
  top-level declaration/expression nodes. Never raises — used to extract a
  module's own fixity/`use`/`@prelude`/module-name structure without a fully
  successful body parse.
  """
  @spec harvest([term()], String.t(), FixityTable.t(), term()) :: [tuple()]
  def harvest(tokens, file, base, edition \\ nil) do
    edition = edition || Cure.Edition.current()

    harvest_state =
      put_tokens(
        %__MODULE__{file: file, emit_events: false, edition: edition, fixity_table: base},
        tokens
      )

    {exprs, _state} = parse_program(harvest_state)
    exprs
  end

  defp prelude_macros do
    case {Process.get(:cure_loading_prelude), :persistent_term.get({__MODULE__, :prelude_macros}, :missing)} do
      {true, _} -> %{}
      {_, rules} when is_map(rules) -> rules
      _ -> load_prelude_macros()
    end
  end

  defp load_prelude_macros do
    Process.put(:cure_loading_prelude, true)

    {rules, literal_rules} =
      case Application.get_env(:cure, :stdlib_macro_rules) do
        rules when is_map(rules) ->
          # Env-supplied grammar sets carry only keyword `:syntax` rules; there
          # is no literal-rule channel for this legacy escape hatch.
          {rules, %{}}

        _ ->
          stdlib_macro_paths =
            (Path.wildcard(Path.expand("../../std/*.cure", __DIR__)) ++
               Path.wildcard(Path.expand("../../std_deps/regex/*.cure", __DIR__)))
            |> Enum.sort()

          # First harvest every standard-library macro without any builtin
          # rules. A second parse uses that complete grammar set so one
          # standard-library macro can transparently invoke another (for
          # example, standard-library starters invoking another syntax macro).
          harvested = collect_stdlib_macro_rules(stdlib_macro_paths, %{})
          syntax = collect_stdlib_macro_rules(stdlib_macro_paths, %{}, harvested)
          literal = collect_stdlib_literal_rules(stdlib_macro_paths, harvested)
          {syntax, literal}
      end

    :persistent_term.put({__MODULE__, :prelude_macros}, rules)
    :persistent_term.put({__MODULE__, :prelude_literal_macros}, literal_rules)
    Process.delete(:cure_loading_prelude)
    rules
  end

  # Suffix-keyed `literal` rules gathered from every standard-library module, so
  # a suffix such as `ms` expands in any file the way keyword `:syntax` macros
  # are globally active. Populated as a side effect of `load_prelude_macros/0`
  # (both persistent-term caches are written together); while the prelude is
  # itself loading, no prelude literal rules are active (self-reference guard).
  defp prelude_literal_macros do
    case {Process.get(:cure_loading_prelude), :persistent_term.get({__MODULE__, :prelude_literal_macros}, :missing)} do
      {true, _} ->
        %{}

      {_, rules} when is_map(rules) ->
        rules

      _ ->
        load_prelude_macros()
        :persistent_term.get({__MODULE__, :prelude_literal_macros}, %{})
    end
  end

  defp collect_stdlib_literal_rules(paths, builtin_macros) do
    Enum.reduce(paths, %{}, fn path, acc ->
      with {:ok, source} <- File.read(path),
           {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
           {:ok, ast} <-
             parse(tokens,
               file: path,
               emit_events: false,
               prelude_macros: false,
               builtin_macros: builtin_macros
             ) do
        Map.merge(acc, harvest_literal_macros(ast, path), fn _k, v1, v2 -> v1 ++ v2 end)
      else
        _ -> acc
      end
    end)
  end

  defp collect_stdlib_macro_rules(paths, acc, builtin_macros \\ %{}) do
    Enum.reduce(paths, acc, fn path, rules ->
      with {:ok, source} <- File.read(path),
           {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
           {:ok, ast} <-
             parse(tokens,
               file: path,
               emit_events: false,
               prelude_macros: false,
               builtin_macros: builtin_macros
             ) do
        collect_macro_rules(ast, rules, path)
      else
        _ -> rules
      end
    end)
  end

  # `path` is the home file of every rule harvested here (a stdlib module). It is
  # stamped onto each rule as `:source_path` so a computed/family use-site can
  # later resolve the rule's expander in its DEFINITION-SITE scope (ambient macro
  # hygiene), not just the bare caller env. Local/user macros harvest through
  # harvest_active_macros / harvest_computed_macros instead and carry no path, so
  # their expansion behaviour is unchanged.
  defp collect_macro_rules(ast, acc, path) do
    Enum.reduce(collect_macro_defs_with_scope(ast), acc, fn {:macro_def, meta, rules}, macro_acc ->
      tagged = Enum.map(harvestable_macro_rules(meta, rules), &Map.put(&1, :source_path, path))

      Enum.reduce(tagged, macro_acc, fn
        %{kind: :syntax, keyword: keyword} = rule, acc2 when is_binary(keyword) ->
          Map.update(acc2, keyword, [rule], &(&1 ++ [rule]))

        %{kind: :computed, keyword: keyword} = rule, acc2 when is_binary(keyword) ->
          Map.update(acc2, keyword, [rule], &(&1 ++ [rule]))

        _, acc2 ->
          acc2
      end)
    end)
  end

  @doc """
  The `syntax`/`computed` rules a parsed module publishes, keyed by leading
  keyword and stamped with the module's source path.

  Callers that compile a whole universe pass these back in as `:imported_macros`
  when parsing the modules that `use` this one.
  """
  @spec macro_rules(ast() | [ast()], Path.t() | nil) :: %{String.t() => [map()]}
  def macro_rules(ast, source_path \\ nil), do: collect_macro_rules(ast, %{}, source_path)

  defp merge_imported_rules(own, imported),
    do: Map.merge(imported, own, fn _keyword, _imported, own -> own end)

  defp syntax_macro_rules(rules) when is_map(rules), do: filter_macro_rules(rules, :syntax)
  defp syntax_macro_rules(_rules), do: %{}

  defp computed_macro_rules(rules) when is_map(rules), do: filter_macro_rules(rules, :computed)
  defp computed_macro_rules(_rules), do: %{}

  defp filter_macro_rules(rules, kind) do
    for {keyword, candidates} <- rules,
        selected = Enum.filter(List.wrap(candidates), &(&1[:kind] == kind)),
        selected != [],
        into: %{} do
      {keyword, selected}
    end
  end

  @doc """
  Expand a macro example's captured use-site tokens through the macro's own
  rules — the same expansion a real use-site gets (nested literal/`<fresh>`
  expansion included). Used by MacroValidate to check `example … expands …`
  pins (self-proving §5). Returns the expanded surface AST.
  """
  @spec expand_example([map()], [Token.t()]) :: ast()
  def expand_example(rules, use_site_tokens) do
    synthetic = [{:macro_def, [], rules}]
    active = harvest_active_macros(synthetic)
    computed = harvest_computed_macros(synthetic)
    literal = harvest_literal_macros(synthetic)

    eof = %Token{type: :eof, value: nil, line: 0, col: 0}

    state =
      put_tokens(
        %__MODULE__{
          file: "example",
          emit_events: false,
          builtin_macros: %{},
          builtin_computed_macros: %{},
          active_macros: active,
          computed_macros: computed,
          literal_macros: literal
        },
        use_site_tokens ++ [eof]
      )

    {ast, state} = parse_expr(state, 0)

    # A hole segment unconditionally parses ONE expr and binds it -- match_segments
    # is satisfied the moment every declared segment is matched, regardless of
    # whether every captured use-site token was consumed (that is correct for a
    # REAL use-site, where anything left over is just the start of the next
    # top-level form). An example's use-site has no such continuation: it is
    # captured as "every token up to `expands`" specifically so it names ONE
    # complete macro use. If tokens remain unconsumed here, the example's
    # use-site does not correspond to a single full expansion -- wrap the
    # result in a sentinel no hand-written pin can ever equal, so
    # MacroValidate.check_examples reports example_mismatch instead of
    # silently accepting a garbage-suffixed example.
    case peek(state) do
      %Token{type: :eof} -> ast
      # Generated raw-hole proofs preserve the structural delimiter for the
      # enclosing parser, so no ordinary example continuation remains.
      %Token{type: :dedent} -> ast
      _leftover -> {:example_use_site_not_fully_consumed, [], [ast]}
    end
  end

  # Collect every local macro rule, indexed by the rule's leading keyword, from
  # a parsed top-level expr list. Descends into containers (a `macro` inside a
  # `mod` is still a local macro of that module).
  defp harvest_active_macros(exprs) do
    exprs
    |> collect_macro_defs_with_scope()
    |> Enum.reduce(%{}, fn {:macro_def, meta, rules}, acc ->
      Enum.reduce(harvestable_macro_rules(meta, rules), acc, fn
        %{kind: :syntax, keyword: kw} = rule, acc2 when is_binary(kw) ->
          Map.update(acc2, kw, [rule], &(&1 ++ [rule]))

        _rule, acc2 ->
          acc2
      end)
    end)
  end

  # Tier-3 sibling of the parse-time syntax harvester. Computed rules are kept
  # separate because their use-sites emit deferred AST nodes; they must not be
  # mistaken for Tier-2 templates that can expand before elaboration.
  defp harvest_computed_macros(exprs) do
    exprs
    |> collect_macro_defs_with_scope()
    |> Enum.reduce(%{}, fn {:macro_def, meta, rules}, acc ->
      Enum.reduce(harvestable_macro_rules(meta, rules), acc, fn
        %{kind: :computed, keyword: kw} = rule, acc2 when is_binary(kw) ->
          Map.update(acc2, kw, [rule], &(&1 ++ [rule]))

        _rule, acc2 ->
          acc2
      end)
    end)
  end

  defp harvestable_macro_rules(meta, rules) do
    MacroFamily.lowered_rules(meta, rules)
  end

  # Sibling of harvest_active_macros for Tier-1 `literal` rules, keyed by their
  # dispatch suffix. Malformed literal rules (no suffix) are skipped.
  defp harvest_literal_macros(exprs, source_path \\ nil) do
    exprs
    |> collect_macro_defs_with_scope()
    |> Enum.reduce(%{}, fn {:macro_def, _meta, rules}, acc ->
      Enum.reduce(rules, acc, fn
        %{kind: :literal, suffix: s} = rule, acc2 when is_binary(s) ->
          tagged = if source_path, do: Map.put(rule, :source_path, source_path), else: rule
          Map.update(acc2, s, [tagged], &(&1 ++ [tagged]))

        %{kind: :computed_literal, token_kind: kind} = rule, acc2 when is_atom(kind) ->
          tagged = if source_path, do: Map.put(rule, :source_path, source_path), else: rule
          Map.update(acc2, {:token, kind}, [tagged], &(&1 ++ [tagged]))

        _rule, acc2 ->
          acc2
      end)
    end)
  end

  # Macro rules inherit the imports visible where their definition lives. A
  # generated lifted module is a new compilation unit, so those imports must be
  # carried across the quotation boundary before its types and function bodies
  # are elaborated. This is lexical scope propagation, not a behavior-specific name
  # table: any user-defined macro can use the same mechanism.
  defp collect_macro_defs_with_scope(node, imports \\ [])

  defp collect_macro_defs_with_scope(node, imports) when is_list(node),
    do: Enum.flat_map(node, &collect_macro_defs_with_scope(&1, imports))

  defp collect_macro_defs_with_scope({:macro_def, meta, rules}, imports) do
    rules = Enum.map(rules, &Map.put_new(&1, :lexical_imports, imports))
    [{:macro_def, meta, rules}]
  end

  defp collect_macro_defs_with_scope({:container, meta, children}, imports) when is_list(meta) do
    imports =
      case Keyword.get(meta, :container_type) do
        :module -> imports ++ direct_import_declarations(children)
        _ -> imports
      end

    Enum.flat_map(children, &collect_macro_defs_with_scope(&1, imports))
  end

  defp collect_macro_defs_with_scope({_type, _meta, children}, imports) when is_list(children),
    do: Enum.flat_map(children, &collect_macro_defs_with_scope(&1, imports))

  defp collect_macro_defs_with_scope(_other, _imports), do: []

  defp direct_import_declarations(children) when is_list(children) do
    for {:import, meta, _} = declaration <- children,
        is_list(meta),
        is_binary(Keyword.get(meta, :source)),
        do: declaration
  end

  defp direct_import_declarations(_children), do: []

  # A use-site of an active macro keyword. Milestone-2 handles a single rule per
  # keyword; the rule's segments are matched against the use-site tokens, binding
  # holes, then substituted into the template. `progress` (segments consumed) is
  # the syntax-parse "how far did we get" carried for maximal-failure selection
  # once multiple rules per keyword arrive.
  # After a number literal is read (state already past it), check whether the
  # next token is a registered literal-rule suffix; if so, expand that rule with
  # the number bound to its leading hole. Otherwise return the plain number.
  defp maybe_literal_macro(state, num) do
    case peek(state) do
      %Token{type: :identifier, value: suffix} ->
        case Map.fetch(state.literal_macros, suffix) do
          {:ok, [rule | _]} -> expand_literal_rule(rule, num, state)
          :error -> {num, state}
        end

      _ ->
        {num, state}
    end
  end

  # Bind the already-read number to the rule's leading hole, then match the
  # remaining segments (the suffix, consumed here) and expand. Reuses
  # match_segments/expand_rule so <fresh> + hole-subst + the soundness firewall
  # all apply identically to keyword-triggered rules.
  defp expand_literal_rule(rule, num, state) do
    [{:hole, %{name: hole_name}} | rest] = rule.segments

    bindings = put_macro_binding(%{}, hole_name, num)

    case match_segments(state, rest, bindings, 1) do
      {:ok, bindings, _progress, state} ->
        {expanded, state} = expand_rule(rule, bindings, state)

        frame =
          macro_expansion_frame(
            Map.get(rule, :suffix, "literal"),
            first_node_source_span(num),
            Map.get(rule, :source_span),
            macro_match_span(bindings)
          )

        {append_macro_provenance(expanded, frame), state}

      {:error, _progress, state} ->
        # Only reachable for an out-of-scope malformed literal rule with segments
        # after the suffix; the suffix segment `match_segments` matched is already
        # consumed here. T4 does not diagnose malformed literal rules (error-floor
        # task); this branch exists only so expand_literal_rule is total.
        {num, state}
    end
  end

  defp parse_macro_use(state, keyword), do: parse_macro_use(state, keyword, state.active_macros)

  defp parse_macro_use(state, keyword, registry) do
    rules = Map.fetch!(registry, keyword)
    # consume the keyword token
    keyword_token = peek(state)
    state = advance(state)

    case match_macro_rule(rules, state) do
      {:ok, rule, bindings, state} ->
        {expanded, state} = expand_rule(rule, bindings, state)

        frame =
          macro_expansion_frame(
            keyword,
            keyword_token.span,
            Map.get(rule, :source_span),
            macro_match_span(bindings)
          )

        {append_macro_provenance(expanded, frame), state}

      {:error, rule, progress, state} ->
        t = peek(state)

        state =
          add_error(
            state,
            {:macro_use_mismatch,
             %{
               keyword: keyword,
               expected: macro_expected_at(rule, progress),
               got: macro_got_desc(t),
               token_type: t.type,
               span: t.span,
               invocation_span: keyword_token.span,
               definition_span: Map.get(rule, :source_span),
               line: t.line,
               column: t.col
             }}
          )

        # Recover: yield the bare keyword variable so the outer parse continues.
        {variable(%Cure.Compiler.Token{
           type: :identifier,
           value: keyword,
           line: t.line,
           col: t.col
         }), state}
    end
  end

  # Rules sharing a dispatch keyword may overlap (for example, a specific
  # `with` form and a general body form). Try each complete grammar match from
  # the same post-keyword state so a failed partial match cannot consume input
  # or prevent a later rule from being considered.
  defp match_macro_rule([rule | rest], state) do
    case match_segments(state, rule.segments, %{}, 0) do
      {:ok, bindings, _progress, matched_state} ->
        {:ok, rule, bindings, matched_state}

      {:error, progress, failed_state} ->
        case match_macro_rule(rest, state) do
          {:error, _last_rule, _last_progress, _last_state} ->
            {:error, rule, progress, failed_state}

          success ->
            success
        end
    end
  end

  defp match_macro_rule([], state), do: {:error, %{segments: []}, 0, state}

  # Tier-3 use-sites are matched at parse time, but their elab runs only after
  # the dependent environment exists. Preserve the elab reference and the
  # matched inputs in a generic syntax-shaped node for the elaboration pass.
  defp parse_computed_use(state, keyword) do
    rules = computed_rules(state, keyword)
    original_state = state
    keyword_token = peek(state)
    state = advance(state)

    case match_computed_rule(rules, state) do
      {:ok, bindings, _progress, state, rule} ->
        inputs =
          Enum.flat_map(rule.segments, &segment_inputs(&1, bindings))

        input = {:macro_input, [keyword: keyword], inputs}

        meta = [
          keyword: keyword,
          syntax_type: Map.get(rule, :syntax_type, macro_syntax_type(keyword)),
          syntax_fields: Map.get(rule, :syntax_fields, macro_syntax_fields(rule.segments)),
          syntax_repeated_fields: Map.get(rule, :syntax_repeated_fields, macro_syntax_repeated_fields(rule.segments)),
          syntax_field_types: Map.get(rule, :syntax_field_types, %{}),
          file: state.file,
          line: keyword_token.line,
          col: keyword_token.col
        ]

        meta = put_computed_use_source_info(meta, keyword_token, rule, bindings)

        meta =
          case computed_use_obligations(rule, bindings) do
            [] -> meta
            obligations -> Keyword.put(meta, :capture_obligations, obligations)
          end

        # The matched rule's segments (literals interleaved with holes). The
        # printer needs the literal separators (`state`/`messages`/…) to
        # reconstruct the surface invocation — the flattened arg list drops
        # them — and a file being reprinted has no access to the stdlib rule
        # that defined this macro, so the segments must travel on the node.
        # Omit the key entirely for zero-hole macros (empty segments): they
        # reprint from the keyword alone and their deferred-node shape stays
        # unchanged (macro_computed_test pins the exact meta for such macros).
        meta =
          case rule.segments do
            [] -> meta
            segments -> Keyword.put(meta, :syntax_segments, segments)
          end

        # Only stdlib-harvested rules carry a home file (:source_path). Attach it
        # as :home_source for definition-site expander resolution; omit the key
        # entirely for user/local macros so their deferred-node shape is unchanged.
        meta =
          case Map.get(rule, :source_path) do
            nil -> meta
            home_source -> Keyword.put(meta, :home_source, home_source)
          end

        meta =
          if Map.get(rule, :direct_inputs, false),
            do: Keyword.put(meta, :direct_inputs, true),
            else: meta

        {{:computed_use, put_expansion_context(meta, state.expansion_context), [rule.elab, input]}, state}

      {:error, rule, progress, state} ->
        case computed_macro_fallback(original_state, keyword) do
          {:ok, ast, fallback_state} ->
            {ast, fallback_state}

          :none ->
            t = peek(state)

            state =
              add_error(
                state,
                {:macro_use_mismatch,
                 %{
                   keyword: keyword,
                   expected: macro_expected_at(rule, progress),
                   got: macro_got_desc(t),
                   token_type: t.type,
                   span: t.span,
                   invocation_span: keyword_token.span,
                   definition_span: Map.get(rule, :source_span),
                   line: t.line,
                   column: t.col
                 }}
              )

            {variable(%Cure.Compiler.Token{
               type: :identifier,
               value: keyword,
               line: t.line,
               col: t.col
             }), state}
        end
    end
  end

  defp match_computed_rule([rule | rest], state) do
    case match_segments(state, rule.segments, %{}, 0) do
      {:ok, bindings, progress, matched_state} ->
        {:ok, bindings, progress, matched_state, rule}

      {:error, progress, _failed_state} ->
        case match_computed_rule(rest, state) do
          {:error, _last_rule, _last_progress, _last_state} ->
            {:error, rule, progress, state}

          success ->
            success
        end
    end
  end

  defp match_computed_rule([], state), do: {:error, %{segments: []}, 0, state}

  defp computed_use_obligations(rule, bindings) do
    Enum.flat_map(Map.get(rule, :obligations, []), fn obligation ->
      expression =
        case Map.get(obligation, :field) do
          nil -> Map.get(bindings, obligation.capture)
          field -> family_binding_field(bindings["definition"], rule.syntax_family.fields, field)
        end

      if is_nil(expression), do: [], else: [Map.put(obligation, :expression, expression)]
    end)
  end

  defp family_binding_field({:family_input, _meta, values}, fields, field) do
    fields
    |> Enum.zip(values)
    |> Enum.find_value(fn
      {%{name: ^field}, value} -> value
      _ -> nil
    end)
  end

  defp family_binding_field(_binding, _fields, _field), do: nil

  # A computed rule may deliberately share a keyword with an older transparent
  # rule. Let the computed grammar win when it matches, but preserve the
  # existing rule as a grammar fallback when it does not. The fallback starts
  # from the original state so the failed computed match cannot consume input.
  defp computed_macro_fallback(state, keyword) do
    cond do
      is_map_key(state.builtin_macros, keyword) and prelude_macro_head?(state, keyword) ->
        {ast, state} = parse_macro_use(state, keyword, state.builtin_macros)
        {:ok, ast, state}

      is_map_key(state.active_macros, keyword) and macro_use_head?(state, keyword) ->
        {ast, state} = parse_macro_use(state, keyword)
        {:ok, ast, state}

      true ->
        :none
    end
  end

  defp computed_rules(state, keyword) do
    case Map.get(state.computed_macros, keyword) do
      nil -> Map.get(state.builtin_computed_macros, keyword, [])
      rules -> rules
    end
  end

  # Describe the segment a macro rule expected at the failed position, for the
  # default mismatch diagnostic (SP1 §2 floor). A literal segment names the exact
  # word; a hole names its declared kind; past the end means the use supplied
  # tokens the rule did not call for.
  #
  # NOTE (reviewed): under today's match_segments/4, a {:hole, _} segment NEVER
  # fails to match (it unconditionally parses an expr and binds it), so the only
  # way parse_macro_use's single call site reaches this function is via a
  # {:lit, w} mismatch. The {:hole_kind, k} and :nothing_more arms are
  # defensive/forward-looking (for when match_segments gains hole-content
  # validation, or T9's maximal-progress selection makes a hole-position failure
  # possible) and are not reachable by any input today.
  defp macro_expected_at(rule, progress) do
    case Enum.at(rule.segments, progress) do
      {:lit, w} -> {:literal, w}
      {:hole, %{kind: k}} -> {:hole_kind, k}
      {:code_hole, %{delimiter: delimiter}} -> {:code_until, delimiter}
      _ -> :nothing_more
    end
  end

  # A short human description of the token actually found at the mismatch.
  #
  # This is the single choke point for the "found `...`" clause, so its
  # result is escaped for control characters (see escape_for_diagnostic/1)
  # regardless of which case below produced it: a *content-bearing* token
  # (string, char, ...) can carry a raw newline/tab in its decoded `value`
  # just as easily as the structural tokens below carry one directly, and
  # either would splice a raw control byte into format_diagnostic's
  # single-line `| message` convention.
  defp macro_got_desc(token), do: token |> macro_got_desc_raw() |> escape_for_diagnostic()

  # Structural/whitespace tokens (:newline, :indent, :dedent) are named in
  # words rather than falling through to their raw `value` (a literal "\n"
  # byte, or a bare indentation-level integer): splicing either into the
  # message reads as meaningless ("found `2`"), even once escaped. These are
  # common mismatches (e.g. a macro keyword used bare, with nothing supplied
  # before the line ends).
  defp macro_got_desc_raw(%Token{type: :eof}), do: "end of input"
  # The `nil` keyword lexes as %Token{type: nil, value: nil} (unlike every
  # other keyword, which lexes as {:keyword, atom}) -- neither field carries
  # displayable text, so without this clause it falls through to
  # `to_string(nil)` (a literal "" empty string), rendering `found ``` .
  defp macro_got_desc_raw(%Token{type: nil}), do: "nil"
  defp macro_got_desc_raw(%Token{type: :newline}), do: "end of line"
  defp macro_got_desc_raw(%Token{type: :indent}), do: "an indent"
  defp macro_got_desc_raw(%Token{type: :dedent}), do: "a dedent"
  # A :char token's value is the decoded Unicode codepoint (e.g. 97 for 'a'),
  # not its source spelling -- render the character itself rather than the
  # bare integer. Falls through to the generic clause (numeric render) for a
  # codepoint outside the valid Unicode scalar range, so this can never raise.
  defp macro_got_desc_raw(%Token{type: :char, value: v})
       when is_integer(v) and (v in 0..0xD7FF or v in 0xE000..0x10FFFF),
       do: "'#{<<v::utf8>>}'"

  # Some tokens carry a STRUCTURED value that `to_string/1` cannot render and
  # would raise on: a :regex value is `{body, flags}`, a :string_interpolation
  # value is a list of parts. Name them by kind. The final `is_tuple/is_list`
  # guard is a future-proof backstop for any other structured-value token.
  defp macro_got_desc_raw(%Token{type: :regex}), do: "a regex literal"
  defp macro_got_desc_raw(%Token{type: :string_interpolation}), do: "an interpolated string"
  defp macro_got_desc_raw(%Token{value: v}) when is_tuple(v) or is_list(v), do: "a complex token"

  defp macro_got_desc_raw(%Token{value: v}) when not is_nil(v), do: to_string(v)
  defp macro_got_desc_raw(%Token{type: t}), do: to_string(t)

  # Escape control characters that would otherwise corrupt format_diagnostic's
  # single-line `| message` convention (e.g. a plain string literal's decoded
  # value, or a char literal's decoded value, can carry a raw "\n"/"\t" from a
  # source escape sequence such as "a\nb" or '\n').
  defp escape_for_diagnostic(s) do
    s
    |> String.replace("\r\n", "\\n")
    |> String.replace("\n", "\\n")
    |> String.replace("\r", "\\r")
    |> String.replace("\t", "\\t")
  end

  # Walk a rule's segments against the use-site tokens. A `{:lit, w}` must match
  # the next token's value; a `{:hole, %{name}}` binds `name` to a parsed
  # expression. Returns `{:ok, bindings, progress, state}` or
  # `{:error, progress, state}` (progress = segments consumed before the miss).
  @macro_match_span_key :__cure_macro_match_span__

  defp match_segments(state, [], bindings, progress), do: {:ok, bindings, progress, state}

  defp match_segments(state, [{:lit, w} | rest], bindings, progress) do
    token = peek(state)

    if lit_token_matches?(token, w) do
      match_segments(advance(state), rest, advance_macro_match(bindings, token.span), progress + 1)
    else
      {:error, progress, state}
    end
  end

  defp match_segments(state, [{:hole, %{name: name, kind: "Type"}} | rest], bindings, progress) do
    {arg, state} = parse_type_expr(state)
    match_segments(state, rest, put_macro_binding(bindings, name, arg), progress + 1)
  end

  defp match_segments(state, [{:hole, %{name: name, kind: "ModuleName"}} | rest], bindings, progress) do
    case peek(state) do
      %Token{type: :identifier} ->
        module_start = peek(state)
        {module_name, module_end, state} = parse_dotted_name_owned(state)
        module_span = through_spans(module_start.span, module_end.span) || module_start.span
        module_meta = Metadata.put_source_info([subtype: :symbol], %SourceInfo{whole: module_span})
        qualified = qualify_lifted_module_name(module_name, state.enclosing_module)
        module = {:literal, module_meta, String.to_atom(qualified)}
        match_segments(state, rest, put_macro_binding(bindings, name, module), progress + 1)

      _ ->
        {:error, progress, state}
    end
  end

  defp match_segments(state, [{:hole, %{name: name, kind: "Name"}} | rest], bindings, progress) do
    case peek(state) do
      %Token{type: :identifier} = token ->
        name_ast = variable(token)
        match_segments(advance(state), rest, put_macro_binding(bindings, name, name_ast), progress + 1)

      _ ->
        {:error, progress, state}
    end
  end

  # The production owns the surrounding parentheses. Capture their contents
  # with Cure's ordinary parameter parser so every source-defined macro can use
  # typed, graded, implicit, and multiple binders without a bespoke parser.
  defp match_segments(state, [{:hole, %{name: name, kind: "Parameters"}} | rest], bindings, progress) do
    {params, state} = parse_typed_params(state)
    match_segments(state, rest, put_macro_binding(bindings, name, params), progress + 1)
  end

  defp match_segments(state, [{:hole, %{name: name, kind: kind}} | rest], bindings, progress)
       when kind in ["Int", "Float", "Atom", "Bool"] do
    {arg, state} = parse_expr(state, 0)
    state = validate_primitive_capture(arg, kind, state)
    match_segments(state, rest, put_macro_binding(bindings, name, arg), progress + 1)
  end

  # Code holes may introduce an indented expression block after their marker
  # (`derive` newline `match ...`). The ordinary expression parser owns the
  # block tokens, so only the separator newline belongs to the grammar matcher.
  defp match_segments(state, [{:hole, %{name: name, kind: "Code"}} | rest], bindings, progress) do
    state = skip_newlines(state)
    {arg, state} = parse_expr(state, 0)
    match_segments(state, rest, put_macro_binding(bindings, name, arg), progress + 1)
  end

  # A delimiter-aware Code hole is still parsed by the ordinary expression
  # parser. The matcher temporarily replaces the delimiter with a synthetic
  # dedent so an indented code block cannot consume the next grammar literal.
  defp match_segments(
         state,
         [{:code_hole, %{name: name, delimiter: delimiter}} | rest],
         bindings,
         progress
       ) do
    case parse_code_until(state, delimiter) do
      {:ok, arg, state} ->
        match_segments(state, rest, put_macro_binding(bindings, name, arg), progress + 1)
    end
  end

  # A positional declarations block hole consumes the indented run of
  # definitions as one `:declarations_block` node — the same shape the
  # structured family `body Declarations` section produces — so a raw Tier-0
  # template body can flow through `computed`. `parse_definition_block` reads
  # from the block's `:indent` through its matching `:dedent`, so the only
  # supported delimiter is the block's own dedent.
  defp match_segments(state, [{:declarations_hole, %{name: name}} | rest], bindings, progress) do
    # A positional declarations body always begins on its OWN line: the block's
    # `:indent` (or, for an empty body, the form simply ends). So the token
    # DIRECTLY following the preceding segment must be a structural boundary.
    # If instead a same-line token follows (e.g. a sibling rule's `with`/`call`
    # keyword, as in the single-line use-sites the expansion fuzzer synthesises
    # for those siblings), this rule does not apply: report a non-match and hand
    # the ORIGINAL state back so `match_macro_rule` tries the next rule, rather
    # than greedily matching an empty body and leaving the continuation over.
    # This mirrors the `{:family}` clause's `:indent` guard while still allowing
    # a bodyless `actor <name> state <type>` (the form ends at a newline/dedent).
    case peek(state) do
      %Token{type: type} when type in [:newline, :indent, :dedent, :eof] ->
        scan_state = skip_newlines(state)
        token = peek(scan_state)
        {stmts, after_state} = parse_definition_block(scan_state)
        node = {:declarations_block, [line: token.line, col: token.col], stmts}
        match_segments(after_state, rest, put_macro_binding(bindings, name, node), progress + 1)

      _ ->
        {:error, progress, state}
    end
  end

  defp match_segments(state, [{:hole, %{name: name}} | rest], bindings, progress) do
    {arg, state} = parse_expr(state, 0)
    match_segments(state, rest, put_macro_binding(bindings, name, arg), progress + 1)
  end

  # A structured family consumes the indented body as one grammar unit. The
  # family parser then parses named sections with the ordinary Cure
  # expression/type parsers, preserving normal nested syntax and macro use.
  # The enclosing dedent remains in the token stream for the surrounding
  # declaration parser.
  defp match_segments(state, [{:family, family_meta} | rest], bindings, progress) do
    family_state = skip_newlines(state)

    case peek(family_state) do
      %Token{type: :indent} ->
        body_start = family_state |> advance() |> skip_newlines()

        case peek(body_start) do
          %Token{type: :keyword} ->
            {:error, progress, state}

          %Token{type: :identifier, value: field_name} ->
            if Enum.any?(family_meta.fields, fn field ->
                 field.name == field_name or
                   (Map.has_key?(field, :grammar) and field.cardinality in [:repeated, :one_or_more])
               end) do
              {captured, state} = capture_family_body(state)
              {family_value, parsed_state} = parse_family_body(captured, family_meta, state)

              state = %{
                state
                | errors: state.errors ++ parsed_state.errors,
                  fresh_counter: parsed_state.fresh_counter
              }

              match_segments(state, rest, put_macro_binding(bindings, family_meta.name, family_value), progress + 1)
            else
              {:error, progress, state}
            end

          _ ->
            {:error, progress, state}
        end

      _ ->
        {:error, progress, state}
    end
  end

  # Raw holes are the reader-tier escape hatch: capture the token span without
  # asking the ordinary expression parser to interpret it. Structural
  # delimiters belong to the enclosing parser, so `dedent`/`newline` remain in
  # the stream while punctuation delimiters are consumed by the macro rule.
  defp match_segments(
         state,
         [{:raw_hole, %{name: name, delimiter: delimiter} = hole_meta} | rest],
         bindings,
         progress
       ) do
    remaining = tokens_from(state, state.pos)

    case MacroRaw.capture(remaining, delimiter) do
      {:ok, captured, _rest} ->
        state = advance_n(state, length(captured) + if(consume_raw_delimiter?(delimiter), do: 1, else: 0))
        raw_meta = [line: raw_line(captured, state), delimiter: delimiter]
        raw_meta = if hole_meta[:delayed], do: Keyword.put(raw_meta, :delayed, true), else: raw_meta
        raw = {:raw_tokens, raw_meta, captured}
        match_segments(state, rest, put_macro_binding(bindings, name, raw), progress + 1)

      {:error, {:missing_raw_delimiter, "dedent"}} ->
        # A top-level built-in macro may end at EOF without an indentation
        # delimiter. Treat the remaining newline/trivia as an empty body and
        # leave EOF for the enclosing program parser.
        captured = Enum.take_while(remaining, &match?(%Token{type: :newline}, &1))
        state = advance_n(state, length(captured))
        raw_meta = [line: raw_line(captured, state), delimiter: delimiter]
        raw_meta = if hole_meta[:delayed], do: Keyword.put(raw_meta, :delayed, true), else: raw_meta
        raw = {:raw_tokens, raw_meta, captured}
        match_segments(state, rest, put_macro_binding(bindings, name, raw), progress + 1)

      {:error, _} ->
        {:error, progress, state}
    end
  end

  defp match_segments(state, [{:repeat, segment} | rest], bindings, progress) do
    {values, state, repeated_span} = match_repeated_segment(state, segment, bindings, [], nil)
    bindings = put_repeated_binding(bindings, segment, values)
    bindings = advance_macro_match(bindings, repeated_span)
    match_segments(state, rest, bindings, progress + 1)
  end

  defp match_segments(state, [{:optional, group} | rest], bindings, progress) do
    if optional_group_present?(state, group) do
      case match_segments(state, group, bindings, progress) do
        {:ok, bindings, _group_progress, matched_state} ->
          match_segments(matched_state, rest, bindings, progress + 1)

        {:error, _group_progress, _matched_state} ->
          match_segments(state, rest, bindings, progress + 1)
      end
    else
      match_segments(state, rest, bindings, progress + 1)
    end
  end

  # Do not invoke an expression/raw parser merely to discover that an optional
  # group is absent. At a structural boundary that parser would record a
  # spurious error on the enclosing form, even though absence is valid.
  defp optional_group_present?(state, [{:lit, word} | _]), do: lit_token_matches?(peek(state), word)

  defp optional_group_present?(state, [{kind, _meta} | _]) when kind in [:hole, :raw_hole] do
    not match?(%Token{type: type} when type in [:newline, :dedent, :eof], peek(state))
  end

  defp optional_group_present?(state, [{:code_hole, _meta} | _]) do
    not match?(%Token{type: type} when type in [:newline, :dedent, :eof], peek(state))
  end

  defp optional_group_present?(state, [{:repeat, segment} | _]),
    do: optional_group_present?(state, [segment])

  defp optional_group_present?(state, [{:optional, segments} | _]),
    do: optional_group_present?(state, segments)

  defp optional_group_present?(_state, []), do: false

  defp match_repeated_segment(state, {:hole, %{name: name}}, bindings, acc, last_span) do
    case peek(state) do
      %Token{type: type} when type in [:newline, :dedent, :eof] ->
        {Enum.reverse(acc), state, last_span}

      _ ->
        {arg, state} = parse_expr(state, 0)
        match_repeated_segment(state, {:hole, %{name: name}}, bindings, [arg | acc], macro_value_span(arg) || last_span)
    end
  end

  defp match_repeated_segment(state, {:lit, word}, _bindings, acc, last_span) do
    token = peek(state)

    if lit_token_matches?(token, word) do
      match_repeated_segment(advance(state), {:lit, word}, %{}, [word | acc], token.span)
    else
      {Enum.reverse(acc), state, last_span}
    end
  end

  defp match_repeated_segment(state, _segment, _bindings, acc, last_span),
    do: {Enum.reverse(acc), state, last_span}

  defp put_repeated_binding(bindings, {:hole, %{name: name}}, values), do: Map.put(bindings, name, values)
  defp put_repeated_binding(bindings, _segment, _values), do: bindings

  defp put_macro_binding(bindings, name, value) do
    bindings
    |> Map.put(name, value)
    |> advance_macro_match(macro_value_span(value))
  end

  defp advance_macro_match(bindings, nil), do: bindings

  defp advance_macro_match(bindings, %Cure.Diagnostic.Span{} = span) do
    case Map.get(bindings, @macro_match_span_key) do
      %Cure.Diagnostic.Span{end_byte: end_byte} when end_byte >= span.end_byte -> bindings
      _ -> Map.put(bindings, @macro_match_span_key, span)
    end
  end

  defp macro_match_span(bindings), do: Map.get(bindings, @macro_match_span_key)

  defp macro_value_span({:raw_tokens, _meta, tokens}) when is_list(tokens), do: token_list_span(tokens)

  defp macro_value_span({:declarations_block, _meta, declarations}) when is_list(declarations),
    do: source_values_span(declarations)

  defp macro_value_span(value) when is_list(value), do: source_values_span(value)

  defp macro_value_span(%Cure.Diagnostic.Span{} = span), do: span

  defp macro_value_span(value) when is_map(value) do
    value
    |> Map.values()
    |> source_values_span()
  end

  defp macro_value_span(value), do: ast_source_span(value)

  defp source_values_span(values) do
    spans = values |> Enum.map(&macro_value_span/1) |> Enum.reject(&is_nil/1)
    through_spans(List.first(spans), List.last(spans)) || List.last(spans)
  end

  defp token_list_span(tokens) do
    spans = tokens |> Enum.map(& &1.span) |> Enum.reject(&is_nil/1)
    through_spans(List.first(spans), List.last(spans)) || List.last(spans)
  end

  defp capture_family_body(state) do
    remaining = tokens_from(state, state.pos)
    target_indent = Enum.find_value(remaining, &indent_value/1)

    case target_indent do
      nil ->
        count = Enum.find_index(remaining, &match?(%Token{type: :eof}, &1)) || length(remaining)
        {Enum.take(remaining, count), advance_n(state, count)}

      target_indent ->
        count =
          remaining
          |> Enum.with_index()
          |> Enum.find_value(length(remaining), fn
            {%Token{type: :dedent, value: ^target_indent}, index} -> index
            _ -> nil
          end)

        {Enum.take(remaining, count), advance_n(state, count)}
    end
  end

  defp indent_value(%Token{type: :indent, value: value}) when is_integer(value), do: value
  defp indent_value(_token), do: nil

  defp parse_family_body(tokens, family_meta, parser_state) do
    target_indent = Enum.find_value(tokens, &indent_value/1) || 0
    family_meta = Map.put(family_meta, :body_span, family_body_span(tokens))

    # Built against `parser_state` before its tokens are swapped out.
    family_tokens =
      tokens ++ [%Token{type: :dedent, value: target_indent, line: 0, col: 0}, eof_token(peek(parser_state))]

    family_state =
      put_tokens(
        %{parser_state | pos: 0, errors: [], fresh_counter: parser_state.fresh_counter},
        family_tokens
      )

    family_state = skip_newlines(family_state)

    case peek(family_state) do
      %Token{type: :indent} ->
        {value, family_state} = parse_family_sections(advance(family_state), family_meta, %{})
        {value, family_state}

      token ->
        family_state =
          add_error(
            family_state,
            {:syntax_family_body_syntax,
             %{
               kind: :syntax_family_body_indent_missing,
               family: family_meta.family,
               valid_fields: Enum.map(family_meta.fields, & &1.name),
               expected: :indent,
               observed: macro_separator_observed(token),
               token_type: token.type,
               span: zero_width_start(token.span),
               observed_span: token.span,
               body_span: Map.get(family_meta, :body_span),
               line: token.line,
               column: token.col
             }}
          )

        family_value(family_meta, %{}, family_state)
    end
  end

  defp parse_family_sections(state, family_meta, values) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        family_value(family_meta, values, state)

      %Token{type: type, value: name} = token when type in [:identifier, :keyword] ->
        field_name = to_string(name)

        case Enum.find(family_meta.fields, &(&1.name == field_name)) do
          nil ->
            case parse_bare_family_production(state, family_meta) do
              {:ok, field, value, state} ->
                {values, state} = record_family_value(values, field, value, token, state)
                parse_family_sections(state, family_meta, values)

              :error ->
                state =
                  add_error(state, {
                    :unknown_syntax_family_field,
                    %{
                      family: family_meta.family,
                      field: name,
                      valid_fields: Enum.map(family_meta.fields, & &1.name),
                      span: token.span,
                      line: token.line,
                      column: token.col
                    }
                  })

                {_ignored, state} = parse_expr_or_block(advance(state))
                parse_family_sections(state, family_meta, values)
            end

          field ->
            # Structured family fields use declaration-style assignment in
            # the surface language (`strategy = ...`). The family schema
            # describes the value after the field name, so consume the
            # optional separator here rather than making every family repeat
            # it in its grammar.
            state = consume_family_field_separator(advance(state))
            {value, state} = parse_family_field_value(state, field)
            {values, state} = record_family_value(values, field, value, token, state)
            parse_family_sections(state, family_meta, values)
        end

      token ->
        case parse_bare_family_production(state, family_meta) do
          {:ok, field, value, state} ->
            {values, state} = record_family_value(values, field, value, token, state)
            parse_family_sections(state, family_meta, values)

          :error ->
            state =
              add_error(
                state,
                {:syntax_family_body_syntax,
                 %{
                   kind: :syntax_family_entry_invalid,
                   family: family_meta.family,
                   valid_fields: Enum.map(family_meta.fields, & &1.name),
                   expected: family_meta.fields |> List.first() |> then(&(&1 && &1.name)),
                   observed: macro_separator_observed(token),
                   token_type: token.type,
                   span: token.span,
                   previous_span: previous_authored_span(state, nil),
                   body_span: Map.get(family_meta, :body_span),
                   line: token.line,
                   column: token.col
                 }}
              )

            parse_family_sections(advance(state), family_meta, values)
        end
    end
  end

  defp parse_bare_family_production(state, family_meta) do
    family_meta.fields
    |> Enum.filter(&(Map.has_key?(&1, :grammar) and &1.cardinality in [:repeated, :one_or_more]))
    |> Enum.find_value(:error, fn field ->
      case parse_family_production(state, field.grammar) do
        {:ok, value, matched_state} -> {:ok, field, value, matched_state}
        :error -> nil
      end
    end)
  end

  defp parse_family_production(state, grammar) do
    Enum.find_value(grammar.productions, :error, fn production ->
      case match_bare_family_production(state, grammar, production) do
        {:ok, value, matched_state} ->
          {:ok, value, matched_state}

        :none ->
          case match_segments(state, production.segments, %{}, 0) do
            {:ok, bindings, _progress, matched_state} ->
              case peek(matched_state) do
                %Token{type: type} when type in [:newline, :dedent, :eof] ->
                  production_values = Map.take(bindings, production.fields)
                  {value, matched_state} = parse_production_body(matched_state, grammar, production_values)
                  {:ok, value, matched_state}

                _ ->
                  nil
              end

            _ ->
              nil
          end
      end
    end)
  end

  # A family production may use the conventional `kind module as identity`
  # spelling while allowing the kind to be omitted for the common worker case:
  # `module as identity`. Keep this compatibility in the generic matcher so
  # source-defined families do not need a second production with a different
  # field prefix (which would change the generated family record shape).
  defp match_bare_family_production(
         state,
         grammar,
         %{segments: [{:hole, _}, {:hole, module_hole}, {:lit, "as"} | rest]} = production
       ) do
    case match_segments(state, [{:hole, module_hole}, {:lit, "as"} | rest], %{}, 0) do
      {:ok, bindings, _progress, matched_state} ->
        case peek(matched_state) do
          %Token{type: type} when type in [:newline, :dedent, :eof] ->
            production_values = Map.put(Map.take(bindings, production.fields), "kind", nil)
            {value, matched_state} = parse_production_body(matched_state, grammar, production_values)
            {:ok, value, matched_state}

          _ ->
            :none
        end

      _ ->
        :none
    end
  end

  defp match_bare_family_production(_state, _grammar, _production), do: :none

  defp parse_production_body(state, grammar, values) do
    nested_state = skip_newlines(state)

    case peek(nested_state) do
      %Token{type: :indent} ->
        {value, nested_state} = parse_family_sections(advance(nested_state), grammar, values)
        {value, expect_dedent(nested_state)}

      _ ->
        family_value(grammar, values, state)
    end
  end

  defp parse_family_field_value(state, %{shape: "Type"}) do
    state = skip_newlines(state)
    parse_type_expr(state)
  end

  defp parse_family_field_value(state, %{shape: "ModuleName"}) do
    state = skip_newlines(state)
    {name, state} = parse_dotted_name(state)
    qualified = qualify_lifted_module_name(name, state.enclosing_module)
    {{:literal, [subtype: :symbol], String.to_atom(qualified)}, state}
  end

  defp parse_family_field_value(state, %{shape: shape}) when shape in ["Int", "Float", "Atom", "Bool"] do
    state = skip_newlines(state)
    {value, state} = parse_expr(state, 0)
    {value, validate_primitive_capture(value, shape, state)}
  end

  defp parse_family_field_value(state, %{shape: "Cases"}) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :indent} = indent ->
        {arms, state} = parse_block_match_arms(advance(state))
        state = expect_dedent(state)
        {{:case_block, [line: indent.line, col: indent.col], arms}, state}

      _ ->
        {arm, state} = parse_match_arm(state)
        {{:case_block, [], [arm]}, state}
    end
  end

  defp parse_family_field_value(state, %{shape: "Declarations"}) do
    state = skip_newlines(state)
    token = peek(state)
    {stmts, state} = parse_definition_block(state)
    {{:declarations_block, [line: token.line, col: token.col], stmts}, state}
  end

  # A named repeated production field is an indented collection of that
  # family's rows. This is the structured spelling of the already-supported
  # bare production form:
  #
  #     children
  #       actor Counter as CounterChild
  #       supervisor Workers as WorkersChild
  #
  # The parser remains domain-neutral: `children`, `actor`, and `supervisor`
  # are merely literals from the source-defined family metadata. Each row may
  # itself own an optional indented production body.
  defp parse_family_field_value(
         state,
         %{grammar: grammar, cardinality: cardinality} = field
       )
       when cardinality in [:repeated, :one_or_more] do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :indent} ->
        {values, state} = parse_family_production_entries(advance(state), field, [])
        {{:family_repeated_values, values}, expect_dedent(state)}

      # `children []` is the explicit empty spelling for a structured repeated
      # field. It predates syntax families and remains useful for deliberately
      # childless supervisors; do not feed it to the row grammar, where `[` is
      # correctly not the start of a production.
      %Token{type: :lbracket} ->
        case peek_at(state, 1) do
          %Token{type: :rbracket} ->
            {{:family_repeated_values, []}, advance_n(state, 2)}

          _ ->
            token = peek(state)

            state = add_family_production_error(state, token, field)

            {{:family_repeated_values, []}, state}
        end

      _ ->
        case parse_family_production(state, grammar) do
          {:ok, value, state} ->
            {{:family_repeated_values, [value]}, state}

          :error ->
            token = peek(state)

            state = add_family_production_error(state, token, field)

            {{:family_repeated_values, []}, state}
        end
    end
  end

  defp parse_family_field_value(state, _field) do
    state = skip_newlines(state)
    parse_expr_or_block(state)
  end

  defp consume_family_field_separator(state) do
    case peek(state) do
      %Token{type: :assign} -> advance(state)
      _ -> state
    end
  end

  defp parse_family_production_entries(state, %{grammar: grammar} = field, values) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(values), state}

      token ->
        case parse_family_production(state, grammar) do
          {:ok, value, state} ->
            parse_family_production_entries(state, field, [value | values])

          :error ->
            state = add_family_production_error(state, token, field)

            {_ignored, state} = parse_expr_or_block(advance(state))
            parse_family_production_entries(state, field, values)
        end
    end
  end

  defp add_family_production_error(state, token, field) do
    grammar = Map.fetch!(field, :grammar)

    add_error(
      state,
      {:syntax_family_body_syntax,
       %{
         kind: :syntax_family_production_invalid,
         family: Map.get(grammar, :family),
         field: Map.get(field, :name),
         expected: :syntax_family_production,
         observed: macro_separator_observed(token),
         token_type: token.type,
         span: token.span,
         previous_span: previous_authored_span(state, nil),
         line: token.line,
         column: token.col
       }}
    )
  end

  defp record_family_value(
         values,
         %{name: name, cardinality: cardinality},
         {:family_repeated_values, entries},
         _token,
         state
       )
       when cardinality in [:repeated, :one_or_more] do
    {Map.update(values, name, entries, &(&1 ++ entries)), state}
  end

  defp record_family_value(values, %{name: name, cardinality: cardinality}, value, _token, state)
       when cardinality in [:repeated, :one_or_more] do
    {Map.update(values, name, [value], &(&1 ++ [value])), state}
  end

  defp record_family_value(values, %{name: name, cardinality: :optional}, value, _token, state) do
    {Map.put(values, name, {:family_option, [present: true], [value]}), state}
  end

  defp record_family_value(values, %{name: name}, value, token, state) do
    if Map.has_key?(values, name) do
      first_span = previous_family_field_span(state, name, token.span)

      {values,
       add_error(state, {
         :duplicate_syntax_family_field,
         %{
           field: name,
           span: token.span,
           first_span: first_span,
           line: token.line,
           column: token.col
         }
       })}
    else
      {Map.put(values, name, value), state}
    end
  end

  defp previous_family_field_span(state, name, current_span) do
    tokens = if is_tuple(state.tokens), do: Tuple.to_list(state.tokens), else: state.tokens

    tokens
    |> Enum.take(state.pos)
    |> Enum.reverse()
    |> Enum.find_value(fn
      %Token{type: type, value: value, span: %Cure.Diagnostic.Span{} = span}
      when type in [:identifier, :keyword] ->
        if to_string(value) == to_string(name) and span != current_span, do: span

      _ ->
        nil
    end)
  end

  defp family_body_span(tokens) do
    tokens
    |> Enum.reject(&(&1.type in [:newline, :indent, :dedent, :eof]))
    |> authored_token_span()
  end

  defp family_value(family_meta, values, state) do
    {fields, state} =
      Enum.map_reduce(family_meta.fields, state, fn field, state ->
        case Map.fetch(values, field.name) do
          {:ok, value} ->
            {value, state}

          :error when field.cardinality == :repeated ->
            {[], state}

          :error when field.cardinality == :optional ->
            {{:family_option, [present: false], []}, state}

          :error when field.cardinality == :one_or_more ->
            error =
              {:missing_syntax_family_field,
               %{
                 family: family_meta.family,
                 field: field.name,
                 span: insertion_at_end(Map.get(family_meta, :body_span)),
                 body_span: Map.get(family_meta, :body_span),
                 line: field.line,
                 column: field.col
               }}

            {[], add_error(state, error)}

          :error ->
            error =
              {:missing_syntax_family_field,
               %{
                 family: family_meta.family,
                 field: field.name,
                 span: insertion_at_end(Map.get(family_meta, :body_span)),
                 body_span: Map.get(family_meta, :body_span),
                 line: field.line,
                 column: field.col
               }}

            {nil, add_error(state, error)}
        end
      end)

    {{:family_input, [family: family_meta.family], fields}, state}
  end

  defp validate_primitive_capture({:literal, meta, _value}, shape, state) do
    expected =
      case shape do
        "Int" -> :integer
        "Float" -> :float
        "Atom" -> :symbol
        "Bool" -> :boolean
      end

    if Keyword.get(meta, :subtype) == expected do
      state
    else
      value = {:literal, meta, nil}

      add_error(state, {
        :expected_literal_capture,
        %{
          shape: shape,
          span: first_node_source_span(value),
          line: Keyword.get(meta, :line, 0),
          column: Keyword.get(meta, :col, 0)
        }
      })
    end
  end

  defp validate_primitive_capture(_value, shape, state),
    do:
      add_error(state, {
        :expected_literal_capture,
        %{shape: shape, span: peek(state).span, line: peek(state).line, column: peek(state).col}
      })

  defp insertion_at_end(%Cure.Diagnostic.Span{} = span) do
    %{
      span
      | start_byte: span.end_byte,
        start_line: span.end_line,
        start_column: span.end_column
    }
  end

  defp insertion_at_end(_span), do: nil

  defp advance_n(state, 0), do: state
  defp advance_n(state, count), do: advance_n(advance(state), count - 1)

  defp consume_raw_delimiter?(delimiter), do: delimiter not in ["dedent", "newline"]

  defp parse_code_until(state, delimiter) do
    remaining = tokens_from(state, state.pos)

    case split_code_until(remaining, delimiter, nil, []) do
      {:ok, prefix, delimiter_token} ->
        boundary = code_boundary_token(prefix, delimiter_token)
        parse_state = put_tokens(%{state | pos: 0}, prefix ++ [boundary, eof_token(delimiter_token)])
        parse_state = skip_newlines(parse_state)
        {arg, parse_state} = parse_expr(parse_state, 0)
        state = %{state | errors: parse_state.errors, fresh_counter: parse_state.fresh_counter}
        {:ok, arg, %{state | pos: state.pos + length(prefix)}}

      :missing ->
        state = skip_newlines(state)
        {arg, state} = parse_expr(state, 0)
        {:ok, arg, state}
    end
  end

  defp split_code_until([], _delimiter, _previous, _acc), do: :missing

  defp split_code_until([token | rest], delimiter, previous, acc) do
    if code_until_delimiter?(token, delimiter, previous, List.first(rest)) do
      {:ok, Enum.reverse(acc), token}
    else
      split_code_until(rest, delimiter, token, [token | acc])
    end
  end

  defp code_until_delimiter?(%Token{} = token, delimiter, previous, next) do
    token_matches?(token, delimiter) and
      match?(%Token{type: type} when type in [:newline, :dedent], previous) and
      match?(%Token{type: type} when type in [:newline, :dedent, :eof], next)
  end

  defp token_matches?(%Token{type: type, value: value}, delimiter) do
    to_string(type) == delimiter or (is_binary(value) and value == delimiter)
  end

  defp code_boundary_token(prefix, delimiter_token) do
    indent = Enum.find(prefix, &match?(%Token{type: :indent}, &1))

    case indent do
      %Token{value: value} when is_integer(value) ->
        %Token{type: :dedent, value: value, line: delimiter_token.line, col: delimiter_token.col}

      _ ->
        eof_token(delimiter_token)
    end
  end

  defp eof_token(token), do: %Token{type: :eof, value: nil, line: token.line, col: token.col}

  defp raw_line([%Token{line: line} | _], _state), do: line
  defp raw_line([], state), do: peek(state).line

  # A literal segment matches a token whose text equals the segment word. Only
  # scalar token values (binary/atom/number) have text; a structured value —
  # a :regex is `{body, flags}`, a :string_interpolation is a list of parts —
  # can never equal a literal word AND crashes `to_string/1`, so it simply does
  # not match (falling to the mismatch path → the default diagnostic).
  defp lit_token_matches?(%Token{value: v}, w) when is_binary(v), do: v == w
  defp lit_token_matches?(%Token{value: v}, w) when is_atom(v) and not is_nil(v), do: to_string(v) == w
  defp lit_token_matches?(%Token{value: v}, w) when is_number(v), do: to_string(v) == w
  defp lit_token_matches?(_tok, _w), do: false

  # Expand a rule: freshen its `<fresh Name>` markers to per-expansion gensyms
  # BEFORE substituting holes (so use-site hole material is never freshened),
  # then substitute the bound holes. Returns `{expanded_ast, state}` — the
  # freshening counter threads back out to the caller.
  defp expand_rule(rule, bindings, state) do
    expand_template_rule(rule, bindings, state)
  end

  defp expand_template_rule(rule, bindings, state) do
    {freshened, state} = freshen(rule.template, state, true, bindings)
    expanded = subst_holes(freshened, bindings, state)
    expanded = attach_lexical_imports(expanded, Map.get(rule, :lexical_imports, []))

    case Cure.Compiler.MacroSyntax.lower_internal(expanded) do
      {:ok, ast} ->
        {ast, state}

      :not_internal ->
        {expanded, state}
    end
  end

  defp put_computed_use_source_info(meta, %Token{} = keyword_token, rule, bindings) do
    frame =
      macro_expansion_frame(
        Map.get(rule, :keyword, keyword_token.value),
        keyword_token.span,
        Map.get(rule, :source_span),
        macro_match_span(bindings)
      )

    case frame.invocation do
      %Cure.Diagnostic.Span{} = invocation ->
        Keyword.put(meta, :source_info, %SourceInfo{
          whole: invocation,
          name: keyword_token.span,
          provenance: [frame]
        })

      _ ->
        meta
    end
  end

  defp macro_expansion_frame(name, %Cure.Diagnostic.Span{} = first, definition, last_span) do
    invocation = through_spans(first, last_span) || first

    %ProvenanceFrame{
      kind: :macro_expansion,
      name: name || "macro",
      invocation: invocation,
      definition: definition
    }
  end

  defp macro_expansion_frame(name, _first, definition, _last_span) do
    %ProvenanceFrame{kind: :macro_expansion, name: name || "macro", definition: definition}
  end

  # Template expansion is a structural copy followed by substitution. Preserve
  # every authored role on both the copied template and captured use-site nodes;
  # provenance is additive and never replaces either node's `whole` identity.
  # Nodes synthesized by the expansion receive provenance with `whole: nil`.
  defp append_macro_provenance({tag, meta, children}, %ProvenanceFrame{} = frame)
       when is_atom(tag) and is_list(meta) do
    meta =
      meta
      |> Enum.map(fn
        {:source_info, %SourceInfo{} = info} -> {:source_info, info}
        {key, value} -> {key, append_macro_provenance_value(value, frame)}
        other -> other
      end)
      |> append_source_info_provenance(frame)

    {tag, meta, append_macro_provenance_value(children, frame)}
  end

  defp append_macro_provenance(value, %ProvenanceFrame{} = frame),
    do: append_macro_provenance_value(value, frame)

  defp append_macro_provenance_value({tag, meta, _children} = node, frame)
       when is_atom(tag) and is_list(meta),
       do: append_macro_provenance(node, frame)

  defp append_macro_provenance_value(tuple, frame) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.map(&append_macro_provenance_value(&1, frame))
    |> List.to_tuple()
  end

  defp append_macro_provenance_value(list, frame) when is_list(list),
    do: Enum.map(list, &append_macro_provenance_value(&1, frame))

  defp append_macro_provenance_value(%_{} = struct, _frame), do: struct

  defp append_macro_provenance_value(map, frame) when is_map(map) do
    Map.new(map, fn {key, value} ->
      {append_macro_provenance_value(key, frame), append_macro_provenance_value(value, frame)}
    end)
  end

  defp append_macro_provenance_value(other, _frame), do: other

  defp append_source_info_provenance(meta, frame) do
    info = Metadata.source_info(meta) || %SourceInfo{}
    parent = provenance_parent(frame)

    inherited =
      Enum.map(info.provenance, fn
        %ProvenanceFrame{parent: nil} = existing -> %{existing | parent: parent}
        existing -> existing
      end)

    provenance =
      (inherited ++ [frame])
      |> Enum.uniq_by(&provenance_identity/1)

    Keyword.put(meta, :source_info, %{info | provenance: provenance})
  end

  defp provenance_parent(%ProvenanceFrame{} = frame),
    do: %{kind: frame.kind, name: frame.name, invocation: frame.invocation}

  defp provenance_identity(%ProvenanceFrame{} = frame),
    do: {frame.kind, frame.name, frame.invocation, frame.definition, frame.generated}

  defp provenance_identity(other), do: other

  defp attach_lexical_imports({:lift_module, meta, children}, imports) when is_list(meta) and is_list(imports) do
    declarations = Keyword.get(meta, :declarations, [])
    existing = MapSet.new(declarations, &import_declaration_key/1)

    generated_imports =
      for {:import, _meta, _children} = declaration <- imports,
          not MapSet.member?(existing, import_declaration_key(declaration)),
          do: declaration

    declarations = generated_imports ++ declarations
    aliases = import_aliases(imports ++ declarations)
    node = {:lift_module, Keyword.put(meta, :declarations, declarations), children}
    qualify_lexical_aliases(node, aliases)
  end

  defp attach_lexical_imports(ast, _imports), do: ast

  defp import_aliases(imports) do
    for {:import, meta, _children} <- imports,
        is_list(meta),
        alias_name = Keyword.get(meta, :alias),
        source = Keyword.get(meta, :source),
        is_binary(alias_name),
        is_binary(source),
        into: %{} do
      {alias_name, source}
    end
  end

  defp qualify_lexical_aliases({:function_call, meta, children}, aliases) when is_list(meta) do
    meta =
      case Keyword.get(meta, :name) do
        name when is_binary(name) -> Keyword.put(meta, :name, qualify_dotted_name(name, aliases))
        _ -> meta
      end

    {:function_call, meta, Enum.map(children, &qualify_lexical_aliases(&1, aliases))}
  end

  defp qualify_lexical_aliases({:attribute_access, meta, [inner]}, aliases) when is_list(meta) do
    node = {:attribute_access, meta, [qualify_lexical_aliases(inner, aliases)]}

    case dotted_parts(node) do
      [head | tail] when is_binary(head) and is_map_key(aliases, head) ->
        build_dotted(String.split(Map.fetch!(aliases, head), ".") ++ tail)

      _ ->
        node
    end
  end

  defp qualify_lexical_aliases({tag, meta, children}, aliases) when is_list(meta) and is_list(children),
    do: {tag, qualify_lexical_aliases_meta(meta, aliases), Enum.map(children, &qualify_lexical_aliases(&1, aliases))}

  defp qualify_lexical_aliases(list, aliases) when is_list(list),
    do: Enum.map(list, &qualify_lexical_aliases(&1, aliases))

  defp qualify_lexical_aliases(other, _aliases), do: other

  defp qualify_lexical_aliases_meta(meta, aliases) do
    Enum.map(meta, fn
      {key, value} -> {key, qualify_lexical_aliases_meta_value(key, value, aliases)}
      other -> other
    end)
  end

  defp qualify_lexical_aliases_meta_value(:name, value, aliases) when is_binary(value),
    do: qualify_dotted_name(value, aliases)

  defp qualify_lexical_aliases_meta_value(_key, value, aliases) when is_tuple(value),
    do: qualify_lexical_aliases(value, aliases)

  defp qualify_lexical_aliases_meta_value(_key, value, aliases) when is_list(value),
    do: Enum.map(value, &qualify_lexical_aliases_meta_value(nil, &1, aliases))

  defp qualify_lexical_aliases_meta_value(_key, value, _aliases), do: value

  defp qualify_dotted_name(name, aliases) do
    case String.split(name, ".") do
      [head | tail] when is_map_key(aliases, head) ->
        Enum.join(String.split(Map.fetch!(aliases, head), ".") ++ tail, ".")

      _ ->
        name
    end
  end

  defp dotted_parts({:variable, _meta, name}) when is_binary(name), do: [name]

  defp dotted_parts({:attribute_access, meta, [inner]}) when is_list(meta) do
    case dotted_parts(inner) do
      nil -> nil
      parts -> parts ++ [Keyword.get(meta, :attribute)]
    end
  end

  defp dotted_parts(_other), do: nil

  defp build_dotted([head | tail]) do
    Enum.reduce(tail, {:variable, [scope: :local], head}, fn segment, acc ->
      {:attribute_access, [attribute: segment], [acc]}
    end)
  end

  defp import_declaration_key({:import, meta, _children}) when is_list(meta) do
    {Keyword.get(meta, :source), Keyword.get(meta, :items, []), Keyword.get(meta, :alias)}
  end

  defp import_declaration_key(other), do: other

  # Mint one deterministic gensym per distinct declared fresh name, then rewrite
  # markers and, for templates, plain references of those names. Counter lives
  # in parser state so gensyms are stable within a build (design §5) and unique
  # across use-sites.
  defp freshen(template, state, rewrite_plain?, bindings \\ %{})

  # Computed-macro path (`freshen_generated`, rewrite_plain? = false): rewrite
  # ONLY explicit `<fresh Name>` markers to gensyms; reflected plain variables are
  # left untouched (they are reflected use-site data, not template binders). This
  # is the flat, marker-only pass — auto-hygiene does NOT apply to generated ASTs.
  defp freshen(template, state, false, bindings) do
    names = collect_fresh_names(template) |> MapSet.to_list() |> Enum.sort()
    used = collect_used_names(bindings)

    {rename, state} =
      Enum.reduce(names, {%{}, state}, fn n, {m, s} ->
        {gensym, s} = mint_gensym(n, s, used)
        {Map.put(m, n, gensym), s}
      end)

    {apply_freshening(template, rename), state}
  end

  # Template path (Tier-2 `becomes`, rewrite_plain? = true): SP5.3 auto full
  # hygiene. A scope-aware walk auto-renames EVERY unannotated ordinary binder
  # (`let`/pattern/lambda/fn-def/comprehension), plus explicit `<fresh>` markers,
  # threading a per-scope rename map so shadowing re-mints and references track
  # their binder. `<capture Name>` binders opt OUT (bind into caller scope). Holes
  # are never renamed (use-site material, substituted afterwards). Maps are never
  # walked, keeping the OTP lift-module OUT set a no-op (design §4).
  defp freshen(template, state, true, bindings) do
    holes = MapSet.new(Map.keys(bindings))
    used = collect_used_names(bindings)
    scoped_freshen(template, %{}, holes, used, state)
  end

  # Mint "n$<counter>", advancing the state counter on each attempt, and skip any
  # candidate that collides with a name appearing in the use-site material
  # (`used`). Without this a caller can spoof the gensym namespace — pass a
  # backtick identifier `g$0` as a hole — and be captured by the template's own
  # `<fresh g>` binder. Termination: `used` is finite and the counter is strictly
  # monotonic, so a free candidate is reached in at most |used| + 1 steps.
  defp mint_gensym(name, state, used) do
    candidate = "#{name}$#{state.fresh_counter}"
    state = %{state | fresh_counter: state.fresh_counter + 1}

    if MapSet.member?(used, candidate) do
      mint_gensym(name, state, used)
    else
      {candidate, state}
    end
  end

  # Names appearing anywhere in the use-site material bound to holes. A fresh
  # binder must avoid every one so injected caller identifiers cannot be captured
  # (see mint_gensym). We collect plain variable names and raw-token identifier
  # values; over-collection is harmless (it only advances the counter).
  defp collect_used_names(bindings) do
    Enum.reduce(bindings, MapSet.new(), fn {_hole, value}, acc ->
      MapSet.union(acc, collect_used_value(value))
    end)
  end

  defp collect_used_value({:variable, _meta, name}) when is_binary(name),
    do: MapSet.new([name])

  defp collect_used_value({:raw_tokens, _meta, tokens}), do: raw_token_names(tokens)

  defp collect_used_value({_t, meta, ch}) when is_list(ch) do
    Enum.reduce(ch, collect_used_meta(meta), fn c, acc ->
      MapSet.union(acc, collect_used_value(c))
    end)
  end

  defp collect_used_value(list) when is_list(list),
    do: Enum.reduce(list, MapSet.new(), &MapSet.union(&2, collect_used_value(&1)))

  defp collect_used_value(_), do: MapSet.new()

  defp collect_used_meta(meta) when is_list(meta) do
    Enum.reduce(meta, MapSet.new(), fn
      {_k, v}, acc -> MapSet.union(acc, collect_used_value(v))
      _, acc -> acc
    end)
  end

  defp collect_used_meta(_), do: MapSet.new()

  defp raw_token_names(tokens) when is_list(tokens) do
    Enum.reduce(tokens, MapSet.new(), fn
      %Token{type: :identifier, value: v}, acc when is_binary(v) -> MapSet.put(acc, v)
      _, acc -> acc
    end)
  end

  defp raw_token_names(_), do: MapSet.new()

  defp collect_fresh_names({:fresh_name, _meta, name}), do: MapSet.new([name])

  defp collect_fresh_names({_t, meta, ch}) when is_list(ch) do
    Enum.reduce(ch, collect_fresh_names_meta(meta), fn c, acc ->
      MapSet.union(acc, collect_fresh_names(c))
    end)
  end

  defp collect_fresh_names(_), do: MapSet.new()

  # Fresh markers can hide in meta (e.g. a match-arm guard), same reason
  # subst_holes walks meta. A meta VALUE can itself be a raw list of AST nodes
  # rather than a single tuple (e.g. a `with`-rematch arm's `:parent_patterns`),
  # so split on is_tuple/is_list exactly like subst_holes_meta_value.
  defp collect_fresh_names_meta(meta) when is_list(meta) do
    Enum.reduce(meta, MapSet.new(), fn
      {_k, v}, acc -> MapSet.union(acc, collect_fresh_names_value(v))
      _, acc -> acc
    end)
  end

  defp collect_fresh_names_meta(_), do: MapSet.new()

  defp collect_fresh_names_value(v) when is_tuple(v), do: collect_fresh_names(v)

  defp collect_fresh_names_value(v) when is_list(v),
    do: Enum.reduce(v, MapSet.new(), &MapSet.union(&2, collect_fresh_names_value(&1)))

  defp collect_fresh_names_value(_), do: MapSet.new()

  # Marker-only rewrite (computed path): a `<fresh N>` MARKER becomes a variable of
  # its gensym (a template-introduced binder). Plain variables are left untouched —
  # in the generated-AST path they are reflected use-site data, never template
  # binders. Everything else recurses (children AND meta, mirroring subst_holes).
  defp apply_freshening({:fresh_name, meta, name}, rename),
    do: {:variable, meta, Map.get(rename, name, name)}

  # A quoted syntax value is data, not part of the generated program being
  # hygienized. Keep its inner representation available to the next macro
  # stage unchanged, matching MacroExpand's quote boundary.
  defp apply_freshening({:quoted_syntax, _meta, _children} = quoted, _rename), do: quoted

  defp apply_freshening({:variable, _meta, _name} = v, _rename), do: v

  defp apply_freshening({t, meta, ch}, rename) when is_list(ch),
    do: {t, apply_freshening_meta(meta, rename), Enum.map(ch, &apply_freshening(&1, rename))}

  defp apply_freshening(other, _rename), do: other

  defp apply_freshening_meta(meta, rename) when is_list(meta) do
    Enum.map(meta, fn
      {k, v} -> {k, apply_freshening_value(v, rename)}
      other -> other
    end)
  end

  defp apply_freshening_meta(meta, _rename), do: meta

  defp apply_freshening_value(v, rename) when is_tuple(v), do: apply_freshening(v, rename)

  defp apply_freshening_value(v, rename) when is_list(v),
    do: Enum.map(v, &apply_freshening_value(&1, rename))

  defp apply_freshening_value(v, _rename), do: v

  # ---------------------------------------------------------------------------
  # SP5.3 scope-aware auto-hygiene walk (template path).
  #
  # `scoped_freshen(node, rename, holes, used, state) -> {node, state}`.
  # `rename` maps a template binder name to its per-expansion gensym for the
  # CURRENT scope; a binding form extends it over exactly the sub-region it
  # governs, so shadowing re-mints and references resolve to the innermost
  # binder. `holes` are use-site hole names (never renamed — subst_holes fills
  # them afterwards). `used` are use-site identifiers a gensym must avoid
  # (mint_gensym collision-avoidance; see the `g$0` spoof test). `state` threads
  # the global fresh_counter so every mint is unique within a build.
  # ---------------------------------------------------------------------------

  # Reference: a hole is left for substitution; a bound name resolves to its
  # gensym; anything else (a free var, or a constructor) is left verbatim.
  defp scoped_freshen({:variable, meta, name} = v, rename, holes, _used, state) do
    cond do
      MapSet.member?(holes, name) -> {v, state}
      Map.has_key?(rename, name) -> {{:variable, meta, Map.fetch!(rename, name)}, state}
      true -> {v, state}
    end
  end

  # Stray markers outside a recognized binder position (rare): a `<fresh>` resolves
  # to its in-scope gensym (or its literal name if unbound); a `<capture>` lowers to
  # a plain caller-scope variable the walk never renames.
  defp scoped_freshen({:fresh_name, meta, name}, rename, _holes, _used, state),
    do: {{:variable, meta, Map.get(rename, name, name)}, state}

  defp scoped_freshen({:capture_name, meta, name}, _rename, _holes, _used, state),
    do: {{:variable, meta, name}, state}

  # Quoted syntax is a data boundary — leave it whole (mirrors apply_freshening).
  defp scoped_freshen({:quoted_syntax, _meta, _children} = quoted, _rename, _holes, _used, state),
    do: {quoted, state}

  # Uniform block frame (`let`, incl. constructor-pattern destructuring). Walk the
  # children left-to-right; each `{:assignment}` child binds its LHS-leaf binders
  # over the FOLLOWING children only (its RHS is evaluated in the OUTER scope — the
  # RHS is a reference/hole, never bound by this assignment). A later assignment of
  # the same name re-mints, shadowing the earlier binder over the remaining
  # siblings. A lone assignment (bare `becomes let x = e`) has no following sibling
  # — a no-op.
  defp scoped_freshen({:block, meta, children}, rename, holes, used, state) do
    {rev, _rename, state} =
      Enum.reduce(children, {[], rename, state}, fn
        {:assignment, ameta, [lhs, rhs]}, {acc, r, s} ->
          {new_rhs, s} = scoped_freshen(rhs, r, holes, used, s)
          {new_lhs, r2, s} = bind_pattern(lhs, r, holes, used, s)
          {[{:assignment, ameta, [new_lhs, new_rhs]} | acc], r2, s}

        child, {acc, r, s} ->
          {new_child, s} = scoped_freshen(child, r, holes, used, s)
          {[new_child | acc], r, s}
      end)

    {{:block, meta, Enum.reverse(rev)}, state}
  end

  # Match arm: the pattern binders scope BOTH the arm body (children) AND the
  # `guard:` term in meta. The scrutinee is a sibling of the enclosing
  # `pattern_match` node, walked in the outer scope — not here.
  defp scoped_freshen({:match_arm, meta, children}, rename, holes, used, state) do
    {new_pattern, arm_rename, state} = bind_pattern(Keyword.get(meta, :pattern), rename, holes, used, state)
    {new_children, state} = scoped_freshen_list(children, arm_rename, holes, used, state)
    meta = Keyword.put(meta, :pattern, new_pattern)

    {meta, state} =
      case Keyword.fetch(meta, :guard) do
        {:ok, guard} ->
          {new_guard, state} = scoped_freshen(guard, arm_rename, holes, used, state)
          {Keyword.put(meta, :guard, new_guard), state}

        :error ->
          {meta, state}
      end

    {{:match_arm, meta, new_children}, state}
  end

  # Expression-position lambda: params bind the body only.
  defp scoped_freshen({:lambda, meta, children}, rename, holes, used, state) do
    {new_params, lam_rename, state} = bind_params(Keyword.get(meta, :params, []), rename, holes, used, state)
    {new_children, state} = scoped_freshen_list(children, lam_rename, holes, used, state)
    {{:lambda, Keyword.put(meta, :params, new_params), new_children}, state}
  end

  # Single-clause named fn-def — matched STRICTLY on the single-child `[body]`
  # shape. A multi-clause fn-def is `{:function_def, meta, []}` (empty children,
  # `clauses:`/`params:` in meta); it falls through to the generic clause, which
  # never renames its signature (params are bare-string tuple leaves the generic
  # meta walk leaves untouched). Params bind the body PLUS the `guards:`,
  # `return_type:`, `constraints:` (the `where` clause) meta terms and each param's
  # own `type:`/`default:` — all of which may reference the params.
  defp scoped_freshen({:function_def, meta, [body]}, rename, holes, used, state) do
    {new_params, fn_rename, state} = bind_params(Keyword.get(meta, :params, []), rename, holes, used, state)
    {new_params, state} = rewrite_param_annotations(new_params, fn_rename, holes, used, state)
    {new_body, state} = scoped_freshen(body, fn_rename, holes, used, state)

    {meta, state} =
      Enum.reduce([:guards, :return_type, :constraints], {Keyword.put(meta, :params, new_params), state}, fn
        key, {m, s} -> scoped_freshen_meta_slot(m, key, fn_rename, holes, used, s)
      end)

    {{:function_def, meta, [new_body]}, state}
  end

  # Comprehension: REVERSE-scope. `[body | gens_and_filters]` — the body is the
  # FIRST child but is scoped by EVERY generator binder. Generators bind
  # left-to-right (a later generator's collection may reference an earlier binder);
  # filters are scoped by the preceding generators. Walk the generators/filters
  # first, accumulating the rename, then walk the earlier-sibling body under the
  # full accumulated scope.
  defp scoped_freshen({:comprehension, meta, [body | rest]}, rename, holes, used, state) do
    {rev, comp_rename, state} =
      Enum.reduce(rest, {[], rename, state}, fn
        {:generator, gmeta, [pattern, collection]}, {acc, r, s} ->
          {new_collection, s} = scoped_freshen(collection, r, holes, used, s)
          {new_pattern, r2, s} = bind_pattern(pattern, r, holes, used, s)
          {[{:generator, gmeta, [new_pattern, new_collection]} | acc], r2, s}

        filter, {acc, r, s} ->
          {new_filter, s} = scoped_freshen(filter, r, holes, used, s)
          {[new_filter | acc], r, s}
      end)

    {new_body, state} = scoped_freshen(body, comp_rename, holes, used, state)
    {{:comprehension, meta, [new_body | Enum.reverse(rev)]}, state}
  end

  # Generic recursion: no new scope introduced. Recurse meta values and children
  # under the same rename. Bare-string/atom meta values (names, flags) and
  # `{:param, _, string}` tuples are left untouched — only a binding-form frame
  # ever renames a param string — so a stray/empty-children fn-def keeps its
  # signature, and maps (never `{tag, meta, list}`) stop the walk (the OTP OUT set).
  defp scoped_freshen({t, meta, children}, rename, holes, used, state) when is_list(children) do
    {new_meta, state} = scoped_freshen_meta(meta, rename, holes, used, state)
    {new_children, state} = scoped_freshen_list(children, rename, holes, used, state)
    {{t, new_meta, new_children}, state}
  end

  defp scoped_freshen(other, _rename, _holes, _used, state), do: {other, state}

  defp scoped_freshen_list(nodes, rename, holes, used, state) when is_list(nodes) do
    Enum.map_reduce(nodes, state, fn node, s -> scoped_freshen(node, rename, holes, used, s) end)
  end

  defp scoped_freshen_meta(meta, rename, holes, used, state) when is_list(meta) do
    Enum.map_reduce(meta, state, fn
      {k, v}, s ->
        {new_v, s} = scoped_freshen_value(v, rename, holes, used, s)
        {{k, new_v}, s}

      other, s ->
        {other, s}
    end)
  end

  defp scoped_freshen_meta(meta, _rename, _holes, _used, state), do: {meta, state}

  defp scoped_freshen_value(v, rename, holes, used, state) when is_tuple(v),
    do: scoped_freshen(v, rename, holes, used, state)

  defp scoped_freshen_value(v, rename, holes, used, state) when is_list(v),
    do: scoped_freshen_list(v, rename, holes, used, state)

  defp scoped_freshen_value(v, _rename, _holes, _used, state), do: {v, state}

  # Rewrite one meta slot (`guards:`/`return_type:`/`constraints:`) with the
  # in-scope rename if present, threading state; a missing slot is a no-op.
  defp scoped_freshen_meta_slot(meta, key, rename, holes, used, state) do
    case Keyword.fetch(meta, key) do
      {:ok, value} ->
        {new_value, state} = scoped_freshen_value(value, rename, holes, used, state)
        {Keyword.put(meta, key, new_value), state}

      :error ->
        {meta, state}
    end
  end

  # Bind a pattern: mint a gensym for each binder LEAF and rewrite it, returning
  # the rewritten pattern, the extended rename, and threaded state. Binder leaves
  # are lowercase-initial `{:variable}` names (an uppercase name is a nullary
  # constructor — Idris/Cure convention, elaborator.ex:4519 — left untouched) that
  # are NOT holes, plus explicit `<fresh>` markers (always minted). A `<capture>`
  # marker lowers to a plain caller-scope variable and binds nothing. Non-binder
  # structure (a constructor's argument list) is recursed; `name:`-in-meta
  # constructors are not leaves so are never minted.
  defp bind_pattern({:variable, meta, name} = v, rename, holes, used, state) do
    if binder_name?(name) and not MapSet.member?(holes, name) do
      {gensym, state} = mint_gensym(name, state, used)
      {{:variable, meta, gensym}, Map.put(rename, name, gensym), state}
    else
      {v, rename, state}
    end
  end

  defp bind_pattern({:fresh_name, meta, name}, rename, _holes, used, state) do
    {gensym, state} = mint_gensym(name, state, used)
    {{:variable, meta, gensym}, Map.put(rename, name, gensym), state}
  end

  defp bind_pattern({:capture_name, meta, name}, rename, _holes, _used, state),
    do: {{:variable, meta, name}, rename, state}

  defp bind_pattern({t, meta, children}, rename, holes, used, state) when is_list(children) do
    {new_children, rename, state} = bind_pattern_list(children, rename, holes, used, state)
    {{t, meta, new_children}, rename, state}
  end

  defp bind_pattern(other, rename, _holes, _used, state), do: {other, rename, state}

  defp bind_pattern_list(nodes, rename, holes, used, state) when is_list(nodes) do
    {rev, rename, state} =
      Enum.reduce(nodes, {[], rename, state}, fn node, {acc, r, s} ->
        {new_node, r2, s} = bind_pattern(node, r, holes, used, s)
        {[new_node | acc], r2, s}
      end)

    {Enum.reverse(rev), rename, state}
  end

  # Bind lambda / fn-def params: each `{:param, meta, name}` string-child is a
  # binder (params are always binders — no constructor ambiguity). Mint, rewrite
  # the name, extend the rename. Param annotations (`type:`/`default:`) are
  # rewritten separately once the full param scope is known (see
  # rewrite_param_annotations) so a dependent annotation referencing a sibling
  # param resolves correctly.
  defp bind_params(params, rename, _holes, used, state) when is_list(params) do
    {rev, rename, state} =
      Enum.reduce(params, {[], rename, state}, fn
        {:param, pmeta, name}, {acc, r, s} when is_binary(name) ->
          {gensym, s} = mint_gensym(name, s, used)
          {[{:param, pmeta, gensym} | acc], Map.put(r, name, gensym), s}

        other, {acc, r, s} ->
          {[other | acc], r, s}
      end)

    {Enum.reverse(rev), rename, state}
  end

  defp bind_params(params, rename, _holes, _used, state), do: {params, rename, state}

  defp rewrite_param_annotations(params, rename, holes, used, state) when is_list(params) do
    Enum.map_reduce(params, state, fn
      {:param, pmeta, name}, s ->
        {new_pmeta, s} = scoped_freshen_meta(pmeta, rename, holes, used, s)
        {{:param, new_pmeta, name}, s}

      other, s ->
        {other, s}
    end)
  end

  defp rewrite_param_annotations(params, _rename, _holes, _used, state), do: {params, state}

  # A lowercase-initial (or `_`-initial) name is a term binder; an uppercase name
  # is a constructor (elaborator.ex:4519). Empty names never bind.
  defp binder_name?(name) when is_binary(name), do: name =~ ~r/^[a-z_]/
  defp binder_name?(_), do: false

  defp subst_holes({:variable, _meta, name} = v, bindings, _state) do
    case Map.fetch(bindings, name) do
      {:ok, args} when is_list(args) -> {:list, [generated_by: :macro_repeat], args}
      {:ok, {:raw_tokens, _raw_meta, _tokens} = raw} -> raw
      {:ok, arg} -> arg
      :error -> v
    end
  end

  defp subst_holes({:lift_module, meta, children}, bindings, state) when is_list(meta) do
    case Keyword.get(meta, :module) do
      {:macro_hole, module_hole} ->
        with {:ok, module_ast} <- Map.fetch(bindings, module_hole),
             module_name when is_binary(module_name) <- module_name_from_ast(module_ast) do
          meta = subst_lift_module_meta(meta, bindings, state, {:macro_hole, module_hole}, module_hole, module_name)
          {:lift_module, meta, Enum.map(children, &subst_holes(&1, bindings, state))}
        else
          _ ->
            {:lift_module, subst_holes_meta(meta, bindings, state),
             Enum.map(children, &subst_holes(&1, bindings, state))}
        end

      {:macro_path_hole, prefix, module_hole} ->
        with {:ok, module_ast} <- Map.fetch(bindings, module_hole),
             captured_name when is_binary(captured_name) <- module_name_from_ast(module_ast),
             module_name <- qualify_module_name(prefix, captured_name) do
          meta =
            subst_lift_module_meta(
              meta,
              bindings,
              state,
              {:macro_path_hole, prefix, module_hole},
              module_hole,
              module_name
            )

          {:lift_module, meta, Enum.map(children, &subst_holes(&1, bindings, state))}
        else
          _ ->
            {:lift_module, subst_holes_meta(meta, bindings, state),
             Enum.map(children, &subst_holes(&1, bindings, state))}
        end

      _ ->
        {:lift_module, subst_holes_meta(meta, bindings, state), Enum.map(children, &subst_holes(&1, bindings, state))}
    end
  end

  defp subst_holes({t, meta, children}, bindings, state) when is_list(children) do
    {t, subst_holes_meta(meta, bindings, state), Enum.map(children, &subst_holes(&1, bindings, state))}
  end

  defp subst_holes(other, _bindings, _state), do: other

  defp parse_raw_hole(tokens, parser_state, context \\ nil) do
    eof = %Token{type: :eof, value: nil, line: 0, col: 0}
    context = context || parser_state.expansion_context

    state =
      put_tokens(
        %__MODULE__{
          file: parser_state.file,
          emit_events: false,
          edition: parser_state.edition,
          builtin_macros: parser_state.builtin_macros,
          builtin_computed_macros: parser_state.builtin_computed_macros,
          active_macros: parser_state.active_macros,
          computed_macros: parser_state.computed_macros,
          literal_macros: parser_state.literal_macros,
          expansion_context: context
        },
        tokens ++ [eof]
      )

    {exprs, state} = parse_program(state)

    case state.errors do
      [] -> {:raw_splice, exprs}
      errors -> {:macro_error, [reason: {:raw_hole_parse_error, Enum.reverse(errors)}], []}
    end
  end

  # Not every child AST lives in a node's `children` list: `match_arm` stashes
  # its `pattern`/`guard` in the node's `meta` keyword list instead. A hole
  # referenced from one of those would otherwise survive expansion unbound.
  # Walk meta's values too, substituting into anything AST-shaped and leaving
  # plain data (lines/cols/names/flags) untouched.
  defp subst_holes_meta(meta, bindings, state) when is_list(meta) do
    Enum.map(meta, fn
      {k, v} -> {k, subst_holes_meta_value(v, bindings, state)}
      other -> other
    end)
  end

  defp subst_holes_meta(meta, _bindings, _state), do: meta

  defp subst_lift_module_meta(meta, bindings, state, module_marker, module_hole, module_name) do
    Enum.map(meta, fn
      {:module, ^module_marker} ->
        {:module, module_name}

      {:declarations, declarations} ->
        {:declarations, subst_lift_module_value(declarations, bindings, state, module_hole, module_name)}

      {:callbacks, callbacks} ->
        {:callbacks, subst_lift_module_value(callbacks, bindings, state, module_hole, module_name)}

      {key, value} ->
        {key, subst_holes_meta_value(value, bindings, state)}

      other ->
        other
    end)
  end

  defp subst_lift_module_value({:variable, _meta, name}, _bindings, _state, module_hole, module_name)
       when name == module_hole do
    {:literal, [subtype: :symbol], String.to_atom(module_name)}
  end

  defp subst_lift_module_value({:raw_tokens, raw_meta, tokens}, _bindings, state, _module_hole, _module_name)
       when is_list(raw_meta) and is_list(tokens) do
    if Keyword.get(raw_meta, :delayed, false),
      do: {:delayed_raw_tokens, raw_meta, tokens},
      else: parse_raw_hole(tokens, state)
  end

  defp subst_lift_module_value({:delayed_raw_tokens, raw_meta, tokens}, _bindings, _state, _module_hole, _module_name),
    do: {:delayed_raw_tokens, raw_meta, tokens}

  defp subst_lift_module_value({type, meta, children}, bindings, state, module_hole, module_name)
       when is_list(children) do
    {type, subst_lift_module_value_meta(meta, bindings, state, module_hole, module_name),
     Enum.flat_map(children, fn child ->
       case subst_lift_module_value(child, bindings, state, module_hole, module_name) do
         {:raw_splice, nodes} -> nodes
         expanded -> [expanded]
       end
     end)}
  end

  defp subst_lift_module_value(value, bindings, state, module_hole, module_name) when is_list(value) do
    Enum.flat_map(value, fn item ->
      case subst_lift_module_value(item, bindings, state, module_hole, module_name) do
        {:raw_splice, nodes} -> nodes
        expanded -> [expanded]
      end
    end)
  end

  defp subst_lift_module_value(%Cure.MetaAST.SourceInfo{} = value, _bindings, _state, _module_hole, _module_name),
    do: value

  defp subst_lift_module_value(%Cure.Diagnostic.Span{} = value, _bindings, _state, _module_hole, _module_name),
    do: value

  defp subst_lift_module_value(value, bindings, state, module_hole, module_name) when is_map(value) do
    value =
      Map.new(value, fn {key, item} ->
        {key, subst_lift_module_value(item, bindings, state, module_hole, module_name)}
      end)

    case Map.get(value, :body) do
      body when not is_nil(body) ->
        context = Map.get(value, :callback_context)
        Map.put(value, :body, resolve_delayed_raw(body, state, context))

      _ ->
        value
    end
  end

  defp subst_lift_module_value(value, bindings, state, _module_hole, _module_name),
    do: subst_holes_meta_value(value, bindings, state)

  defp parse_delayed_callback_body(tokens, state, context) do
    case parse_raw_hole(tokens, state, context) do
      {:raw_splice, [body]} ->
        body

      {:raw_splice, []} ->
        {:macro_error, [reason: :delayed_callback_requires_one_expression], []}

      {:raw_splice, _body} ->
        {:macro_error, [reason: :delayed_callback_requires_one_expression], []}

      error ->
        error
    end
  end

  # Delayed slots can occur below ordinary expression nodes (for example, a
  # callback body that guards a phase with `match`). Resolve them only after
  # the lifted callback has introduced its lexical context, then let the
  # normal parser/elaborator validate the resulting expression.
  defp resolve_delayed_raw({:delayed_raw_tokens, _raw_meta, tokens}, state, context)
       when is_list(tokens),
       do: parse_delayed_callback_body(tokens, state, context)

  defp resolve_delayed_raw({tag, meta, children}, state, context) when is_list(children) do
    {tag, meta, Enum.map(children, &resolve_delayed_raw(&1, state, context))}
  end

  defp resolve_delayed_raw(list, state, context) when is_list(list),
    do: Enum.map(list, &resolve_delayed_raw(&1, state, context))

  defp resolve_delayed_raw(%Cure.MetaAST.SourceInfo{} = value, _state, _context), do: value

  defp resolve_delayed_raw(map, state, context) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, resolve_delayed_raw(value, state, context)} end)

  defp resolve_delayed_raw(value, _state, _context), do: value

  defp subst_lift_module_value_meta(meta, bindings, state, module_hole, module_name) when is_list(meta) do
    Enum.map(meta, fn
      {key, value} -> {key, subst_lift_module_value(value, bindings, state, module_hole, module_name)}
      other -> other
    end)
  end

  defp subst_lift_module_value_meta(meta, _bindings, _state, _module_hole, _module_name), do: meta

  defp subst_holes_meta_value({:macro_hole, name}, bindings, _state) do
    case Map.fetch(bindings, name) do
      {:ok, value} -> module_name_from_ast(value)
      :error -> {:macro_hole, name}
    end
  end

  defp subst_holes_meta_value({:variable, _meta, name} = variable, bindings, state) do
    case Map.fetch(bindings, name) do
      {:ok, {:raw_tokens, raw_meta, tokens}} when is_list(raw_meta) and is_list(tokens) ->
        if Keyword.get(raw_meta, :delayed, false),
          do: {:delayed_raw_tokens, raw_meta, tokens},
          else: parse_raw_hole(tokens, state)

      {:ok, {:declarations_block, _block_meta, stmts}} when is_list(stmts) ->
        # A `Declarations until dedent` body binds a pre-parsed block. Splice
        # its statements flat into the enclosing declarations — the same
        # `{:raw_splice, _}` shape the raw-hole path yields — so body members
        # (`fn`/`type`/…) become real module declarations rather than one
        # opaque node the emitter drops. An empty body splices nothing.
        {:raw_splice, stmts}

      {:ok, _value} ->
        subst_holes(variable, bindings, state)

      :error ->
        variable
    end
  end

  defp subst_holes_meta_value({:raw_tokens, _raw_meta, tokens}, _bindings, state),
    do: parse_raw_hole(tokens, state)

  defp subst_holes_meta_value({:delayed_raw_tokens, raw_meta, tokens}, _bindings, _state),
    do: {:delayed_raw_tokens, raw_meta, tokens}

  defp subst_holes_meta_value(v, bindings, state) when is_tuple(v),
    do: subst_holes(v, bindings, state)

  defp subst_holes_meta_value(v, bindings, state) when is_list(v) do
    Enum.flat_map(v, fn item ->
      case subst_holes_meta_value(item, bindings, state) do
        {:raw_splice, nodes} -> nodes
        expanded -> [expanded]
      end
    end)
  end

  defp subst_holes_meta_value(v, _bindings, _state), do: v

  defp put_expansion_context(meta, nil), do: meta
  defp put_expansion_context(meta, context), do: Keyword.put(meta, :expansion_context, context)

  defp module_name_from_ast({:variable, _meta, name}), do: name
  defp module_name_from_ast({:literal, _meta, name}) when is_binary(name), do: name
  defp module_name_from_ast({:literal, _meta, name}) when is_atom(name), do: Atom.to_string(name)

  defp module_name_from_ast({:attribute_access, meta, [base]}) when is_list(meta) do
    case {module_name_from_ast(base), Keyword.get(meta, :attribute)} do
      {base, attr} when is_binary(base) and is_binary(attr) -> base <> "." <> attr
      _ -> nil
    end
  end

  defp module_name_from_ast(other), do: other

  # `mod Demo` compiles to `Cure.Demo` without the author writing the prefix. The
  # lifted-module macros (`fsm`, `actor`, `sup`, `app`, `behavior`) capture every
  # module they name or reference through a `ModuleName` hole, so they qualify by
  # the same rule instead of making the emitter's prefix part of the surface
  # syntax.
  #
  # Two spellings, so a lifted module can be both scoped and reachable:
  #
  #   * a **bare** name is relative to the enclosing module -- `actor Act`
  #     inside `mod Demo` is `Cure.Demo.Act`, so a sibling module may declare
  #     its own `Act` without colliding. The top level belongs to the implicit
  #     `Main` module, so top-level `actor Act` is `Cure.Main.Act`; lifting never
  #     escapes its lexical owner merely because that owner was implicit.
  #   * a **dotted** name is absolute -- `worker Demo.Act` names `Cure.Demo.Act`
  #     from anywhere, which is how one module reaches another's children.
  #
  # A name that already says `Cure.` passes through unchanged; an `Elixir.`-prefixed
  # or lowercase name is a foreign module and keeps its own name.
  defp qualify_lifted_module_name(name, enclosing) when is_binary(name) do
    cond do
      String.starts_with?(name, "Cure.") -> name
      String.starts_with?(name, "Elixir.") -> name
      name in ["Cure", "Elixir"] -> name
      not Regex.match?(~r/^[A-Z]/, name) -> name
      String.contains?(name, ".") -> "Cure." <> name
      is_nil(enclosing) -> "Cure.Main." <> name
      true -> "Cure." <> enclosing <> "." <> name
    end
  end

  defp join_module_name(nil, name), do: name
  defp join_module_name(outer, name), do: outer <> "." <> name

  defp qualify_module_name(prefix, captured_name) do
    if String.starts_with?(captured_name, "Cure."),
      do: captured_name,
      else: prefix <> "." <> captured_name
  end

  # -- Program (top-level sequence) ------------------------------------------

  defp parse_program(state) do
    state = skip_newlines(state)
    parse_program(state, [])
  end

  defp parse_program(state, acc) do
    case peek(state) do
      %Token{type: :eof} ->
        {Enum.reverse(acc), state}

      # Residue from a nested construct, not a terminator. A macro family body
      # captures its tokens up to -- but not including -- the `dedent` that
      # closes it, because a structural delimiter belongs to the enclosing
      # parser (see the `:raw_hole` clause of `match_segments/4`).
      # `parse_block_body/3` discharges that debt by skipping any dedent deeper
      # than its own indent; the top level is indent 0, so every dedent that
      # reaches here is deeper. Returning instead silently discarded every
      # declaration after the first `fsm`/`actor`/`sup` in a file.
      %Token{type: :dedent, value: value} when is_integer(value) and value > 0 ->
        state
        |> advance()
        |> skip_newlines()
        |> parse_program(acc)

      %Token{type: :dedent} ->
        {Enum.reverse(acc), state}

      %Token{type: :line_comment} ->
        {node, state} = consume_line_comment(state)
        state = skip_newlines(state)
        parse_program(state, [node | acc])

      %Token{type: :doc_comment} ->
        # Collect consecutive doc comments (including blocks separated by
        # blank-line gaps when no statement intervenes), attach to next
        # definition.
        {doc_text, state} = collect_all_doc_comments(state)
        state = skip_newlines(state)
        parse_documented(state, acc, doc_text)

      _ ->
        state = mark_seen_if_stmt(state)
        prev_errors = length(state.errors)
        {expr, state} = parse_expr(state, 0)
        # Recovery: synchronize after a broken top-level statement so subsequent
        # well-formed definitions (fn, mod, rec, etc.) are still parsed.
        state =
          if length(state.errors) > prev_errors,
            do: synchronize_to_statement(state),
            else: state

        state = skip_newlines(state)

        if state.emit_events do
          line =
            case expr do
              {_, meta, _} when is_list(meta) -> Keyword.get(meta, :line, 1)
              _ -> 1
            end

          Events.emit(:parser, :node_parsed, expr, Events.meta(state.file, max(line, 1)))
        end

        parse_program(state, [expr | acc])
    end
  end

  # Parse the statement that a leading `##` block documents.
  #
  # A standalone decorator node — `{:decorator, …}` when it carries arguments,
  # `{:property, …}` when it is argless like `@prelude` — is not a documentable
  # declaration, so the doc passes OVER it and lands on the declaration that
  # follows. Only decorators
  # that attach to what comes next fold into that node (`@extern fn`, `@prelude
  # typealias`, `@group(:g) mod`); the rest — notably `@prelude` above `mod`, and
  # `@group` when another decorator stands between it and `mod` — stay siblings of
  # the container, which is how whole-module prelude membership is discovered
  # (`Cure.Elab.Program.module_prelude_decorated?/1` reads the sibling form).
  # Attaching the doc to that sibling would silently strip the module's
  # documentation, which is exactly `lib/std/core.cure`'s shape: its `##` block
  # sits above `@group(:core)` / `@prelude`.
  defp parse_documented(state, acc, doc_text) do
    case peek(state) do
      %Token{type: type} when type in [:eof, :dedent] ->
        {Enum.reverse(acc), state}

      _ ->
        state = mark_seen_if_stmt(state)
        prev_errors = length(state.errors)
        {expr, state} = parse_expr(state, 0)
        errored? = length(state.errors) > prev_errors

        state = if errored?, do: synchronize_to_statement(state), else: state
        state = skip_newlines(state)

        case expr do
          {tag, _meta, _payload} when tag in [:decorator, :property] and not errored? ->
            parse_documented(state, [expr | acc], doc_text)

          _ ->
            parse_program(state, [attach_doc(expr, doc_text) | acc])
        end
    end
  end

  # -- Core Pratt Loop -------------------------------------------------------

  # Effective fixity table: the session table when seeded, else the memoized
  # built-in table (sub-parsers that build `%__MODULE__{}` directly leave the
  # field `nil`).
  defp fixity_table(%__MODULE__{fixity_table: nil}), do: session_builtin_fixity_table()
  defp fixity_table(%__MODULE__{fixity_table: table}), do: table

  # `BuiltinFixity.table/0` is a compile-time constant, so consulting it here can
  # never recurse back into parsing. The `:cure_building_fixity_table` flag is a
  # supported seam for parsing an operator-defining source against an EMPTY table
  # — `operators.cure` is all inert declarations, so an empty table parses it
  # faithfully. The compile-time bake seeds `Parser.harvest/4` with an explicit
  # empty base directly (never this flag); the flag path is exercised by
  # `Cure.Std.OperatorBootstrapTest` and left as a defensive escape hatch.
  # `BuiltinFixity` lives in the compiler layer precisely so the table is
  # reachable here even while `Preload` bakes its stdlib deps at compile time.
  defp session_builtin_fixity_table do
    if Process.get(:cure_building_fixity_table) do
      FixityTable.new()
    else
      BuiltinFixity.table()
    end
  end

  # The lexeme string a token binds under in the fixity table, or `nil` for a
  # non-operator token.
  defp lexeme_of(%Token{type: :operator, value: v}) when is_binary(v), do: v
  defp lexeme_of(%Token{type: type}), do: Map.get(@token_lexemes, type)

  defp infix_token?(table, token),
    do: FixityTable.infix_bp(table, lexeme_of(token)) != :not_infix

  # Step over the `:indent` opening an infix continuation, recording its level
  # so `close_continuations/1` can drop the matching `:dedent`.
  #
  # Operatorhood is declaration-driven while layout is lexical, so the two can
  # only be reconciled where the fixity table AND the parse position are both
  # known — that is, here, in operand position. Deciding it earlier over the
  # raw token stream cannot tell a trailing comparison from the `>` closing a
  # `<name: Type>` macro binder, and erasing that binder's layout deletes the
  # `:indent` opening the macro body.
  defp open_continuation(%__MODULE__{} = state) do
    case peek(state) do
      %Token{type: :indent, value: level} ->
        %__MODULE__{state | continuation_levels: [level | state.continuation_levels]}
        |> advance()

      _ ->
        state
    end
  end

  # Drop the `:dedent` closing each continuation the operand has now finished,
  # innermost first. The dedent is deleted rather than stepped over because the
  # `:newline` ending the operand's line sits in front of it and has to stay: it
  # still separates this statement from the next, while the dedent — which would
  # close the enclosing block — was never a block boundary to begin with.
  # Layout no continuation opened is left alone.
  defp close_continuations(%__MODULE__{continuation_levels: []} = state), do: state

  defp close_continuations(%__MODULE__{continuation_levels: [level | rest]} = state) do
    case continuation_dedent_index(state, state.pos, level) do
      nil ->
        state

      idx ->
        %__MODULE__{drop_token_at(state, idx) | continuation_levels: rest}
        |> close_continuations()
    end
  end

  # Index of the `:dedent` closing `level`, looking past the newline(s) that end
  # the operand's line; `nil` when the operand has not dedented out yet.
  defp continuation_dedent_index(state, idx, level) do
    case token_at(state, idx) do
      %Token{type: :newline} -> continuation_dedent_index(state, idx + 1, level)
      %Token{type: :dedent, value: ^level} -> idx
      _ -> nil
    end
  end

  defp drop_token_at(%__MODULE__{tokens: tokens, count: count} = state, idx) do
    %__MODULE__{state | tokens: Tuple.delete_at(tokens, idx), count: count - 1}
  end

  # A `min_bp` that stops a bounded sub-parse just above built-in operator
  # `lexeme` — i.e. one past its left binding power in the active fixity table,
  # so the loop stops before `lexeme` and everything looser. This replaces the
  # former Precedence-domain magic constants (`6` = "above `=`", `42` = "above
  # comparison"): the flipped table numbers those groups differently, so the
  # thresholds must be read from the table rather than written as literals.
  # When the session table carries no infix fixity for `lexeme` (an empty
  # sub-parser table), fall back to the built-in table — the single source of
  # truth — which always contains `=`/`<`, so the threshold stays table-relative
  # rather than a stale old-scale constant.
  defp bp_above(state, lexeme) do
    case FixityTable.infix_bp(fixity_table(state), lexeme) do
      {left_bp, _right_bp} -> left_bp + 1
      :not_infix -> builtin_bp_above(lexeme)
    end
  end

  # Fallback threshold read from the built-in fixity table. Raises only if even
  # the built-in table lacks `lexeme` as an infix operator, which would be a
  # genuine bug (every `bp_above` caller passes a built-in infix lexeme).
  defp builtin_bp_above(lexeme) do
    case FixityTable.infix_bp(BuiltinFixity.table(), lexeme) do
      {left_bp, _right_bp} ->
        left_bp + 1

      :not_infix ->
        raise "bp_above: #{inspect(lexeme)} is not a built-in infix operator"
    end
  end

  defp parse_expr(state, min_bp), do: parse_expr(state, min_bp, nil)

  # `ctx_op` is the lexeme of the operator whose scope this expression sits in:
  # the enclosing operator for a right operand, or the previously-bound operator
  # for a same-level chain. It lets `reject_incomparable_chain/5` reject two
  # operators from incomparable precedence groups meeting without parentheses.
  defp parse_expr(state, min_bp, ctx_op) do
    {left, state} = parse_prefix(state)
    parse_infix(state, left, min_bp, ctx_op)
  end

  defp parse_infix(state, left, min_bp, ctx_op) do
    # The operand may have sat on its own line. Retire that continuation's
    # layout here, at the loop that opened it, rather than letting a `:dedent`
    # nobody claims reach `parse_program/2` and end the enclosing block.
    state = close_continuations(state)
    token = peek(state)

    # Any declared infix operator at the start of a continuation line belongs
    # to the expression above it. Operatorhood comes exclusively from the
    # active fixity table; `|>`, `<-|`, and user operators share this path.
    {token, state} =
      case token.type do
        :newline ->
          case continuation_infix?(state) do
            true ->
              state = skip_infix_continuation_layout(state)
              {peek(state), state}

            false ->
              {token, state}
          end

        _ ->
          {token, state}
      end

    cond do
      # Postfix: function call  f(...). Function application is maximal-binding —
      # it attaches regardless of the surrounding `min_bp` (a call binds tighter
      # than every operator, including the dot whose right operand carries the
      # highest binding power in the table). The former `min_bp <= 110` ceiling
      # was a Precedence-domain constant that never fired (its max right BP was
      # 101); dropping it keeps existing behaviour byte-identical while staying
      # correct under the flipped, higher-numbered fixity table.
      token.type == :lparen ->
        {left, state} = parse_call(state, left)
        parse_infix(state, left, min_bp, ctx_op)

      # Postfix: record construction  Name{...}
      token.type == :lbrace and is_pascal_case?(left) ->
        {left, state} = parse_record_construction(state, left)
        parse_infix(state, left, min_bp, ctx_op)

      true ->
        table = fixity_table(state)
        lexeme = lexeme_of(token)

        case FixityTable.infix_bp(table, lexeme) do
          {left_bp, _right_bp} when left_bp < min_bp ->
            {left, state}

          {left_bp, right_bp} ->
            state = reject_incomparable_chain(state, table, ctx_op, lexeme, token)
            state = advance(state)
            {ast, state} = build_infix_op(state, left, token, right_bp, lexeme)
            state = reject_non_assoc_chain(state, table, token, lexeme, left_bp)
            parse_infix(state, ast, min_bp, {lexeme, token.span})

          :not_infix ->
            {left, state}
        end
    end
  end

  # Tokens whose only grammatical role is to join two operands: the two built-in
  # connectives, plus `:operator`, which exists only because something declared
  # it `infix`. A line may open with one of these and still be a continuation,
  # because it cannot be the start of anything else.
  @pure_infix_tokens [:pipe, :melquiades, :operator]

  # A continuation is a line the layout marks as belonging to the one above it,
  # so an `:indent` opens one unconditionally. Failing that — a line at the
  # enclosing block's own level — only a pure connective may continue. Every
  # other operator lexeme doubles as something else (`*` opens a macro
  # production row, `-` negates, `<`/`>` bracket a binder), and for those the
  # fixity table cannot tell a continuation from a sibling statement: `*` in
  # `terminal Red` ⏎ `* --Emergency--> Red` is the multiplication operator, so
  # taking it as a continuation glues the row onto the field line above and
  # leaves its `-->` with nowhere to go. Layout can tell them apart, so let it.
  defp continuation_infix?(state) do
    case peek_ahead(state, 1) do
      %Token{type: :indent} ->
        infix_token?(fixity_table(state), peek_ahead(state, 2))

      %Token{type: type} = candidate when type in @pure_infix_tokens ->
        infix_token?(fixity_table(state), candidate)

      _ ->
        false
    end
  end

  defp skip_infix_continuation_layout(state) do
    state |> advance() |> open_continuation()
  end

  # `a == b == c`, `a..b..c`, `a <-| b <-| c`: the spec's operator table and
  # `Precedence`'s own moduledoc call these non-associative, and `right_bp = left_bp + 1`
  # only stops the operator from swallowing a peer on its own right-hand side. It does
  # nothing to stop the loop above from picking the freshly-built node back up as a new
  # left operand at the original `min_bp` — mechanically the same trick `+` and `*` use to
  # left-associate. So the table's "non-assoc" entries parsed as plain left-associative
  # operators, and `a <-| b <-| c` quietly fanned out into two sends.
  #
  # Reject the chain outright, as Haskell (`infix 4 ==`), Rust, and Agda/Idris all do.
  # The error is recorded rather than raised, so the parser keeps going and reports the
  # rest of the file's problems in the same pass.
  defp reject_non_assoc_chain(state, table, token, lexeme, left_bp) do
    next = peek(state)
    next_lexeme = lexeme_of(next)

    # Every operator sharing a left BP with a non-associative one is in its class.
    chained? =
      FixityTable.non_assoc?(table, lexeme) and
        match?({^left_bp, _}, FixityTable.infix_bp(table, next_lexeme))

    if chained? do
      error =
        {:non_associative,
         %{
           operator: operator_display(token),
           next_operator: operator_display(next),
           operator_span: token.span,
           span: next.span,
           line: next.line,
           column: next.col
         }}

      add_error(state, error)
    else
      state
    end
  end

  # Two operators from INCOMPARABLE precedence groups (neither binds tighter than
  # the other) meeting without parentheses have no defined grouping — reject as
  # `{:ambiguous_precedence, g1, g2}`, mirroring how `reject_non_assoc_chain`
  # rejects an illegal chain. `ctx_op` is the operator whose scope the incoming
  # operator (`lexeme`) is binding within; `nil` (top level, no enclosing
  # operator) is never ambiguous. Comparable groups (the whole built-in lattice
  # is totally ordered) never trip this. The error is recorded, not raised, so
  # the rest of the file is still reported.
  defp reject_incomparable_chain(state, _table, nil, _lexeme, _token), do: state

  defp reject_incomparable_chain(state, table, {ctx_op, ctx_span}, lexeme, token) do
    reject_incomparable_chain(state, table, ctx_op, ctx_span, lexeme, token)
  end

  defp reject_incomparable_chain(state, table, ctx_op, lexeme, token) do
    reject_incomparable_chain(state, table, ctx_op, nil, lexeme, token)
  end

  defp reject_incomparable_chain(state, table, ctx_op, ctx_span, lexeme, token) do
    if FixityTable.incomparable?(table, ctx_op, lexeme) do
      add_error(
        state,
        {:ambiguous_precedence,
         %{
           left_group: FixityTable.group_of(table, ctx_op),
           right_group: FixityTable.group_of(table, lexeme),
           operator: operator_display(token),
           operator_span: ctx_span,
           span: token.span,
           line: token.line,
           column: token.col
         }}
      )
    else
      state
    end
  end

  # The operator atom to show in a parse error. Built-in tokens keep their exact
  # historical symbol (`:<`, `:==`, …) so error messages stay byte-identical; a
  # generic user operator shows its lexeme.
  defp operator_display(%Token{type: :operator, value: v}) when is_binary(v), do: String.to_atom(v)
  defp operator_display(%Token{type: type}), do: Precedence.operator_symbol(type)

  # -- Prefix Parsing --------------------------------------------------------

  defp parse_prefix(state) do
    token = peek(state)

    case token.type do
      # Literals
      :integer ->
        maybe_literal_macro(advance(state), literal(:integer, token))

      :float ->
        maybe_literal_macro(advance(state), literal(:float, token))

      :string ->
        {literal(:string, token), advance(state)}

      :bool ->
        {literal(:boolean, token), advance(state)}

      nil ->
        {literal(:null, token), advance(state)}

      :atom ->
        {literal(:symbol, token), advance(state)}

      :regex ->
        maybe_token_literal_macro(advance(state), token)

      :char ->
        {literal(:char, token), advance(state)}

      # A hole `?name` / `?_` — a deferred term (design spec §6 / M8.5).
      :hole ->
        meta = [name: token.value, line: token.line, col: token.col] |> put_token_source_info(token)
        {{:hole, meta, []}, advance(state)}

      :string_interpolation ->
        parse_string_interpolation(state)

      # Variables / identifiers
      :identifier ->
        case token.value do
          # Computed rules get first refusal when they share a public keyword
          # with a transparent rule. A mismatch falls through to that rule in
          # parse_computed_use/2, preserving existing grammar variants.
          name
          when (is_map_key(state.computed_macros, name) or is_map_key(state.builtin_computed_macros, name)) and
                 name not in @reserved_macro_keywords ->
            if computed_macro_head?(state, name) do
              parse_computed_use(state, name)
            else
              case computed_macro_fallback(state, name) do
                {:ok, ast, fallback_state} ->
                  {ast, fallback_state}

                :none ->
                  {variable(token), advance(state)}
              end
            end

          # Standard-library syntax macros use the same segment matcher as
          # user macros. Their raw body is parsed again by the ordinary parser.
          name when is_map_key(state.builtin_macros, name) ->
            if prelude_macro_head?(state, name) do
              parse_macro_use(state, name, state.builtin_macros)
            else
              {variable(token), advance(state)}
            end

          # A use-site of a locally-defined macro keyword. Checked FIRST so a
          # macro keyword wins, but guarded so non-macro identifiers are
          # untouched. (Reserved soft-keyword names are excluded below.)
          name when is_map_key(state.active_macros, name) and name not in @reserved_macro_keywords ->
            if macro_use_head?(state, name) do
              parse_macro_use(state, name)
            else
              {variable(token), advance(state)}
            end

          "assert_type" ->
            parse_assert_type(state, token)

          "check" ->
            parse_macro_check(state, token)

          "rewrite" ->
            parse_rewrite(state, token)

          "simplify" ->
            parse_simplify(state, token)

          "induction" ->
            if induction_block_ahead?(state), do: parse_induction(state, token), else: {variable(token), advance(state)}

          # `have name [: Type] = value` is a checked local fact only at its
          # distinctive binding-shaped head. Elsewhere `have` remains an
          # ordinary identifier, just like the contextual `proof` vocabulary.
          "have" ->
            if local_fact_ahead?(state) do
              parse_local_binding(state, :have)
            else
              {variable(token), advance(state)}
            end

          # `proof` is contextual: at a declaration-shaped head it introduces
          # a proof container; in every other expression/binder position it is
          # an ordinary identifier. The lexer deliberately does not decide.
          "proof" ->
            case peek_at(state, 1) do
              %Token{type: :identifier, value: "chain"} ->
                if proof_chain_boundary?(state), do: parse_proof_chain(state), else: {variable(token), advance(state)}

              %Token{type: :identifier} ->
                parse_proof_container(state)

              _ ->
                {variable(token), advance(state)}
            end

          # `precedencegroup Name` (Phase 3, contextual): declares a precedence
          # group. It is a declaration only when a group-name identifier follows;
          # every other position keeps `precedencegroup` an ordinary identifier.
          "precedencegroup" ->
            case peek_at(state, 1) do
              %Token{type: :identifier} -> parse_precedencegroup(state)
              _ -> {variable(token), advance(state)}
            end

          # `infix|prefix|postfix <op> : Group` (Phase 3, contextual): assigns an
          # operator lexeme to a precedence group. The declaration is recognised
          # only at the distinctive `<op> :` shape, so `prefix + 1`, `prefix: x`,
          # and a bare `infix` value all stay ordinary identifiers.
          fixity when fixity in ["infix", "prefix", "postfix"] ->
            if fixity_decl_ahead?(state) do
              parse_fixity(state)
            else
              {variable(token), advance(state)}
            end

          # Contextual keyword: `with e <arms>` is a with-abstraction only in
          # expression-prefix position and only when what follows `with` can
          # begin a scrutinee. The container macro's payload-binder `with` is
          # consumed before it reaches here, so those uses (and any bare
          # `with` operand) keep their identifier meaning.
          "with" ->
            if with_scrutinee_ahead?(state) do
              parse_with_abs(state, token)
            else
              {variable(token), advance(state)}
            end

          # Soft keyword: `macro Name …` at statement-prefix position is the
          # macro container. `macro` followed by anything other than an
          # identifier stays a plain variable (non-breaking, like sup/app).
          "macro" ->
            case peek_at(state, 1) do
              %Token{type: :identifier} ->
                parse_macro_def(state)

              _ ->
                {variable(token), advance(state)}
            end

          "lift" ->
            case peek_at(state, 1) do
              %Token{type: :identifier, value: "module"} ->
                parse_lift_module(state, token)

              _ ->
                {variable(token), advance(state)}
            end

          # Soft keyword: `public use M` is an explicit reexport — the only
          # way a provider's exports cross a second module boundary. `public`
          # anywhere else stays an ordinary identifier.
          "public" ->
            case peek_at(state, 1) do
              %Token{type: :keyword, value: :use} ->
                parse_use(advance(state), public?: true)

              _ ->
                {variable(token), advance(state)}
            end

          _ ->
            {variable(token), advance(state)}
        end

      # Unary operators
      :minus ->
        parse_unary(state, :arithmetic)

      :not_op ->
        parse_unary(state, :boolean)

      :bnot_op ->
        parse_unary(state, :bitwise)

      # Grouping
      :lparen ->
        parse_grouped(state)

      # Quasiquote splice hole (SP5.1): `$(e)` / `$(e ...)`. Legal only inside a
      # `quote`; outside one the elaborator rejects the orphan splice node.
      :splice_open ->
        parse_splice(state, token)

      # Collections
      :lbracket ->
        parse_list_or_comprehension(state)

      :tuple_open ->
        parse_tuple(state)

      :map_open ->
        parse_map(state)

      # Binary literal
      :binary_open ->
        parse_binary_literal(state)

      # Control flow
      :keyword ->
        parse_keyword_prefix(state, token)

      # At sign (decorator / attribute)
      :at ->
        parse_at(state)

      # Pin operator for patterns: ^x -- introduced in v0.18.0 as a
      # prefix that references a previously-bound variable rather than
      # rebinding. Compiled via {:pin, meta, [inner]}.
      :caret ->
        parse_pin(state)

      # Forced (dot) pattern: a leading `.` in prefix position introduces a
      # forced-equation pattern (`.x`, `.(S(k))`). The inner term is a value the
      # match must be convertible with rather than a fresh binder. Parsing
      # succeeds in any position by design; using a forced pattern outside a
      # pattern is rejected later, at elaboration. Infix `.` (module paths like
      # `Std.String`) is a different grammar position (handle_infix_op :dot) and
      # never reaches this prefix clause.
      :dot ->
        {inner, state} = parse_forced_inner(advance(state))
        meta = put_forced_pattern_source_info([line: token.line, col: token.col], token, inner)
        {{:forced_pattern, meta, [inner]}, state}

      # Named-implicit dot pattern `{ name = <expr> }` in a constructor-argument
      # position — annotates an erased implicit index by name (Lean/Idris-style),
      # e.g. `vcons({k = .m}, h, r)`. A leading `{ IDENT …` is reserved for this
      # form in prefix position, so claim it even when `=` is missing and report
      # the exact repair. Records use postfix `Name{…}`, maps use `#{…}`, and
      # blocks use indentation, so none of those forms reach this clause.
      :lbrace ->
        case peek_at(state, 1) do
          %Token{type: :identifier} ->
            parse_named_implicit_pat(state, token)

          _ ->
            error = unexpected_token_error(token)
            state = add_error(state, error)
            {error_node(token), advance(state)}
        end

      # Indent starts a block
      :indent ->
        parse_block(state)

      # `<fresh Name>` — a template hygiene marker minting a per-expansion
      # gensym (design §5). `<capture Name>` is the symmetric opt-OUT: it marks
      # a template binder that must NOT be auto-freshened, so it binds into the
      # caller's scope on purpose (SP5.3 §4). Only these exact windows are
      # special; every other leading `<` keeps its previous unexpected-token
      # error. Infix `<` (comparisons) never reaches this prefix clause.
      :lt ->
        case {peek_at(state, 1), peek_at(state, 2), peek_at(state, 3)} do
          {%Token{type: :identifier, value: "fresh"}, %Token{type: :identifier, value: name}, %Token{type: :gt}} ->
            node = {:fresh_name, [line: token.line, col: token.col], name}
            state = state |> advance() |> advance() |> advance() |> advance()
            {node, state}

          {%Token{type: :identifier, value: "capture"}, %Token{type: :identifier, value: name}, %Token{type: :gt}} ->
            node = {:capture_name, [line: token.line, col: token.col], name}
            state = state |> advance() |> advance() |> advance() |> advance()
            {node, state}

          _ ->
            error = unexpected_token_error(token)
            state = add_error(state, error)
            {error_node(token), advance(state)}
        end

      _ ->
        error = unexpected_token_error(token)
        state = add_error(state, error)
        {error_node(token), advance(state)}
    end
  end

  defp unexpected_token_error(%Token{} = token) do
    {:unexpected_token,
     %{
       kind: unexpected_token_kind(token.type),
       observed: token.value || token.type,
       token_type: token.type,
       span: token.span,
       line: token.line,
       column: token.col
     }}
  end

  defp unexpected_token_kind(:lbrace), do: :bare_brace_expression
  defp unexpected_token_kind(type) when type in [:rparen, :rbracket, :rbrace], do: :unmatched_closer
  defp unexpected_token_kind(_type), do: :unexpected_token

  # -- assert_type builtin (v0.19.0) ----------------------------------------
  #
  # `assert_type expr : T` is a compile-time type assertion. The type
  # checker verifies `expr : T`; the codegen strips the wrapper and emits
  # only `expr`, so there is no runtime cost.
  defp parse_assert_type(state, token) do
    # Consume the `assert_type` identifier.
    state = advance(state)
    # Parse the expression being asserted. Stop above assignment so a trailing
    # `:`/`=` stays for us; let binding uses the same trick.
    {expr, state} = parse_expr(state, bp_above(state, "="))
    state = expect_assert_type_colon(state, token, expr)
    {type_ast, state} = parse_type_expr(state)
    ast = {:assert_type, [line: token.line, col: token.col], [expr, type_ast]}
    {ast, state}
  end

  defp expect_assert_type_colon(state, assert_token, expr) do
    case expect_token(state, :colon) do
      {:ok, _colon, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :assert_type_colon_missing,
             expected: :colon,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: assert_token.span,
             previous_span: first_node_source_span(expr),
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # Tier-3 semantic guard: `check predicate else fail Name(args)`. The guard is
  # represented explicitly so the dependent elaborator can turn it into a
  # boolean case whose false branch carries the typed Syntax failure value.
  defp parse_macro_check(state, token) do
    state = advance(state)
    {condition, state} = parse_expr(state, 0)

    {else_token, state} =
      case peek(state) do
        %Token{type: :keyword, value: :else} = else_token ->
          {else_token, advance(state)}

        observed ->
          state =
            add_error(
              state,
              {:macro_check_syntax,
               %{
                 kind: :macro_check_else_missing,
                 expected: :else,
                 observed: observed.value || observed.type,
                 token_type: observed.type,
                 span: zero_width_start(observed.span),
                 observed_span: observed.span,
                 opener_span: token.span,
                 previous_span: ast_source_span(condition),
                 line: observed.line,
                 column: observed.col
               }}
            )

          {nil, state}
      end

    {fail_token, state} =
      case peek(state) do
        %Token{type: :identifier, value: "fail"} = fail_token ->
          {fail_token, advance(state)}

        observed ->
          state =
            add_error(
              state,
              {:macro_check_syntax,
               %{
                 kind: :macro_check_fail_missing,
                 expected: :fail,
                 observed: observed.value || observed.type,
                 token_type: observed.type,
                 span: zero_width_start(observed.span),
                 observed_span: observed.span,
                 opener_span: token.span,
                 previous_span: (else_token && else_token.span) || ast_source_span(condition),
                 line: observed.line,
                 column: observed.col
               }}
            )

          {nil, state}
      end

    failure_start = peek(state)
    {failure_call, state} = parse_expr(state, 0)

    case failure_call do
      {:function_call, failure_meta, args} ->
        name = Keyword.get(failure_meta, :name, "?")
        check_meta = [line: token.line, col: token.col, failure: name]
        failure_meta = [line: token.line, col: token.col, name: name]
        {{:macro_check, check_meta, [condition, {:macro_fail, failure_meta, args}]}, state}

      _ ->
        state =
          add_error(
            state,
            {:macro_check_syntax,
             %{
               kind: :macro_check_failure_constructor_invalid,
               expected: :failure_constructor,
               observed: failure_start.value || failure_start.type,
               token_type: failure_start.type,
               span: ast_source_span(failure_call) || failure_start.span,
               opener_span: token.span,
               previous_span: (fail_token && fail_token.span) || (else_token && else_token.span),
               line: failure_start.line,
               column: failure_start.col
             }}
          )

        {{:macro_check, [line: token.line, col: token.col], [condition, {:macro_fail, [name: "?"], []}]}, state}
    end
  end

  # -- Propositional equality rewrite ---------------------------------------
  #
  # `rewrite proof in body` elaborates to a Core rewrite with an explicit motive
  # synthesized by `Cure.Elab`. `rewrite` remains a soft keyword so existing
  # values named `rewrite` only switch forms when used in expression-prefix
  # position.
  defp parse_rewrite(state, token) do
    state = advance(state)

    case peek(state) do
      %Token{type: :identifier, value: value} when value in ["using", "backwards"] ->
        parse_directed_rewrite(state, token)

      _ ->
        parse_legacy_rewrite(state, token)
    end
  end

  defp parse_legacy_rewrite(state, token) do
    {proof, state} = parse_expr(state, 0)
    # `in` may sit on the next line for a multi-line `rewrite … in …` chain, and the BODY may
    # likewise start on the line after `in`. `rewrite` always requires both, so skipping newlines
    # to find each is unambiguous; `skip_newlines` skips only `:newline` (never `:indent`/`:dedent`),
    # so it cannot cross a branch boundary — a missing `in`/body still stops at the dedent and errors.
    state = skip_newlines(state)
    state = expect_legacy_rewrite_in(state, token, proof)
    state = skip_newlines(state)
    {body, state} = parse_expr(state, 0)
    {{:rewrite_expr, [line: token.line, col: token.col], [proof, body]}, state}
  end

  defp expect_legacy_rewrite_in(state, rewrite_token, proof) do
    case peek(state) do
      %Token{type: :keyword, value: :in} ->
        advance(state)

      observed ->
        add_error(
          state,
          {:proof_command_syntax,
           %{
             kind: :rewrite_in_missing,
             expected: :in,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: rewrite_token.span,
             previous_span: ast_source_span(proof),
             line: observed.line,
             column: observed.col
           }}
        )
    end
  end

  defp parse_directed_rewrite(state, rewrite_token) do
    {direction, direction_span, state} =
      case peek(state) do
        %Token{type: :identifier, value: "backwards", span: span} -> {:backwards, span, advance(state)}
        _ -> {:forward, rewrite_token.span, state}
      end

    state =
      case peek(state) do
        %Token{type: :identifier, value: "using"} ->
          advance(state)

        observed ->
          add_error(
            state,
            {:proof_command_syntax,
             %{
               kind: :rewrite_using_missing,
               expected: :using,
               observed: observed.value || observed.type,
               token_type: observed.type,
               span: zero_width_start(observed.span),
               observed_span: observed.span,
               opener_span: rewrite_token.span,
               previous_span: direction_span,
               line: observed.line,
               column: observed.col
             }}
          )
      end

    {proof, state} = parse_expr(state, 0)

    {target, state, last_span} =
      case peek(state) do
        %Token{type: :identifier, value: "at"} = selector ->
          state = advance(state)

          case peek(state) do
            %Token{type: :integer, value: occurrence, span: span} when occurrence > 0 ->
              {{:at, occurrence}, advance(state), span}

            observed ->
              state =
                add_error(
                  state,
                  {:proof_command_syntax,
                   %{
                     kind: :rewrite_occurrence_invalid,
                     expected: :positive_integer,
                     observed: observed.value || observed.type,
                     token_type: observed.type,
                     span: observed.span,
                     opener_span: rewrite_token.span,
                     previous_span: selector.span,
                     line: observed.line,
                     column: observed.col
                   }}
                )

              {{:at, 0}, state, observed.span}
          end

        %Token{type: :keyword, value: :in} = selector ->
          state = advance(state)

          case peek(state) do
            %Token{type: :identifier, value: name, span: span} ->
              {{:in, name}, advance(state), span}

            observed ->
              state =
                add_error(
                  state,
                  {:proof_command_syntax,
                   %{
                     kind: :rewrite_hypothesis_name_invalid,
                     expected: :identifier,
                     observed: observed.value || observed.type,
                     token_type: observed.type,
                     span: observed.span,
                     opener_span: rewrite_token.span,
                     previous_span: selector.span,
                     line: observed.line,
                     column: observed.col
                   }}
                )

              {{:in, "?"}, state, observed.span}
          end

        _ ->
          {:goal, state, ast_source_span(proof)}
      end

    meta = [line: rewrite_token.line, col: rewrite_token.col, direction: direction, target: target]

    meta =
      with %Cure.Diagnostic.Span{} = first <- rewrite_token.span,
           %Cure.Diagnostic.Span{} = last <- last_span,
           {:ok, whole} <- Range.through(first, last) do
        Keyword.put(meta, :source_info, %SourceInfo{
          whole: whole,
          operator: rewrite_token.span,
          body: ast_source_span(proof),
          operands: [ast_source_span(proof)],
          fields: %{
            rewrite_keyword: rewrite_token.span,
            direction: direction_span
          }
        })
      else
        _ -> meta
      end

    {{:rewrite_command, meta, [proof]}, state}
  end

  # -- Equational proof chains ----------------------------------------------

  defp parse_simplify(state, token) do
    state = advance(state)

    case peek(state) do
      %Token{type: :identifier, value: "using"} ->
        state = advance(state)
        mode = if match?(%Token{type: :lbracket}, peek(state)), do: :rules, else: :proof
        {rules, state} = parse_expr(state, 0)
        meta = put_token_source_info([line: token.line, col: token.col], token)
        {{:simplify_command, Keyword.put(meta, :using, mode), [rules]}, state}

      _ ->
        meta = put_token_source_info([line: token.line, col: token.col], token)
        {{:simplify_command, meta, []}, state}
    end
  end

  # `induction` and its `case` introducers are contextual vocabulary. Keeping
  # them as identifiers outside this distinctive block head preserves ordinary
  # functions and binders with those names.
  defp induction_block_ahead?(state), do: induction_block_ahead?(state, 1, false)

  defp induction_block_ahead?(state, offset, saw_subject?) do
    case peek_at(state, offset) do
      %Token{type: :newline} when saw_subject? ->
        match?(%Token{type: :indent}, peek_at(state, offset + 1))

      %Token{type: type} when type in [:eof, :dedent] ->
        false

      _token ->
        induction_block_ahead?(state, offset + 1, true)
    end
  end

  defp parse_induction(state, token) do
    state = advance(state)
    {subject, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {cases, state} = parse_induction_cases(state, [], token)
        state = expect_dedent(state)
        meta = induction_meta(token, subject, cases)
        {{:induction, meta, [subject | cases]}, state}

      observed ->
        state =
          add_error(
            state,
            {:proof_command_syntax,
             %{
               kind: :induction_block_indent_missing,
               expected: :indent,
               observed: observed.value || observed.type,
               token_type: observed.type,
               span: observed.span,
               opener_span: token.span,
               previous_span: ast_source_span(subject),
               line: observed.line,
               column: observed.col
             }}
          )

        {{:induction, put_token_source_info([line: token.line, col: token.col], token), [subject]}, state}
    end
  end

  defp parse_induction_cases(state, acc, induction_token) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :identifier, value: "case"} = case_token ->
        state = advance(state)
        {pattern, state} = parse_expr(state, 0)
        {arrow_token, state} = expect_induction_case_arrow(state, case_token, pattern)
        state = skip_newlines(state)

        {body, terminal_span, impossible?, state} =
          if impossible_body?(state) do
            impossible_token = peek(state)
            {nil, impossible_token.span, true, advance(state)}
          else
            {body, state} = parse_expr_or_block(state)
            {body, ast_source_span(body), false, state}
          end

        meta =
          [line: case_token.line, col: case_token.col]
          |> Keyword.put(:impossible, impossible?)
          |> put_induction_case_source_info(case_token, arrow_token, pattern, terminal_span)

        parse_induction_cases(state, [{:induction_case, meta, [pattern, body]} | acc], induction_token)

      observed ->
        state =
          add_error(
            state,
            {:proof_command_syntax,
             %{
               kind: :induction_case_introducer_missing,
               expected: :case,
               observed: observed.value || observed.type,
               token_type: observed.type,
               span: observed.span,
               opener_span: induction_token.span,
               previous_span: acc |> List.first() |> ast_source_span(),
               line: observed.line,
               column: observed.col
             }}
          )

        {Enum.reverse(acc), advance(state)}
    end
  end

  defp expect_induction_case_arrow(state, case_token, pattern) do
    case expect_token(state, :fat_arrow) do
      {:ok, arrow, next_state} ->
        {arrow, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:branch_arrow_missing,
           %{
             family: :induction_case,
             expected: :fat_arrow,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: case_token.span,
             previous_span: first_node_source_span(pattern),
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp put_induction_case_source_info(meta, case_token, arrow_token, pattern, terminal_span) do
    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(case_token.span, terminal_span) || case_token.span,
      opener: case_token.span,
      operator: arrow_token && arrow_token.span,
      pattern: ast_source_span(pattern),
      body: terminal_span
    })
  end

  defp induction_meta(token, subject, cases) do
    last = List.last(cases)
    last_span = ast_source_span(last) || ast_source_span(subject)

    info = %SourceInfo{
      whole: through_spans(token.span, last_span) || token.span,
      opener: token.span,
      operands: Enum.filter([ast_source_span(subject)], & &1),
      branches: cases |> Enum.map(&ast_source_span/1) |> Enum.filter(& &1)
    }

    Metadata.put_source_info([line: token.line, col: token.col], info)
  end

  defp through_spans(%Cure.Diagnostic.Span{} = first, %Cure.Diagnostic.Span{} = last) do
    case Range.through(first, last) do
      {:ok, whole} -> whole
      _ -> nil
    end
  end

  defp through_spans(_, _), do: nil

  defp proof_chain_boundary?(state) do
    match?(%Token{type: :newline}, peek_at(state, 2))
  end

  defp parse_proof_chain(state) do
    proof_token = peek(state)
    state = state |> advance() |> advance() |> skip_newlines()

    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state) |> skip_newlines()
        {first, state} = parse_expr(state, bp_above(state, "=="))
        state = reject_first_chain_previous(state, first, proof_token)
        state = skip_newlines(state)
        {steps, state} = parse_proof_chain_steps(state, [], true, ast_source_span(first))
        state = expect_dedent(state)
        meta = proof_chain_source_info([line: proof_token.line, col: proof_token.col], proof_token, first, steps)
        {{:proof_chain, meta, [first | steps]}, state}

      token ->
        problem = %ProofChainSyntaxProblem{
          kind: :empty_chain,
          construct: proof_token.span,
          observed: token.type,
          expected: :first_expression
        }

        state = add_error(state, {:proof_chain_syntax, problem})
        {{:proof_chain, [line: proof_token.line, col: proof_token.col], []}, state}
    end
  end

  defp parse_proof_chain_steps(state, acc, first?, previous_span) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :eq} when first? ->
        {step, state} = parse_proof_chain_step(state, :implicit)
        parse_proof_chain_steps(state, [step | acc], false, proof_step_right_span(step))

      %Token{type: :indent} when first? ->
        state = advance(state) |> skip_newlines()
        {step, state} = parse_proof_chain_step(state, :implicit)
        state = state |> skip_newlines() |> expect_dedent() |> skip_newlines()
        parse_proof_chain_steps(state, [step | acc], false, proof_step_right_span(step))

      %Token{type: :identifier, value: "_"} ->
        {step, state} = parse_proof_chain_step(state, :continuation)
        parse_proof_chain_steps(state, [step | acc], false, proof_step_right_span(step))

      _ ->
        if acc == [] do
          token = peek(state)

          problem = %ProofChainSyntaxProblem{
            kind: :missing_relation,
            step: previous_span,
            observed: token.type,
            expected: :equality_step
          }

          state = add_error(state, {:proof_chain_syntax, problem})
          {[], state}
        else
          {Enum.reverse(acc), state}
        end
    end
  end

  defp proof_step_right_span({:proof_step, _meta, [_marker, right, _justification]}), do: ast_source_span(right)

  defp parse_proof_chain_step(state, marker_kind) do
    {marker, relation_token, state} =
      case marker_kind do
        :implicit ->
          token = peek(state)
          {{:proof_chain_previous, [implicit: true, line: token.line, col: token.col], []}, token, state}

        :continuation ->
          token = peek(state)
          marker = {:proof_chain_previous, put_token_source_info([line: token.line, col: token.col], token), []}
          {marker, peek_at(state, 1), advance(state)}
      end

    state =
      case peek(state) do
        %Token{type: :eq} ->
          advance(state)

        token ->
          problem = %ProofChainSyntaxProblem{
            kind: :missing_relation,
            step: token.span,
            observed: token.type,
            expected: :eq,
            insertion: token.span
          }

          add_error(state, {:proof_chain_syntax, problem})
      end

    state = skip_newlines(state)

    {right, state} =
      case peek(state) do
        %Token{type: :identifier, value: "because"} = token ->
          problem = %ProofChainSyntaxProblem{
            kind: :missing_right_side,
            step: token.span,
            observed: :because,
            expected: :expression,
            insertion: token.span
          }

          {{:variable, [line: token.line, col: token.col], "_missing_chain_endpoint"},
           add_error(state, {:proof_chain_syntax, problem})}

        _ ->
          parse_expr(state, bp_above(state, "=="))
      end

    state = skip_newlines(state)

    {nested_because?, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state) |> skip_newlines()}
        _ -> {false, state}
      end

    {because_token, state} =
      case peek(state) do
        %Token{type: :identifier, value: "because"} = token ->
          {token, advance(state)}

        token ->
          problem = %ProofChainSyntaxProblem{
            kind: :missing_because,
            step: ast_source_span(right),
            observed: token.type,
            expected: :because,
            insertion: token.span
          }

          {token, add_error(state, {:proof_chain_syntax, problem})}
      end

    {justification, state} = parse_chain_justification(state, because_token)
    state = if nested_because?, do: state |> skip_newlines() |> expect_dedent(), else: state

    meta =
      [line: relation_token.line, col: relation_token.col]
      |> proof_step_source_info(marker, right, justification, relation_token, because_token)

    {{:proof_step, meta, [marker, right, justification]}, state}
  end

  defp parse_chain_justification(state, because_token) do
    multiline? = match?(%Token{type: :newline}, peek(state))
    state = skip_newlines(state)

    if multiline? and match?(%Token{type: :indent}, peek(state)) do
      indent_token = peek(state)
      state = advance(state)
      {statements, state} = parse_block_body(state, indent_token.value)
      state = expect_dedent(state)

      meta =
        [line: because_token.line, col: because_token.col]
        |> proof_justification_source_info(because_token, statements)

      {{:proof_justification, meta, statements}, state}
    else
      parse_expr(state, 0)
    end
  end

  defp proof_justification_source_info(meta, %Token{span: %Cure.Diagnostic.Span{} = first}, statements) do
    case statements |> List.last() |> ast_source_span() do
      %Cure.Diagnostic.Span{} = last ->
        case Range.through(first, last) do
          {:ok, whole} -> Keyword.put(meta, :source_info, %SourceInfo{whole: whole, body: whole})
          _ -> meta
        end

      _ ->
        meta
    end
  end

  defp proof_justification_source_info(meta, _token, _statements), do: meta

  defp reject_first_chain_previous(state, {:variable, meta, "_"}, proof_token) do
    problem = %ProofChainSyntaxProblem{
      kind: :first_step_previous,
      construct: proof_token.span,
      step: ast_source_span({:variable, meta, "_"}),
      observed: :previous,
      expected: :first_expression
    }

    add_error(state, {:proof_chain_syntax, problem})
  end

  defp reject_first_chain_previous(state, _first, _proof_token), do: state

  defp proof_chain_source_info(meta, %Token{span: first}, first_expr, steps) do
    last = List.last(steps) || first_expr

    case {first, ast_source_span(last)} do
      {%Cure.Diagnostic.Span{} = start, %Cure.Diagnostic.Span{} = finish} ->
        case Range.through(start, finish) do
          {:ok, whole} -> Keyword.put(meta, :source_info, %SourceInfo{whole: whole, body: ast_source_span(first_expr)})
          _ -> meta
        end

      _ ->
        meta
    end
  end

  defp proof_step_source_info(meta, marker, right, justification, relation, because) do
    marker_span = ast_source_span(marker)
    right_span = ast_source_span(right)
    spans = [marker_span, right_span, ast_source_span(justification)] |> Enum.reject(&is_nil/1)

    case spans do
      [] ->
        meta

      _ ->
        with %Token{span: %Cure.Diagnostic.Span{} = rel_span} <- relation,
             %Token{span: %Cure.Diagnostic.Span{} = because_span} <- because,
             {:ok, whole} <- Range.through(marker_span || rel_span, List.last(spans)) do
          Keyword.put(meta, :source_info, %SourceInfo{
            whole: whole,
            operator: rel_span,
            body: ast_source_span(justification),
            operands: Enum.reject([marker_span, right_span], &is_nil/1),
            opener: because_span
          })
        else
          _ -> meta
        end
    end
  end

  # -- Pin Operator (pattern position) ---------------------------------------

  defp parse_pin(state) do
    token = peek(state)
    state = advance(state)
    inner_token = peek(state)

    case inner_token.type do
      :identifier ->
        state = advance(state)
        inner = variable(inner_token)
        ast = {:pin, [line: token.line, col: token.col], [inner]}
        {ast, state}

      _ ->
        # Fallback: parse any prefix expression and wrap it so that
        # `Cure.Compiler.PatternCompiler.compile_pin/3` can unwrap it.
        {inner, state} = parse_prefix(state)
        ast = {:pin, [line: token.line, col: token.col], [inner]}
        {ast, state}
    end
  end

  # -- Forced (dot) pattern inner --------------------------------------------
  #
  # After a leading `.`, read the forced term. `.(expr)` parses a full
  # parenthesised expression (a compound forced pattern like `.(S(k))`); a bare
  # `.x` reads a single primary (identifier / literal) as the forced value.
  defp parse_forced_inner(state) do
    case peek(state).type do
      :lparen -> parse_grouped(state)
      _ -> parse_prefix(state)
    end
  end

  # -- Named-implicit dot pattern --------------------------------------------
  #
  # `{ name = <expr> }` annotates a constructor's erased implicit index `name`
  # with a forced value in a pattern-argument position. Valid only as a
  # constructor-pattern argument; ordinary expression elaboration rejects it
  # (`{:named_implicit_not_in_pattern, …}`). The inner expression is parsed with
  # the full expression grammar, so a leading `.` yields a `{:forced_pattern,…}`.
  defp parse_named_implicit_pat(state, brace_token) do
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = expect_named_implicit_pattern_assign(state, brace_token, name_token, name)
    {inner, state} = parse_expr(state, 0)

    {state, close_token} =
      expect_container_close(state, :rbrace, :named_implicit_pattern, brace_token, [inner], false, %{
        binder: name,
        binder_span: name_token.span,
        previous_span: pattern_value_terminal_span(inner),
        closing_tokens: [:comma, :rparen, :arrow]
      })

    meta =
      [line: brace_token.line, col: brace_token.col, name: name]
      |> put_named_implicit_source_info(brace_token, close_token, name_token, inner)

    {{:named_implicit_pat, meta, [inner]}, state}
  end

  defp put_forced_pattern_source_info(meta, %Token{span: dot}, inner) do
    inner_span = ast_source_span(inner)

    Metadata.put_source_info(meta, %SourceInfo{
      whole: if(inner_span, do: merge_source_spans(dot, inner_span), else: dot),
      opener: dot,
      operator: dot,
      body: inner_span,
      operands: List.wrap(inner_span)
    })
  end

  defp put_named_implicit_source_info(meta, %Token{span: opener}, close_token, %Token{span: name}, inner) do
    body = ast_source_span(inner)
    closer = if match?(%Token{}, close_token), do: close_token.span
    ending = closer || body || name

    Metadata.put_source_info(meta, %SourceInfo{
      whole: merge_source_spans(opener, ending),
      name: name,
      opener: opener,
      closer: closer,
      body: body,
      fields: %{binder: name}
    })
  end

  defp pattern_value_terminal_span({_kind, meta, _children} = node) when is_list(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{body: %Cure.Diagnostic.Span{} = body} -> body
      _ -> ast_source_span(node)
    end
  end

  defp pattern_value_terminal_span(node), do: ast_source_span(node)

  defp expect_named_implicit_pattern_assign(state, brace_token, name_token, name) do
    case expect_token(state, :assign) do
      {:ok, _assign, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :named_implicit_pattern_assign_missing,
             binder: name,
             expected: :assign,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: brace_token.span,
             previous_span: name_token.span,
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # -- Literals --------------------------------------------------------------

  defp literal(subtype, token) do
    meta =
      [subtype: subtype, line: token.line, col: token.col]
      |> then(fn meta ->
        cond do
          subtype == :float and is_binary(token.lexeme) ->
            Keyword.put(meta, :exact_decimal, token.lexeme)

          subtype == :integer and is_binary(token.lexeme) ->
            Keyword.put(meta, :exact_integer, token.lexeme)

          true ->
            meta
        end
      end)

    {:literal, put_token_source_info(meta, token), token.value}
  end

  # Regex syntax is a compile-time literal macro, not a runtime OTP handle.
  # Preserve the source pattern and flags for the staged `Std.Regex.literal/2`
  # expansion entry. It computes an indexed TyRE and must not leave a runtime
  # pattern parser or `:re` dispatch in generated code.
  defp regex_literal_macro(%Token{value: {body, flags}, line: line, col: col} = token) do
    pattern_token = regex_literal_child_token(token, :string, body, "/")
    flags_token = regex_literal_child_token(token, :string, flags, "/" <> body <> "/")

    {
      :function_call,
      [name: "Std.Regex.literal", line: line, col: col],
      [
        literal(:string, pattern_token),
        literal(:string, flags_token)
      ]
    }
  end

  # A source-defined computed `literal regex ...` rule receives the regex token's
  # opaque body and flags as two ordinary string-literal children. The parser
  # knows only the token class; grammar, options, result shape, and expansion all
  # belong to the rule's Cure expander. If no rule is registered, retain the
  # legacy call-shaped node as a recovery form so parsing remains total.
  defp maybe_token_literal_macro(state, %Token{type: type, value: {body, flags}} = token) do
    case Map.get(state.literal_macros, {:token, type}, []) do
      [rule | _] ->
        pattern = literal(:string, regex_literal_child_token(token, :string, body, "/"))
        options = literal(:string, regex_literal_child_token(token, :string, flags, "/" <> body <> "/"))
        input = {:macro_input, [keyword: Atom.to_string(type)], [pattern, options]}

        meta =
          [
            keyword: Atom.to_string(type),
            syntax_fields: ["pattern", "flags"],
            syntax_field_types: %{},
            file: state.file,
            line: token.line,
            col: token.col
          ]
          |> put_expansion_context(state.expansion_context)
          |> then(fn meta ->
            case Map.get(rule, :source_path) do
              nil -> meta
              home -> Keyword.put(meta, :home_source, home)
            end
          end)

        {{:computed_use, meta, [rule.elab, input]}, state}

      [] ->
        {regex_literal_macro(token), state}
    end
  end

  defp regex_literal_child_token(%Token{span: %Span{} = span} = token, type, value, prefix) do
    {start_line, start_column} = advance_source_coordinates(span.start_line, span.start_column, prefix)
    {end_line, end_column} = advance_source_coordinates(start_line, start_column, value)

    child_span = %Span{
      span
      | start_byte: span.start_byte + byte_size(prefix),
        end_byte: span.start_byte + byte_size(prefix) + byte_size(value),
        start_line: start_line,
        start_column: start_column,
        end_line: end_line,
        end_column: end_column
    }

    %Token{token | type: type, value: value, lexeme: value, span: child_span, line: start_line, col: start_column}
  end

  defp regex_literal_child_token(%Token{} = token, type, value, _prefix),
    do: %Token{token | type: type, value: value, lexeme: value}

  defp advance_source_coordinates(line, column, text) do
    case String.split(text, "\n") do
      [single] -> {line, column + String.length(single)}
      lines -> {line + length(lines) - 1, String.length(List.last(lines)) + 1}
    end
  end

  defp variable(token) do
    meta = [scope: :local, line: token.line, col: token.col]
    {:variable, put_token_source_info(meta, token, :name), token.value}
  end

  defp type_variable(token) do
    meta = [scope: :local, line: token.line, col: token.col]
    {:variable, put_token_source_info(meta, token, :name), to_string(token.value)}
  end

  defp put_token_source_info(meta, token, role \\ nil)

  defp put_token_source_info(meta, %Token{span: %Cure.Diagnostic.Span{} = span}, role) do
    info = %SourceInfo{whole: span}
    info = if role == :name, do: %{info | name: span}, else: info
    Keyword.put(meta, :source_info, info)
  end

  defp put_token_source_info(meta, _token, _role), do: meta

  defp extend_source_info_whole(meta, %Token{span: %Cure.Diagnostic.Span{} = closing_span}) do
    case Metadata.source_info(meta) do
      %SourceInfo{whole: %Cure.Diagnostic.Span{} = opening_span} = info ->
        Keyword.put(meta, :source_info, %{info | whole: merge_source_spans(opening_span, closing_span)})

      _ ->
        meta
    end
  end

  defp extend_source_info_whole(meta, _token), do: meta

  defp error_node(token) do
    {:literal, [subtype: :null, line: token.line, col: token.col, error: true], nil}
  end

  # -- String Interpolation --------------------------------------------------

  defp parse_string_interpolation(state) do
    token = peek(state)
    state = advance(state)
    parts = token.value

    parsed_parts =
      Enum.map(parts, fn
        {:string_part, s} ->
          {:literal, [subtype: :string], s}

        {:expr, expr_tokens} ->
          # Append an EOF token so the sub-parser terminates
          sub_tokens = expr_tokens ++ [Token.new(:eof, nil, token.line, token.col)]

          sub_state =
            put_tokens(%__MODULE__{file: state.file, emit_events: false}, sub_tokens)

          {expr, _} = parse_expr(sub_state, 0)
          expr
      end)

    meta = [line: token.line, col: token.col]
    meta = put_interpolation_source_info(meta, token, parts)
    ast = {:string_interpolation, meta, parsed_parts}
    {ast, state}
  end

  defp put_interpolation_source_info(meta, %Token{span: %Cure.Diagnostic.Span{} = whole}, parts) do
    arguments =
      parts
      |> Enum.flat_map(fn
        {:expr, tokens} ->
          case authored_token_span(tokens) do
            %Cure.Diagnostic.Span{} = span -> [span]
            nil -> []
          end

        _text ->
          []
      end)

    Keyword.put(meta, :source_info, %SourceInfo{whole: whole, arguments: arguments})
  end

  defp put_interpolation_source_info(meta, _token, _parts), do: meta

  defp authored_token_span(tokens) when is_list(tokens) do
    authored = Enum.filter(tokens, &match?(%Token{span: %Cure.Diagnostic.Span{}}, &1))

    case {List.first(authored), List.last(authored)} do
      {%Token{} = first, %Token{} = last} ->
        case Range.through(first, last) do
          {:ok, span} -> span
          {:error, _reason} -> nil
        end

      _ ->
        nil
    end
  end

  defp authored_token_span(_tokens), do: nil

  # -- Unary Operators -------------------------------------------------------

  defp parse_unary(state, category) do
    token = peek(state)
    rbp = prefix_rbp(state, token)
    state = advance(state)
    {operand, state} = parse_expr(state, rbp, {lexeme_of(token), token.span})
    op = Precedence.operator_symbol(token.type)
    meta = [category: category, operator: op, line: token.line, col: token.col]
    meta = put_operator_source_info(meta, nil, operand, token)
    ast = {:unary_op, meta, [operand]}
    {fold_signed_numeric_literal(ast), state}
  end

  # A sign immediately applied to numeric syntax is part of that literal's
  # exact descriptor, not a later call to Additive.negate. Non-literal operands
  # remain ordinary overloadable unary operations.
  defp fold_signed_numeric_literal({:unary_op, meta, [{:literal, literal_meta, value}]} = expression)
       when is_number(value) do
    if Keyword.get(meta, :operator) == :- and
         Keyword.get(literal_meta, :subtype) in [:integer, :float] do
      literal_meta =
        case Keyword.get(literal_meta, :subtype) do
          :integer ->
            Keyword.update(
              literal_meta,
              :exact_integer,
              Integer.to_string(-value),
              &("-" <> String.trim_leading(&1, "-"))
            )

          :float ->
            Keyword.update(
              literal_meta,
              :exact_decimal,
              Float.to_string(-value),
              &("-" <> String.trim_leading(&1, "-"))
            )
        end

      {:literal, literal_meta, -value}
    else
      expression
    end
  end

  defp fold_signed_numeric_literal(expression), do: expression

  # Prefix binding power via the fixity table, falling back to the built-in
  # table — the single source of truth — when the session table carries no
  # prefix fixity for the lexeme (e.g. a sub-parser with an empty table). The
  # built-in `Prefix` group is declared `higher_than: Multiplicative`, so a
  # prefix operator binds tighter than every infix group but `.` (Dot), exactly
  # as the retired static rbp (90, below dot's 100) did.
  defp prefix_rbp(state, token) do
    lexeme = lexeme_of(token)

    case FixityTable.prefix_bp(fixity_table(state), lexeme) do
      bp when is_integer(bp) -> bp
      :not_prefix -> FixityTable.prefix_bp(BuiltinFixity.table(), lexeme)
    end
  end

  # -- Grouping ( ... ) ------------------------------------------------------

  defp parse_grouped(state) do
    open = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        # `()` — the unit value (Swift-style): the sole inhabitant of `Unit`. It
        # is NOT an empty tuple; it lowers to the nullary `unit` constructor.
        state = advance(state)
        {{:unit_value, [line: open.line, col: open.col]}, state}

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        {state, _close_token} =
          expect_container_close(state, :rparen, :grouped_expression, open, [expr], false)

        {expr, state}
    end
  end

  # -- Infix Operators -------------------------------------------------------

  defp parse_infix_rhs(state, right_bp, op_lexeme) do
    state = state |> skip_newlines() |> open_continuation()
    parse_expr(state, right_bp, op_lexeme)
  end

  defp take_infix_rhs_token(state) do
    state = state |> skip_newlines() |> open_continuation()
    token = peek(state)
    state = advance(state)
    {token, state}
  end

  # Build the node for one infix operator whose left operand is already parsed. The
  # caller resumes the Pratt loop, so it can see the token that follows.
  defp build_infix_op(state, left, token, right_bp, op_lexeme) do
    case token.type do
      # Pipe desugaring: a |> f  or  a |> f(b, c). A trailing `|>` may sit at the end of a line with its
      # right operand on the next line (`a |> \n f() |> \n g()`); `|>` always demands an operand, so skipping
      # the intervening newline to find it is unambiguous.
      :pipe ->
        {right, state} = parse_infix_rhs(state, right_bp, {op_lexeme, token.span})
        {desugar_pipe(left, right, token), state}

      # Melquiades spellings are now ordinary library-defined operators. Keep
      # their dedicated lexer token (it gives both spellings excellent spans),
      # but lower through the same overloadable `:binary_op` path as every
      # user-defined operator. `Std.Otp` supplies the meanings; without that
      # import the normal "operator has no definition" diagnostic applies.
      :melquiades ->
        {right, state} = parse_infix_rhs(state, right_bp, {op_lexeme, token.span})
        op = String.to_atom(token.value)
        meta = [category: :overloaded, operator: op, line: token.line, col: token.col]
        meta = put_operator_source_info(meta, left, right, token)
        {{:binary_op, meta, [left, right]}, state}

      # Dot access: obj.field -> {:attribute_access, ...}
      :dot ->
        {field_token, state} = take_infix_rhs_token(state)
        field_name = to_string(field_token.value)
        meta = [attribute: field_name, line: token.line, col: token.col]

        meta =
          with %Cure.Diagnostic.Span{} = first <- ast_source_span(left),
               %Cure.Diagnostic.Span{} = last <- field_token.span,
               {:ok, whole} <- Range.through(first, last) do
            Keyword.put(meta, :source_info, %SourceInfo{whole: whole, name: last, operator: token.span})
          else
            _ -> meta
          end

        {{:attribute_access, meta, [left]}, state}

      # Range operators
      type when type in [:range, :range_inclusive] ->
        {right, state} = parse_infix_rhs(state, right_bp, {op_lexeme, token.span})
        inclusive = type == :range_inclusive
        meta = [inclusive: inclusive, line: token.line, col: token.col]
        meta = put_operator_source_info(meta, left, right, token)
        {{:range, meta, [left, right]}, state}

      # Assignment
      :assign ->
        {right, state} = parse_infix_rhs(state, right_bp, {op_lexeme, token.span})
        {{:assignment, [line: token.line, col: token.col], [left, right]}, state}

      # Generic (user-declared) overloadable operator: build a `:binary_op` node
      # tagged `category: :overloaded` and carrying the operator lexeme as its
      # `operator:` atom. The elaborator desugars it to a call on a function
      # named by the lexeme (`Resolve.method_call`/`Overload.resolve`), keeping
      # the Phase-2 primitive/`struct_eq`/`combine` fast paths for the built-ins.
      :operator ->
        {right, state} = parse_infix_rhs(state, right_bp, {op_lexeme, token.span})
        op = String.to_atom(token.value)
        meta = [category: :overloaded, operator: op, line: token.line, col: token.col]
        meta = put_operator_source_info(meta, left, right, token)
        {{:binary_op, meta, [left, right]}, state}

      # Regular built-in binary operator (arithmetic/comparison/boolean/…):
      # dedicated node with its historical category + symbol, unchanged.
      _ ->
        {right, state} = parse_infix_rhs(state, right_bp, {op_lexeme, token.span})
        category = Precedence.operator_category(token.type)
        op = Precedence.operator_symbol(token.type)
        meta = [category: category, operator: op, line: token.line, col: token.col]
        meta = put_operator_source_info(meta, left, right, token)
        {{:binary_op, meta, [left, right]}, state}
    end
  end

  defp put_operator_source_info(meta, left, right, token) do
    operands = Enum.flat_map([left, right], &node_source_span/1)
    operator = if match?(%Cure.Diagnostic.Span{}, token.span), do: token.span, else: nil

    whole_spans = if is_nil(left) and operator, do: [operator | operands], else: operands

    whole =
      case whole_spans do
        [first | rest] ->
          Enum.reduce(rest, first, &merge_source_spans/2)

        [] ->
          operator
      end

    if whole || operator do
      Keyword.put(meta, :source_info, %SourceInfo{whole: whole, operator: operator, operands: operands})
    else
      meta
    end
  end

  defp node_source_span({_, node_meta, _}) when is_list(node_meta) do
    case Metadata.source_info(node_meta) do
      %SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> [span]
      _ -> []
    end
  end

  defp node_source_span(_), do: []

  defp merge_source_spans(%Cure.Diagnostic.Span{} = right, %Cure.Diagnostic.Span{} = left) do
    start = if left.start_byte <= right.start_byte, do: left, else: right
    ending = if left.end_byte >= right.end_byte, do: left, else: right

    %Cure.Diagnostic.Span{
      start
      | end_byte: ending.end_byte,
        end_line: ending.end_line,
        end_column: ending.end_column
    }
  end

  # -- Pipe Desugaring -------------------------------------------------------

  defp desugar_pipe(left, right, token) do
    case right do
      {:function_call, meta, args} ->
        name = Keyword.get(meta, :name, "unknown")
        new_meta = Keyword.merge(meta, pipe: true, line: token.line, col: token.col)
        new_meta = Keyword.put(new_meta, :name, name)
        new_meta = prepend_pipe_label_metadata(new_meta)
        new_meta = put_pipe_source_info(new_meta, left, right, token)
        {:function_call, new_meta, [left | args]}

      {:variable, _meta, name} = variable ->
        meta = [name: name, pipe: true, line: token.line, col: token.col]
        {:function_call, put_pipe_source_info(meta, left, variable, token), [left]}

      _ ->
        meta = [name: "unknown", pipe: true, line: token.line, col: token.col]
        {:function_call, put_pipe_source_info(meta, left, right, token), [left, right]}
    end
  end

  defp put_pipe_source_info(meta, left, right, %Token{} = token) do
    left_span = ast_source_span(left)
    right_span = ast_source_span(right)
    existing = Metadata.source_info(meta) || %SourceInfo{}

    whole =
      case {left_span, right_span} do
        {%Cure.Diagnostic.Span{} = first, %Cure.Diagnostic.Span{} = last} ->
          case Range.through(first, last) do
            {:ok, span} -> span
            _ -> existing.whole
          end

        _ ->
          existing.whole
      end

    callee = existing.callee || right_span
    arguments = if left_span, do: [left_span | existing.arguments], else: existing.arguments

    Metadata.put_source_info(meta, %{
      existing
      | whole: whole,
        callee: callee,
        operator: token.span,
        arguments: arguments
    })
  end

  defp prepend_pipe_label_metadata(meta) do
    case Keyword.get(meta, :arg_labels) do
      labels when is_list(labels) ->
        meta = Keyword.put(meta, :arg_labels, [nil | labels])

        case Metadata.source_info(meta) do
          %SourceInfo{} = info ->
            Metadata.put_source_info(meta, %{info | argument_labels: [nil | info.argument_labels]})

          _ ->
            meta
        end

      _ ->
        meta
    end
  end

  # -- Function Call ---------------------------------------------------------

  defp parse_call(state, func) do
    token = peek(state)
    state = advance(state)
    name = extract_call_name(func)
    # Argument labels (`f(to: v)`) are a FUNCTION-call spelling. A PascalCase head
    # is a constructor application, where `Ctor(n: T, …)` is instead a TYPED
    # PATTERN (`maybe_wrap_as/2`) — the two spellings are syntactically identical
    # (`identifier :`), so the head's case is what disambiguates them. Only allow
    # label-grabbing for the non-constructor (function) head.
    allow_labels = not is_pascal_case?(func)

    {args, arg_labels, arg_label_spans, state, close_token} =
      parse_call_args(state, allow_labels, name, token)

    meta = [name: name, line: token.line, col: token.col]

    # Carry written argument labels only when at least one is present, so the
    # common all-positional call keeps its exact historical meta shape.
    meta =
      if Enum.any?(arg_labels) do
        Keyword.put(meta, :arg_labels, arg_labels)
      else
        meta
      end

    # When the callee is an expression (e.g. f(x)(y)), preserve it so
    # the codegen can compile it as an expression-based call.
    meta =
      if name == "unknown" do
        Keyword.put(meta, :callee, func)
      else
        meta
      end

    meta = put_call_source_info(meta, func, args, arg_label_spans, token, close_token)

    ast = {:function_call, meta, args}
    {ast, state}
  end

  defp put_call_source_info(meta, func, args, argument_label_spans, open_token, close_token) do
    callee_span =
      case func do
        {_, func_meta, _} when is_list(func_meta) ->
          func_meta |> Metadata.source_info() |> source_whole()

        _ ->
          nil
      end

    argument_spans =
      Enum.flat_map(args, fn
        {_, argument_meta, _} when is_list(argument_meta) ->
          case Metadata.source_info(argument_meta) do
            %SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> [span]
            _ -> []
          end

        _ ->
          []
      end)

    whole =
      case {callee_span, close_token, open_token.span} do
        {%Cure.Diagnostic.Span{} = callee, %Token{} = close, _} ->
          case Range.through(callee, close) do
            {:ok, span} -> span
            _ -> nil
          end

        {nil, %Token{} = close, %Cure.Diagnostic.Span{} = open} ->
          case Range.through(open, close) do
            {:ok, span} -> span
            _ -> nil
          end

        _ ->
          nil
      end

    case whole do
      %Cure.Diagnostic.Span{} = span ->
        Keyword.put(meta, :source_info, %SourceInfo{
          whole: span,
          callee: callee_span,
          arguments: argument_spans,
          argument_labels: argument_label_spans
        })

      _ ->
        meta
    end
  end

  defp source_whole(%SourceInfo{whole: span}), do: span
  defp source_whole(_), do: nil

  defp put_type_application_source_info(meta, start, args, close_token) do
    start_span =
      case start do
        %Token{span: %Cure.Diagnostic.Span{} = span} -> span
        %Cure.Diagnostic.Span{} = span -> span
        {_, node_meta, _} when is_list(node_meta) -> node_meta |> Metadata.source_info() |> source_whole()
        _ -> nil
      end

    argument_spans = Enum.flat_map(args, &node_source_span/1)

    whole =
      case {start_span, close_token} do
        {%Cure.Diagnostic.Span{} = first, %Token{} = close} ->
          case Range.through(first, close) do
            {:ok, span} -> span
            _ -> nil
          end

        _ ->
          nil
      end

    case whole do
      %Cure.Diagnostic.Span{} = span ->
        Keyword.put(meta, :source_info, %SourceInfo{whole: span, arguments: argument_spans})

      _ ->
        meta
    end
  end

  defp put_tuple_type_source_info(meta, name_token, open_token, types, close_token) do
    argument_spans = Enum.flat_map(types, &node_source_span/1)

    case {name_token, open_token, close_token} do
      {%Token{span: %Cure.Diagnostic.Span{} = name}, %Token{span: %Cure.Diagnostic.Span{} = opener},
       %Token{span: %Cure.Diagnostic.Span{} = closer} = close} ->
        case Range.through(name, close) do
          {:ok, whole} ->
            Keyword.put(meta, :source_info, %SourceInfo{
              whole: whole,
              name: name,
              opener: opener,
              closer: closer,
              arguments: argument_spans
            })

          _ ->
            meta
        end

      _ ->
        meta
    end
  end

  # Returns {args, labels, label_spans, state, close_token}: `labels` and
  # `label_spans` are position-aligned with `args`; each label entry is the
  # entry the written argument label (`f(to: v)`) or `nil` when the argument is
  # positional. Callers that ignore labels bind the middle element to `_`.
  defp parse_call_args(state, allow_labels), do: parse_call_args(state, allow_labels, nil, nil)

  defp parse_call_args(state, allow_labels, call_name, open_token) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        close_token = peek(state)
        {[], [], [], advance(state), close_token}

      _ ->
        {label, label_span, state} = parse_arg_label(state, allow_labels)
        {first, state} = parse_expr(state, 0)
        {first, state} = maybe_wrap_as(first, state)
        state = skip_newlines(state)
        {rest, rest_labels, rest_label_spans, state} = parse_more_args(state, allow_labels)
        state = skip_newlines(state)

        {state, close_token} =
          case expect_token(state, :rparen) do
            {:ok, token, next_state} ->
              {next_state, token}

            {:error, next_state} ->
              args = [first | rest]
              {contextualize_call_close_error(next_state, call_name, open_token, args), nil}
          end

        {[first | rest], [label | rest_labels], [label_span | rest_label_spans], state, close_token}
    end
  end

  defp contextualize_call_close_error(state, nil, nil, _args), do: state

  defp contextualize_call_close_error(state, call_name, open_token, args) do
    observed = peek(state)

    kind =
      cond do
        observed.type == :eof -> :call_unclosed
        call_argument_start?(observed) -> :call_argument_separator_missing
        true -> nil
      end

    if kind do
      [_generic | rest] = state.errors
      previous = args |> List.last() |> first_node_source_span()

      span =
        if kind == :call_argument_separator_missing do
          %{
            observed.span
            | end_byte: observed.span.start_byte,
              end_line: observed.span.start_line,
              end_column: observed.span.start_column
          }
        else
          observed.span
        end

      error =
        {:call_arguments_syntax,
         %{
           kind: kind,
           call: call_name,
           expected: if(kind == :call_argument_separator_missing, do: :comma, else: :rparen),
           observed: observed.value || observed.type,
           token_type: observed.type,
           span: span,
           observed_span: observed.span,
           opener_span: open_token.span,
           previous_span: previous,
           line: observed.line,
           column: observed.col
         }}

      %{state | errors: [error | rest]}
    else
      state
    end
  end

  defp call_argument_start?(%Token{type: type})
       when type in [
              :identifier,
              :keyword,
              :integer,
              :float,
              :string,
              :char,
              :atom,
              :lparen,
              :lbracket,
              :tuple_open,
              :map_open,
              :binary_open,
              :fn,
              :minus,
              :plus,
              :bang,
              :question
            ],
       do: true

  defp call_argument_start?(_token), do: false

  defp parse_more_args(state, allow_labels) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {label, label_span, state} = parse_arg_label(state, allow_labels)
        {expr, state} = parse_expr(state, 0)
        {expr, state} = maybe_wrap_as(expr, state)
        state = skip_newlines(state)
        {rest, rest_labels, rest_label_spans, state} = parse_more_args(state, allow_labels)
        {[expr | rest], [label | rest_labels], [label_span | rest_label_spans], state}

      _ ->
        {[], [], [], state}
    end
  end

  # A leading `identifier :` at an argument position is a Swift-style argument
  # label (`f(to: v)`). This spelling is otherwise a parse error in a paren call
  # — `:colon` has no infix binding power — so recognising it here is purely
  # additive and never reinterprets valid existing syntax. Consumes the
  # identifier and the colon; returns {nil, nil, state} when no label is present.
  #
  # `allow_labels` is false under a PascalCase (constructor) head, where the same
  # `identifier :` spelling is a TYPED PATTERN (`Cons(n: Int, rest)`) that must
  # reach `maybe_wrap_as/2` untouched.
  defp parse_arg_label(state, allow_labels) do
    tok = peek(state)
    next = peek_at(state, 1)

    if allow_labels && tok && tok.type == :identifier && next && next.type == :colon do
      {to_string(tok.value), tok.span, state |> advance() |> advance()}
    else
      {nil, nil, state}
    end
  end

  defp extract_call_name({:variable, _meta, name}), do: name

  defp extract_call_name({:attribute_access, meta, [parent]}) do
    # Reconstruct dotted name: Mod.Sub.func -> "Mod.Sub.func"
    attr = Keyword.get(meta, :attribute, "unknown")
    parent_name = extract_dotted_path(parent)

    case parent_name do
      nil -> attr
      path -> path <> "." <> attr
    end
  end

  defp extract_call_name(_), do: "unknown"

  defp extract_dotted_path({:variable, _, name}), do: name

  defp extract_dotted_path({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute, "unknown")

    case extract_dotted_path(parent) do
      nil -> attr
      path -> path <> "." <> attr
    end
  end

  defp extract_dotted_path(_), do: nil

  @doc "Reconstruct a dotted path string from an attribute_access/variable node, or nil."
  def dotted_path_of(node), do: extract_dotted_path(node)

  # -- Record Construction / Update  Name{fields}  or  Name{base | overrides} --

  defp parse_record_construction(state, name_ast) do
    open_token = peek(state)
    # consume {
    state = advance(state)

    rec_name =
      case name_ast do
        {:variable, _, n} -> n
        _ -> "unknown"
      end

    line = open_token.line
    col = open_token.col

    state = skip_newlines(state)

    {layout?, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, state |> advance() |> skip_newlines()}
        _ -> {false, state}
      end

    case peek(state) do
      %Token{type: :rbrace} ->
        # Empty construction: TypeName{}
        close_token = peek(state)
        state = advance(state)

        meta =
          put_record_source_info(
            [name: rec_name, record: true, line: line, col: col],
            name_ast,
            open_token,
            state,
            close_token,
            []
          )

        ast = {:function_call, meta, []}
        {ast, state}

      %Token{type: :dedent} when layout? ->
        state = close_record_layout(state, true)
        {state, close_token} = expect_container_close(state, :rbrace, :record, open_token, [], true)

        meta =
          put_record_source_info(
            [name: rec_name, record: true, line: line, col: col],
            name_ast,
            open_token,
            state,
            close_token,
            []
          )

        ast = {:function_call, meta, []}
        {ast, state}

      _ ->
        # Probe: parse one expression to detect update syntax.
        # :bar ("|") is not an infix operator, so parse_expr stops naturally at it.
        # We save pos+errors so we can fully rewind on a non-update literal.
        saved_pos = state.pos
        saved_errors = state.errors
        {base_expr, probe_state} = parse_expr(state, 0)
        probe_state = skip_newlines(probe_state)

        case peek(probe_state) do
          %Token{type: :bar} ->
            # Record update: TypeName{base | field: val, ...}
            # consume "|"
            probe_state = advance(probe_state)
            probe_state = skip_newlines(probe_state)
            {fields, probe_state} = parse_map_pairs(probe_state, :rbrace, open_token, :record)
            probe_state = close_record_layout(probe_state, layout?)

            {probe_state, close_token} =
              expect_container_close(probe_state, :rbrace, :record, open_token, fields, true)

            meta =
              put_record_source_info(
                [name: rec_name, line: line, col: col],
                name_ast,
                open_token,
                probe_state,
                close_token,
                fields
              )

            ast = {:record_update, meta, [base_expr | fields]}
            {ast, probe_state}

          _ ->
            # Not update syntax: rewind completely and parse as plain construction.
            state = %{state | pos: saved_pos, errors: saved_errors}
            {fields, state} = parse_map_pairs(state, :rbrace, open_token, :record)
            state = close_record_layout(state, layout?)
            {state, close_token} = expect_container_close(state, :rbrace, :record, open_token, fields, true)

            meta =
              put_record_source_info(
                [name: rec_name, record: true, line: line, col: col],
                name_ast,
                open_token,
                state,
                close_token,
                fields
              )

            ast = {:function_call, meta, fields}
            {ast, state}
        end
    end
  end

  defp close_record_layout(state, true), do: state |> skip_newlines() |> expect_dedent() |> skip_newlines()
  defp close_record_layout(state, false), do: state

  defp put_record_source_info(meta, name_ast, open_token, _state, close_token, fields) do
    name_span = first_node_source_span(name_ast)

    whole =
      case {name_span || open_token.span, close_token} do
        {%Cure.Diagnostic.Span{} = first, %Token{} = close} ->
          case Range.through(first, close) do
            {:ok, span} -> span
            _ -> nil
          end

        _ ->
          nil
      end

    field_spans =
      Enum.reduce(fields, %{}, fn
        {:pair, pair_meta, [key | _]}, acc ->
          case Metadata.source_info(pair_meta) do
            %SourceInfo{name: %Cure.Diagnostic.Span{} = field} ->
              Map.put(acc, field_name(key), field)

            _ ->
              acc
          end

        _, acc ->
          acc
      end)

    if whole do
      Keyword.put(meta, :source_info, %SourceInfo{
        whole: whole,
        name: name_span,
        opener: open_token.span,
        closer: if(match?(%Token{span: %Cure.Diagnostic.Span{}}, close_token), do: close_token.span),
        fields: field_spans
      })
    else
      meta
    end
  end

  defp is_pascal_case?({:variable, _, <<first, _rest::binary>>}) when first in ?A..?Z, do: true

  # A qualified head (`Mod.Ctor`, `Std.Nat.S`) is PascalCase by its FINAL
  # segment — the constructor/type name a caller actually writes — regardless of
  # the leading module path's case. Without this, `Std.Nat.S(n: Std.Nat)` (a
  # qualified constructor pattern with a typed field binder) is mistaken for a
  # labelled function call: `n:` is swallowed as an argument label instead of
  # reaching `maybe_wrap_as/2` to parse as `{:typed_pattern, _, ["n", ...]}`,
  # silently dropping the `n` binder.
  defp is_pascal_case?({:attribute_access, meta, _}) do
    case Keyword.get(meta, :attribute) do
      <<first, _rest::binary>> when first in ?A..?Z -> true
      _ -> false
    end
  end

  defp is_pascal_case?(_), do: false

  # -- Collections -----------------------------------------------------------

  # List: [1, 2, 3] or [h | t] or comprehension [x for x <- list]
  defp parse_list_or_comprehension(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbracket} ->
        # Empty list
        close_token = peek(state)
        state = advance(state)
        meta = put_container_source_info([line: token.line, col: token.col], token, state, close_token)
        {{:list, meta, []}, state}

      _ ->
        {first, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        case peek(state) do
          # Comprehension: [expr for ...]
          %Token{type: :keyword, value: :for} ->
            parse_comprehension(state, first, token)

          # Cons: [h | t]
          %Token{type: :bar} ->
            state = advance(state)
            state = skip_newlines(state)
            {tail, state} = parse_expr(state, 0)
            state = skip_newlines(state)

            {state, close_token} =
              expect_container_close(state, :rbracket, :list_cons, token, [first, tail], false)

            meta =
              put_container_source_info(
                [cons: true, line: token.line, col: token.col],
                token,
                state,
                close_token
              )

            ast = {:list, meta, [first, tail]}
            {ast, state}

          # Multi-head cons or regular list: [a, b, c]  or  [a, b | rest]
          _ ->
            {rest_heads, state} = parse_multi_head_list_rest(state, token, first)

            case peek(state) do
              %Token{type: :bar} ->
                # `[a, b | rest]` -- desugar into right-associated cons
                # cells: `[a | [b | rest]]`.
                state = advance(state)
                state = skip_newlines(state)
                {tail, state} = parse_expr(state, 0)
                state = skip_newlines(state)

                {state, close_token} =
                  expect_container_close(
                    state,
                    :rbracket,
                    :list_cons,
                    token,
                    [first | rest_heads] ++ [tail],
                    false
                  )

                heads = [first | rest_heads]
                ast = build_multi_head_cons(heads, tail, token)
                ast = put_container_source_info_ast(ast, token, state, close_token)
                {ast, state}

              _ ->
                state = skip_newlines(state)
                elements = [first | rest_heads]

                {state, close_token} =
                  expect_container_close(state, :rbracket, :list, token, elements, true)

                meta = put_container_source_info([line: token.line, col: token.col], token, state, close_token)
                ast = {:list, meta, elements}
                {ast, state}
            end
        end
    end
  end

  # Parse `, expr` repeatedly, stopping before `|` or `]`.
  defp parse_multi_head_list_rest(state, open_token, previous) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} = comma ->
        state = advance(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :rbracket} ->
            {[], add_container_trailing_separator(state, :list, open_token, previous, comma)}

          _ ->
            {expr, state} = parse_expr(state, 0)
            state = skip_newlines(state)
            {rest, state} = parse_multi_head_list_rest(state, open_token, expr)
            {[expr | rest], state}
        end

      _ ->
        {[], state}
    end
  end

  # Build nested cons cells right-associatively:
  #   [a, b, c | rest]  ->  [a | [b | [c | rest]]]
  defp build_multi_head_cons([head], tail, token),
    do: {:list, [cons: true, line: token.line, col: token.col], [head, tail]}

  defp build_multi_head_cons([head | rest], tail, token) do
    nested = build_multi_head_cons(rest, tail, token)
    {:list, [cons: true, line: token.line, col: token.col], [head, nested]}
  end

  # Tuple: %[a, b, c]
  defp parse_tuple(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbracket} ->
        close_token = peek(state)
        state = advance(state)
        meta = put_container_source_info([line: token.line, col: token.col], token, state, close_token)
        {{:tuple, meta, []}, state}

      _ ->
        {first, state} = parse_expr(state, 0)
        {rest, state} = parse_container_comma_exprs(state, :tuple, token, first)
        state = skip_newlines(state)
        elements = [first | rest]

        {state, close_token} =
          expect_container_close(state, :rbracket, :tuple, token, elements, true)

        meta = put_container_source_info([line: token.line, col: token.col], token, state, close_token)

        {:tuple, meta, elements}
        |> then(&{&1, state})
    end
  end

  defp parse_container_comma_exprs(state, container, open_token, previous) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} = comma ->
        state = advance(state) |> skip_newlines()

        case peek(state) do
          %Token{type: :rbracket} ->
            {[], add_container_trailing_separator(state, container, open_token, previous, comma)}

          _ ->
            {expr, state} = parse_expr(state, 0)
            {rest, state} = parse_container_comma_exprs(state, container, open_token, expr)
            {[expr | rest], state}
        end

      _ ->
        {[], state}
    end
  end

  defp add_container_trailing_separator(state, container, open_token, previous, comma) do
    error =
      {:container_elements_syntax,
       %{
         kind: :container_trailing_separator,
         container: container,
         expected: :element,
         observed: comma.value || comma.type,
         token_type: comma.type,
         span: comma.span,
         opener_span: open_token.span,
         previous_span: first_node_source_span(previous),
         line: comma.line,
         column: comma.col
       }}

    add_error(state, error)
  end

  defp expect_container_close(state, closing, container, open_token, elements, separator_allowed) do
    expect_container_close(state, closing, container, open_token, elements, separator_allowed, %{})
  end

  defp expect_container_close(state, closing, container, open_token, elements, separator_allowed, context) do
    case expect_token(state, closing) do
      {:ok, token, next_state} ->
        {next_state, token}

      {:error, next_state} ->
        observed = peek(next_state)

        closing_boundary? =
          observed.type in Map.get(context, :closing_tokens, []) or
            observed.value in Map.get(context, :closing_values, [])

        kind =
          cond do
            observed.type in [:eof, :dedent, :newline] or closing_boundary? -> :container_unclosed
            separator_allowed and call_argument_start?(observed) -> :container_separator_missing
            true -> nil
          end

        if kind do
          [_generic | rest] = next_state.errors

          previous =
            Map.get(context, :previous_span) ||
              elements |> List.last() |> first_node_source_span() ||
              previous_authored_span(next_state, open_token.span)

          span =
            if kind == :container_separator_missing or observed.type == :newline or closing_boundary? do
              %{
                observed.span
                | end_byte: observed.span.start_byte,
                  end_line: observed.span.start_line,
                  end_column: observed.span.start_column
              }
            else
              observed.span
            end

          details =
            Map.merge(context, %{
              kind: kind,
              container: container,
              expected: if(kind == :container_separator_missing, do: :comma, else: closing),
              observed: observed.value || observed.type,
              token_type: observed.type,
              span: span,
              observed_span: observed.span,
              opener_span: open_token.span,
              previous_span: previous,
              line: observed.line,
              column: observed.col
            })

          error = {:container_elements_syntax, details}

          {%{next_state | errors: [error | rest]}, nil}
        else
          {next_state, nil}
        end
    end
  end

  # Recovery diagnostics sometimes parse scalar elements (for example names in
  # an import list) which deliberately have no AST metadata. Recover their
  # exact ownership from the token immediately before the observed token. This
  # is not used to construct successful AST ranges.
  defp previous_authored_span(state, fallback) do
    state.tokens
    |> Tuple.to_list()
    |> Enum.take(state.pos)
    |> Enum.reverse()
    |> Enum.find(fn
      %Token{type: type} -> type not in [:newline, :indent, :dedent]
      _ -> false
    end)
    |> case do
      %Token{span: %Cure.Diagnostic.Span{} = span} -> span
      _ -> fallback
    end
  end

  # Map: %{k: v, ...} or %{k => v, ...}
  defp parse_map(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        close_token = peek(state)
        state = advance(state)
        meta = put_container_source_info([line: token.line, col: token.col], token, state, close_token)
        {{:map, meta, []}, state}

      _ ->
        {pairs, state} = parse_map_pairs(state, :rbrace, token, :map)
        state = skip_newlines(state)
        {state, close_token} = expect_container_close(state, :rbrace, :map, token, pairs, true)
        meta = put_container_source_info([line: token.line, col: token.col], token, state, close_token)
        {{:map, meta, pairs}, state}
    end
  end

  defp parse_map_pairs(state, closing, open_token, container) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: ^closing} ->
        {[], state}

      _ ->
        {pair, state} = parse_map_pair(state, open_token, container)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            {rest, state} = parse_map_pairs(state, closing, open_token, container)
            {[pair | rest], state}

          _ ->
            {[pair], state}
        end
    end
  end

  defp parse_map_pair(state, open_token, container) do
    token = peek(state)
    next = peek_at(state, 1)

    cond do
      # Shorthand: identifier followed by colon  =>  atom key
      token.type == :identifier and next != nil and next.type == :colon ->
        key_atom = String.to_atom(token.value)
        separator_token = next
        state = advance(state) |> advance()
        state = skip_newlines(state)
        {value, state} = parse_expr(state, 0)
        pair_meta = put_field_source_info([], token, token.span, separator_token, value)
        pair = {:pair, pair_meta, [{:literal, [subtype: :symbol], key_atom}, value]}
        {pair, state}

      # Pattern/construction field punning (v0.18.0): a bare identifier
      # followed by `,` or the closing delimiter is shorthand for
      # `name: name`. Used both in record patterns (`Point{x, y}`) and in
      # map-construction shorthand (`%{x, y}` -> `%{x: x, y: y}`).
      token.type == :identifier and next != nil and
          next.type in [:comma, :rbrace, :newline] ->
        key_atom = String.to_atom(token.value)
        var_ast = variable(token)
        state = advance(state)
        pair_meta = put_field_source_info([pun: true], token, token.span, nil, var_ast)
        pair = {:pair, pair_meta, [{:literal, [subtype: :symbol], key_atom}, var_ast]}
        {pair, state}

      true ->
        # Explicit: key => value
        {key, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        {separator_token, state} = expect_map_entry_separator(state, open_token, token, key, container)
        state = skip_newlines(state)
        {value, state} = parse_expr(state, 0)

        pair_meta =
          put_field_source_info(
            [field: field_name(key)],
            token,
            first_node_source_span(key),
            separator_token,
            value
          )

        pair = {:pair, pair_meta, [key, value]}
        {pair, state}
    end
  end

  defp expect_map_entry_separator(state, open_token, entry_token, key, container) do
    case expect_token(state, :fat_arrow) do
      {:ok, arrow, next_state} ->
        {arrow, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)
        ambiguous? = match?({:variable, _, _}, key) and call_argument_start?(observed)

        error =
          {:declaration_separator_missing,
           %{
             kind: :map_entry_separator_missing,
             container: container,
             ambiguous: ambiguous?,
             expected: if(ambiguous?, do: nil, else: :fat_arrow),
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: open_token.span,
             previous_span: first_node_source_span(key),
             entry_span: entry_token.span,
             key: field_name(key),
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp put_field_source_info(meta, start_token, field_span, separator_token, value) do
    value_span = ast_source_span(value)
    whole = through_spans(start_token.span, value_span) || start_token.span

    if whole do
      Metadata.put_source_info(meta, %SourceInfo{
        whole: whole,
        name: field_span,
        operator: separator_token && separator_token.span,
        body: value_span
      })
    else
      meta
    end
  end

  defp field_name({:variable, _meta, name}), do: name
  defp field_name({:literal, _meta, name}) when is_atom(name), do: name
  defp field_name(_), do: :unknown

  # Binary literal / pattern: <<seg1, seg2, ...>>
  #
  # Each segment is `value [:: specifier_chain]` where the chain is a
  # hyphen-joined list of specifiers (mirrors Elixir):
  #
  #   integer | float | bits | bitstring | bytes | binary | utf8 | utf16 | utf32
  #   signed | unsigned
  #   big | little | native
  #   size(expr)
  #   unit(n)
  #   <integer>           (shorthand for size(<integer>))
  #
  # The segment is emitted as
  #   {:bin_segment, [type:, signedness:, endianness:, size:, unit:, line:, col:], [value]}
  # with each keyword omitted when the caller did not supply one. The enclosing
  # literal keeps its historical shape
  #   {:literal, [subtype: :bytes, line:, col:], [bin_segment, ...]}
  # so downstream consumers that only care about the outer shape are unaffected.
  defp parse_binary_literal(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :binary_close} ->
        {{:literal, [subtype: :bytes, line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {segments, state} = parse_bin_segments(state, [])
        {state, close_token} = expect_container_close(state, :binary_close, :binary_literal, token, segments, false)

        meta = [subtype: :bytes, line: token.line, col: token.col]
        meta = put_container_source_info(meta, token, state, close_token)
        ast = {:literal, meta, segments}
        {ast, state}
    end
  end

  defp parse_bin_segments(state, acc) do
    {segment, state} = parse_bin_segment(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        parse_bin_segments(state, [segment | acc])

      _ ->
        {Enum.reverse([segment | acc]), state}
    end
  end

  defp parse_bin_segment(state) do
    start_token = peek(state)
    {value, state} = parse_expr(state, 0)

    {specifier_meta, specifier_token, terminal_span, state} =
      case peek(state) do
        %Token{type: :colon_colon} = specifier_token ->
          state = advance(state)
          {meta, state, terminal_span} = parse_bin_specifier_chain(state, [])
          {meta, specifier_token, terminal_span, state}

        _ ->
          {[], nil, ast_source_span(value), state}
      end

    meta = [line: start_token.line, col: start_token.col] ++ specifier_meta
    meta = put_binary_segment_source_info(meta, start_token, value, specifier_token, terminal_span)

    {{:bin_segment, meta, [value]}, state}
  end

  defp put_binary_segment_source_info(meta, start_token, value, specifier_token, terminal_span) do
    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(start_token.span, terminal_span) || ast_source_span(value),
      operator: specifier_token && specifier_token.span,
      body: ast_source_span(value),
      arguments: specifier_argument_spans(meta)
    })
  end

  defp specifier_argument_spans(meta) do
    meta
    |> Keyword.take([:size, :unit])
    |> Enum.flat_map(fn {_key, value} -> node_source_span(value) end)
  end

  defp parse_bin_specifier_chain(state, acc) do
    {entry, state, terminal_span} = parse_bin_specifier(state)
    acc = merge_specifier(acc, entry)

    case peek(state) do
      %Token{type: :minus} ->
        state = advance(state)
        parse_bin_specifier_chain(state, acc)

      _ ->
        {acc, state, terminal_span}
    end
  end

  # A single specifier fragment. Accepts:
  #   * identifiers (`integer`, `binary`, `utf8`, `size`, `unit`, etc.)
  #   * `size(expr)` and `unit(n)` call-style forms
  #   * bare integer literals as shorthand for `size(n)`
  # Returns `{:type | :signedness | :endianness | :size | :unit, value}`.
  defp parse_bin_specifier(state) do
    token = peek(state)

    case token.type do
      :integer ->
        state = advance(state)

        {{:size, {:literal, [subtype: :integer, line: token.line, col: token.col], token.value}}, state, token.span}

      :identifier ->
        name = to_string(token.value)
        state = advance(state)

        case peek(state) do
          %Token{type: :lparen} when name in ["size", "unit"] ->
            open_token = peek(state)
            state = advance(state)
            state = skip_newlines(state)
            {arg, state} = parse_expr(state, 0)
            state = skip_newlines(state)

            {state, close_token} =
              expect_container_close(state, :rparen, :binary_specifier_arguments, open_token, [arg], false, %{
                specifier: name,
                specifier_span: token.span,
                closing_tokens: [:binary_close, :minus, :comma]
              })

            {{String.to_atom(name), arg}, state, (close_token && close_token.span) || ast_source_span(arg)}

          _ ->
            {classify_bin_specifier_name(name), state, token.span}
        end

      _ ->
        # Unknown specifier token -- consume and ignore so we don't deadlock.
        state = advance(state)
        {{:type, :any}, state, token.span}
    end
  end

  defp classify_bin_specifier_name(name) do
    type_names = ~w(integer float bits bitstring bytes binary utf8 utf16 utf32)
    sign_names = ~w(signed unsigned)
    endian_names = ~w(big little native)

    cond do
      name in type_names -> {:type, String.to_atom(name)}
      name in sign_names -> {:signedness, String.to_atom(name)}
      name in endian_names -> {:endianness, String.to_atom(name)}
      true -> {:type, String.to_atom(name)}
    end
  end

  # Merge a single specifier entry into the meta-accumulator. Later
  # entries override earlier entries for the same axis, matching
  # Elixir's "last wins" behaviour for duplicate specifiers.
  defp merge_specifier(acc, {key, value}) do
    Keyword.put(acc, key, value)
  end

  # -- Comprehensions --------------------------------------------------------

  defp parse_comprehension(state, body, open_token) do
    # Already consumed body, currently at `for` keyword
    state = advance(state)
    state = skip_newlines(state)
    {generators_and_filters, state} = parse_generators(state)
    state = skip_newlines(state)

    {state, close_token} =
      expect_container_close(
        state,
        :rbracket,
        :comprehension,
        open_token,
        [body | generators_and_filters],
        false
      )

    meta =
      put_container_source_info(
        [line: open_token.line, col: open_token.col],
        open_token,
        state,
        close_token
      )

    ast = {:comprehension, meta, [body | generators_and_filters]}
    {ast, state}
  end

  defp put_container_source_info(meta, open_token, _state, close_token) do
    case {open_token.span, close_token} do
      {%Cure.Diagnostic.Span{} = opener, %Token{span: %Cure.Diagnostic.Span{} = closer}} ->
        case Range.through(opener, closer) do
          {:ok, whole} ->
            Keyword.put(meta, :source_info, %SourceInfo{whole: whole, opener: opener, closer: closer})

          _ ->
            meta
        end

      _ ->
        meta
    end
  end

  defp put_container_source_info_ast({tag, meta, children}, open_token, state, close_token)
       when is_list(meta) do
    {tag, put_container_source_info(meta, open_token, state, close_token), children}
  end

  defp put_container_source_info_ast(ast, _open_token, _state, _close_token), do: ast

  defp parse_generators(state) do
    {item, state} = parse_generator_or_filter(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_generators(state)
        {[item | rest], state}

      _ ->
        {[item], state}
    end
  end

  defp parse_generator_or_filter(state) do
    # The lexer emits `<` and `-` as separate tokens for `<-`.
    # Strategy: parse LHS at BP above comparison (42) so `<` is not consumed,
    # then check if `< -` follows (generator) or fall back to a full-BP filter.
    # v0.22.0: a leading `:binary_open` (`<<`) opens a binary-pattern
    # generator (`for <<b <- buf>>`) that otherwise mis-tokenises as
    # a less-than comparison inside the `<<...>>` literal.
    case peek(state) do
      %Token{type: :binary_open} -> parse_binary_generator(state)
      _ -> parse_non_binary_generator_or_filter(state)
    end
  end

  defp parse_non_binary_generator_or_filter(state) do
    saved_pos = state.pos
    {expr, state} = parse_expr(state, bp_above(state, "<"))
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :lt} ->
        next = peek_at(state, 1)

        if next != nil and next.type == :minus do
          # Generator: pattern <- collection
          state = advance(state) |> advance()
          state = skip_newlines(state)
          {collection, state} = parse_expr(state, 0)
          meta = put_clause_source_info([], expr, collection)
          {{:generator, meta, [expr, collection]}, state}
        else
          # Not a generator. Re-parse from saved position at BP 0 for full filter expression.
          state = %{state | pos: saved_pos}
          {filter_expr, state} = parse_expr(state, 0)
          meta = put_clause_source_info([], filter_expr, filter_expr)
          {{:filter, meta, [filter_expr]}, state}
        end

      _ ->
        # Check if the high-BP parse left something behind (e.g. `x > 0`).
        # If the expression was just a variable and there's an operator next, re-parse at BP 0.
        token = peek(state)

        if FixityTable.infix_bp(fixity_table(state), lexeme_of(token)) != :not_infix do
          state = %{state | pos: saved_pos}
          {filter_expr, state} = parse_expr(state, 0)
          meta = put_clause_source_info([], filter_expr, filter_expr)
          {{:filter, meta, [filter_expr]}, state}
        else
          meta = put_clause_source_info([], expr, expr)
          {{:filter, meta, [expr]}, state}
        end
    end
  end

  defp put_clause_source_info(meta, first_node, last_node) do
    with %Cure.Diagnostic.Span{} = first <- first_node_source_span(first_node),
         %Cure.Diagnostic.Span{} = last <- first_node_source_span(last_node),
         {:ok, whole} <- Range.through(first, last) do
      Keyword.put(meta, :source_info, %SourceInfo{whole: whole})
    else
      _ -> meta
    end
  end

  # v0.22.0: binary-pattern generator `<<seg1, seg2, ... <- source>>`.
  # Elixir-style surface syntax wraps the whole generator in `<<...>>`:
  # the pattern segments, the `<-` arrow, and the source expression all
  # live between the opening `<<` and the closing `>>`. The `<-` itself
  # is emitted by the lexer as `:lt` followed by `:minus`; we parse
  # segments at BP 42 so the leading `<` of `<-` is not consumed as a
  # less-than comparison. The resulting AST is
  # `{:binary_generator, meta, [pattern, source]}` where `pattern` is
  # a `{:literal, [subtype: :bytes], segments}` (reusing the v0.21.0
  # pattern-compiler path) and the codegen lowers it to Erlang's
  # `b_generate` qualifier.
  defp parse_binary_generator(state) do
    open_token = peek(state)
    state = advance(state)
    state = skip_newlines(state)
    {segments, state} = parse_binary_generator_segments(state, [])

    state = expect_binary_generator_arrow(state, open_token, segments)

    state = skip_newlines(state)
    {source, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    {state, close_token} =
      expect_container_close(state, :binary_close, :binary_generator, open_token, [source], false)

    pattern =
      {:literal, [subtype: :bytes, line: open_token.line, col: open_token.col], segments}

    meta = [line: open_token.line, col: open_token.col]
    meta = put_container_source_info(meta, open_token, state, close_token)
    {{:binary_generator, meta, [pattern, source]}, state}
  end

  defp expect_binary_generator_arrow(state, open_token, segments) do
    case {peek(state), peek_at(state, 1)} do
      {%Token{type: :lt}, %Token{type: :minus}} ->
        state |> advance() |> advance()

      _ ->
        observed = peek(state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :binary_generator_arrow_missing,
             expected: "<-",
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: open_token.span,
             previous_span: segments |> List.last() |> first_node_source_span(),
             line: observed.line,
             column: observed.col
           }}

        add_error(state, error)
    end
  end

  # Parse `seg1, seg2, ...` inside a binary-generator, stopping when the
  # next token is either the closing `>>` (`:binary_close`) or the
  # generator arrow `<-` (`:lt` + `:minus`). Each segment is parsed via
  # `parse_bin_generator_segment/1` so specifier chains (`::integer`,
  # `::size(n)`, ...) carry through.
  defp parse_binary_generator_segments(state, acc) do
    case peek(state) do
      %Token{type: :binary_close} ->
        {Enum.reverse(acc), state}

      %Token{type: :lt} ->
        next = peek_at(state, 1)

        if next != nil and next.type == :minus do
          {Enum.reverse(acc), state}
        else
          advance_into_segment(state, acc)
        end

      _ ->
        advance_into_segment(state, acc)
    end
  end

  defp advance_into_segment(state, acc) do
    {segment, state} = parse_bin_generator_segment(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        parse_binary_generator_segments(state, [segment | acc])

      _ ->
        {Enum.reverse([segment | acc]), state}
    end
  end

  # Variant of `parse_bin_segment/1` that stops before `<` (BP 40) so
  # the trailing `<-` of a binary generator is not mis-tokenised as a
  # less-than comparison operator.
  defp parse_bin_generator_segment(state) do
    start_token = peek(state)
    {value, state} = parse_expr(state, bp_above(state, "<"))

    {specifier_meta, specifier_token, terminal_span, state} =
      case peek(state) do
        %Token{type: :colon_colon} = specifier_token ->
          state = advance(state)
          {meta, state, terminal_span} = parse_bin_specifier_chain(state, [])
          {meta, specifier_token, terminal_span, state}

        _ ->
          {[], nil, ast_source_span(value), state}
      end

    meta = [line: start_token.line, col: start_token.col] ++ specifier_meta
    meta = put_binary_segment_source_info(meta, start_token, value, specifier_token, terminal_span)

    {{:bin_segment, meta, [value]}, state}
  end

  # -- Keyword-Triggered Prefix Expressions ----------------------------------

  defp parse_keyword_prefix(state, token) do
    case token.value do
      :let ->
        parse_let(state)

      :if ->
        parse_if(state)

      :match ->
        parse_match(state)

      :quote ->
        parse_quote(state)

      :unsafe ->
        parse_unsafe(state, token)

      :do ->
        parse_do(state, token)

      :pickup ->
        parse_pickup(state)

      :return ->
        parse_keyword_unary(state, :early_return)

      :throw ->
        parse_keyword_unary(state, :throw)

      :yield ->
        parse_keyword_unary(state, :yield)

      :spawn ->
        parse_keyword_unary(state, :async_operation)

      :send ->
        parse_send(state)

      :receive ->
        parse_receive(state)

      :try ->
        parse_try(state)

      # Structural constructs (Milestone 3)
      :fn ->
        parse_fn_or_lambda(state)

      :local ->
        parse_local(state)

      :mod ->
        parse_module(state)

      :rec ->
        parse_record(state)

      :type ->
        parse_type_def(state)

      # `opaque type Name(params)` — a constructor-less, non-eliminable carrier
      # type. Consume `opaque`, then parse the type head with the opaque flag.
      :opaque ->
        parse_type_def(advance(state), opaque: true)

      # `primitive Name` — an irreducible machine base type (Int/Float/Binary).
      # No constructors, no `=`; the `@builtin(:tag)` marker names its Core node.
      :primitive ->
        parse_primitive_def(state)

      :typealias ->
        parse_typealias(state)

      :proto ->
        parse_proto(state)

      :proof ->
        parse_proof_container(state)

      :impl ->
        parse_impl(state)

      :interface ->
        parse_interface(state)

      :implementation ->
        parse_implementation(state)

      :use ->
        parse_use(state)

      _ ->
        # Treat unknown keywords as identifiers (e.g., type names used as values)
        {variable(token), advance(state)}
    end
  end

  # `unsafe expr` is a prefix marker, not a runtime expression. Keep it on
  # call metadata so elaboration can enforce it after resolving the callee.
  defp parse_unsafe(state, token) do
    state = advance(state)
    {operand, state} = parse_expr(state, 110)

    case operand do
      # `unsafe run do` is the compact spelling for running an indented
      # effect block.  `do` is a keyword, so it cannot be parsed as an
      # ordinary function argument by the Pratt loop; claim it here while the
      # unsafe marker is still available to attach to the generated call.
      {:variable, meta, "run"} when is_list(meta) ->
        case peek(state) do
          %Token{type: :keyword, value: :do} = do_token ->
            {body, state} = parse_do(state, do_token)
            call_meta = Keyword.put(meta, :name, "run")
            call_meta = Keyword.put(call_meta, :unsafe, true)
            call_meta = Keyword.put(call_meta, :unsafe_span, token.span)
            {{:function_call, call_meta, [body]}, state}

          _ ->
            meta = Keyword.put(meta, :unsafe, true) |> Keyword.put(:unsafe_span, token.span)
            {{:variable, meta, "run"}, state}
        end

      {:function_call, meta, args} when is_list(meta) ->
        meta = Keyword.put(meta, :unsafe, true) |> Keyword.put(:unsafe_span, token.span)
        {{:function_call, meta, args}, state}

      _ ->
        {{:unsafe_expression, [line: token.line, col: token.col, unsafe_span: token.span], [operand]}, state}
    end
  end

  # `do` is deliberately a surface-only construct.  Its statements are the
  # same assignments the effect elaborator already understands, but `<-`
  # makes the sequencing intent explicit and avoids pretending that an effect
  # result is an ordinary pure value.
  #
  #     do
  #       value <- operation()
  #       next(value)
  #
  # The resulting block is checked against `Effect(R)` by its context (most
  # commonly `unsafe run`), and the existing elaborator lowers each binding
  # to `effect_bind` and the final pure value to `effect_pure`.
  defp parse_do(state, token) do
    state = advance(state) |> skip_newlines()

    case peek(state) do
      %Token{type: :indent} = indent_token ->
        state = advance(state)
        {exprs, state} = parse_do_block_body(state, indent_token.value, [])
        state = expect_dedent(state)
        meta = [do: true, line: token.line, col: token.col]
        {{:block, meta, exprs}, state}

      observed ->
        state =
          add_error(state, {
            :do_block_indent_missing,
            %{
              expected: :indent,
              observed: observed.type,
              span: zero_width_start(observed.span),
              line: observed.line,
              column: observed.col
            }
          })

        {{:block, [do: true, line: token.line, col: token.col], []}, state}
    end
  end

  defp parse_do_block_body(state, indent, acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      _ ->
        {expr, state} = parse_do_statement(state)
        state = skip_newlines(state)
        parse_do_block_body(state, indent, [expr | acc])
    end
  end

  defp parse_do_statement(state) do
    # Look ahead before parsing a normal expression.  Otherwise the Pratt
    # parser quite correctly treats the first `<` in `<-` as comparison
    # syntax, and the sequencing marker is no longer recoverable.
    case {peek(state), peek_at(state, 1), peek_at(state, 2)} do
      {%Token{type: :identifier} = binder, %Token{type: :lt}, %Token{type: :minus}} ->
        pattern = variable(binder)
        pattern_meta = elem(pattern, 1)
        state = state |> advance() |> advance() |> advance() |> skip_newlines()
        {value, state} = parse_expr_or_block(state)
        meta = [let: true, do_bind: true, line: Keyword.get(pattern_meta, :line), col: Keyword.get(pattern_meta, :col)]
        {{:assignment, meta, [pattern, value]}, state}

      _ ->
        parse_expr(state, 0)
    end
  end

  defp macro_head?(state) do
    case peek_at(state, 1) do
      %Token{type: type} when type in [:identifier, :atom, :quoted_identifier] -> true
      _ -> false
    end
  end

  defp prelude_macro_head?(state, "lens") do
    case peek_at(state, 1) do
      %Token{type: :identifier, value: value} when value in ["first", "second"] -> true
      _ -> false
    end
  end

  defp prelude_macro_head?(state, _name), do: macro_head?(state)

  defp macro_use_head?(state, "lens"), do: prelude_macro_head?(state, "lens")
  defp macro_use_head?(_state, _name), do: true

  defp computed_macro_head?(state, name) do
    rules = Map.get(state.computed_macros, name, []) ++ Map.get(state.builtin_computed_macros, name, [])

    Enum.any?(rules, fn rule ->
      case {rule.segments, peek_at(state, 1)} do
        {[], _next} -> true
        {[{:lit, "("} | _], %Token{type: :lparen}} -> true
        {_segments, %Token{type: :lparen}} -> false
        {_segments, _next} -> true
      end
    end)
  end

  # -- Let Binding -----------------------------------------------------------

  defp parse_let(state), do: parse_local_binding(state, :let)

  defp parse_local_binding(state, kind) when kind in [:let, :have] do
    token = peek(state)
    state = advance(state)

    {grade_prefix, state} = parse_binder_grade_prefix(state)

    # Parse pattern (LHS) at high enough BP to NOT consume `=`: one above the
    # assignment operator's left binding power, read from the fixity table.
    {pattern, state} = parse_expr(state, bp_above(state, "="))

    # `: Type`, or a graded `:g [Type]` — the type is optional after a grade because
    # `let_inferred/8` synthesises it from the rhs (Idris `letBinder` does the same).
    let_name =
      case pattern do
        {:variable, _, n} -> n
        _ -> "let binding"
      end

    # Only a graded binder may stop at `=` with the type left out; an ungraded
    # `let x : = e` states an annotation and then fails to give one.
    stop_on = if grade_prefix, do: [:assign], else: []

    {_ignored_grade, type_ann, state, annotation_span} = parse_binder_annotation(state, let_name, stop_on)
    grade = grade_prefix && elem(grade_prefix, 1)

    # A grade attaches to a SIMPLE VARIABLE binder only. A destructuring `let` lowers
    # to a `case`, whose binders take their grades from the constructor's field
    # quantities, so there is no single Core binder for this grade to land on. Reject
    # it here rather than parse it and silently ignore the annotation.
    state =
      if grade && not match?({:variable, _, _}, pattern) do
        add_error(state, {
          :graded_let_requires_variable,
          %{
            grade: grade,
            pattern_span: first_node_source_span(pattern),
            grade_span: grade_prefix_span(grade_prefix),
            line: token.line,
            column: token.col
          }
        })
      else
        state
      end

    {assign_token, state} = expect_local_binding_assign(state, token, pattern, annotation_span, kind, let_name)
    state = skip_newlines(state)

    # Parse value (RHS) -- might be an indented block
    {value, state} = parse_expr_or_block(state)

    meta = [let: true, line: token.line, col: token.col]
    meta = if kind == :have, do: Keyword.put(meta, :have, true), else: meta
    meta = if type_ann, do: Keyword.put(meta, :type_annotation, type_ann), else: meta
    meta = if grade, do: Keyword.put(meta, :grade, grade), else: meta

    meta =
      put_let_source_info(
        meta,
        token,
        pattern,
        value,
        annotation_span,
        assign_token,
        grade_prefix_span(grade_prefix)
      )

    assignment = {:assignment, meta, [pattern, value]}

    # Optional ML-style `let <pat> = <value> in <body>`: an expression-position
    # binder. Desugar to the same two-statement `{:block, …}` node a block-form
    # `let` followed by a trailing expression produces, which the elaborator
    # already lowers to a β-redex `(λ x:T. body) value`. Without `in`, `let`
    # stays a block statement (the enclosing block collects the following
    # statements), exactly as before.
    case peek(state) do
      %Token{type: :keyword, value: :in} ->
        state = advance(state)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)
        block = {:block, [line: token.line, col: token.col], [assignment, body]}
        {block, state}

      _ ->
        {assignment, state}
    end
  end

  defp expect_local_binding_assign(state, binding_token, pattern, annotation_span, kind, name) do
    case expect_token(state, :assign) do
      {:ok, assign, next_state} ->
        {assign, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :local_binding_assign_missing,
             family: kind,
             declaration: name,
             expected: :assign,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: binding_token.span,
             previous_span: annotation_span || first_node_source_span(pattern),
             pattern_span: first_node_source_span(pattern),
             annotation_span: annotation_span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp local_fact_ahead?(state) do
    case peek_at(state, 1) do
      %Token{type: type} when type in [:identifier, :quoted_identifier] -> true
      _ -> false
    end
  end

  # -- If / Elif / Else
  #
  # The legacy `if`/`elif` construct has been removed by the v1.0.0
  # branching specs (PICKUP §17, MATCH §10). It is still parsed for
  # source migration purposes but every encounter emits a deprecation
  # event (`Cure.Pipeline.Events`, payload `:if_deprecated`) so editors,
  # the LSP, and `mix cure.rewrite` can surface the migration hint. The
  # spec-mandated diagnostic code `E-IF-REMOVED` is reserved by the
  # error catalogue but not yet emitted as a hard error.

  defp parse_if(state) do
    token = peek(state)
    state = advance(state)
    state = emit_if_deprecation(state, token)

    # Parse condition
    {condition, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Inline form: if cond then a else b
    # Block form: if cond <newline> <indent> ... <dedent> [elif ...] [else ...]
    case peek(state) do
      %Token{type: :keyword, value: :then} ->
        then_token = peek(state)
        state = advance(state)
        {then_branch, state} = parse_expr(state, 0)

        {else_branch, else_token, state} =
          case peek(state) do
            %Token{type: :keyword, value: :else} = else_token ->
              state = advance(state)
              {else_branch, state} = parse_expr(state, 0)
              {else_branch, else_token, state}

            _ ->
              {{:literal, [subtype: :null], nil}, nil, state}
          end

        meta =
          put_conditional_source_info(
            [line: token.line, col: token.col],
            token,
            condition,
            then_branch,
            else_branch,
            then_token,
            else_token
          )

        ast = {:conditional, meta, [condition, then_branch, else_branch]}
        {ast, state}

      _ ->
        # Block form
        {then_branch, state} = parse_block(state)

        state = skip_newlines(state)

        {else_branch, else_token, state} =
          case peek(state) do
            %Token{type: :keyword, value: :elif} = elif_token ->
              # Desugar elif to nested conditional
              {else_branch, state} = parse_if(state)
              {else_branch, elif_token, state}

            %Token{type: :keyword, value: :else} = else_token ->
              state = advance(state)
              state = skip_newlines(state)
              {else_branch, state} = parse_block(state)
              {else_branch, else_token, state}

            _ ->
              {{:literal, [subtype: :null], nil}, nil, state}
          end

        meta =
          put_conditional_source_info(
            [line: token.line, col: token.col],
            token,
            condition,
            then_branch,
            else_branch,
            nil,
            else_token
          )

        ast = {:conditional, meta, [condition, then_branch, else_branch]}
        {ast, state}
    end
  end

  # -- Match Expression ------------------------------------------------------

  defp parse_match(state) do
    token = peek(state)
    state = advance(state)

    # Parse scrutinee
    {scrutinee, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Inline form: match x { pat -> body, ... }
    # Block form: match x <newline> <indent> arms <dedent>
    case peek(state) do
      %Token{type: :lbrace} = open_token ->
        state = advance(state)
        {arms, state} = parse_inline_match_arms(state)

        {state, _close_token} =
          expect_container_close(state, :rbrace, :branch_block, open_token, arms, false, %{family: :match})

        meta = put_match_source_info([line: token.line, col: token.col], token, scrutinee, arms, state)
        ast = {:pattern_match, meta, [scrutinee | arms]}
        {ast, state}

      %Token{type: :indent} ->
        state = advance(state)
        {arms, state} = parse_block_match_arms(state)
        state = expect_dedent(state)
        meta = put_match_source_info([line: token.line, col: token.col], token, scrutinee, arms, state)
        ast = {:pattern_match, meta, [scrutinee | arms]}
        {ast, state}

      _ ->
        meta = put_match_source_info([line: token.line, col: token.col], token, scrutinee, [], state)
        ast = {:pattern_match, meta, [scrutinee]}
        {ast, state}
    end
  end

  # -- With-abstraction (capability A) ---------------------------------------
  #
  # `with <expr>` matches on an intermediate expression and refines the GOAL by
  # the scrutinee's VALUE (not just its type indices) — what plain `match`
  # cannot do. Mirrors `parse_match/1` and reuses its arm parsers, producing a
  # distinct `{:with_abs, meta, [scrut | arms]}` node the dependent elaborator
  # dispatches on. Only capability A (single scrutinee, block/inline form) is
  # parsed; the `proof` clause and multiple with-expressions are out of scope.
  defp parse_with_abs(state, token) do
    state = advance(state)

    {scrutinee, state} = parse_expr(state, 0)
    # Multiple with-scrutinees (Idris `foo a b with (g a) | (g b)`) are written
    # space-separated in Cure surface syntax: `with g(a) g(b)`. Juxtaposition is
    # not application here (`g(a) g(b)` parses as two exprs because `parse_expr`
    # stops at the second callee), so we simply keep pulling scrutinees while the
    # next token can begin one. A single scrutinee leaves `scruts == [scrutinee]`
    # and the legacy path below is taken byte-for-byte unchanged.
    {scruts, state} = collect_with_scrutinees([scrutinee], state)
    # Optional `proof <ident>` (capability B): binds the scrutinee equation
    # `Eq(T, e, pat)` in each branch. `proof` is a soft keyword recognised only
    # in this slot; elsewhere it stays an ordinary identifier.
    {proof, proof_source, state} = parse_optional_with_proof(state)
    state = skip_newlines(state)

    base_meta = [line: token.line, col: token.col]
    meta = if proof, do: Keyword.put(base_meta, :proof, proof), else: base_meta

    case scruts do
      [single] ->
        case peek(state) do
          %Token{type: :lbrace} = open_token ->
            state = advance(state)
            {arms, state} = parse_inline_match_arms(state)

            {state, _close_token} =
              expect_container_close(state, :rbrace, :branch_block, open_token, arms, false, %{family: :with})

            meta = put_match_source_info(meta, token, single, arms, state)
            ast = {:with_abs, meta, [single | arms]}
            {put_with_proof_source_info(ast, proof_source), state}

          %Token{type: :indent} ->
            state = advance(state)
            {arms, state} = parse_with_block_arms(state)
            state = expect_dedent(state)
            meta = put_match_source_info(meta, token, single, arms, state)
            ast = {:with_abs, meta, [single | arms]}
            {put_with_proof_source_info(ast, proof_source), state}

          _ ->
            meta = put_match_source_info(meta, token, single, [], state)
            ast = {:with_abs, meta, [single]}
            {put_with_proof_source_info(ast, proof_source), state}
        end

      _ ->
        {ast, state} = parse_multi_with_abs(scruts, proof, base_meta, token, state)
        {put_with_proof_source_info(ast, proof_source), state}
    end
  end

  # Pull the second and subsequent space-separated with-scrutinees. Each call
  # peeks the current token: if it can start an expression we parse one more
  # scrutinee and recurse; otherwise we stop. `proof`/`:newline`/`:indent`/
  # `:lbrace` are not expression starters, so they terminate the scrutinee list.
  defp collect_with_scrutinees(acc, state) do
    if with_scrutinee_start?(peek(state)) do
      {expr, state} = parse_expr(state, 0)
      collect_with_scrutinees(acc ++ [expr], state)
    else
      {acc, state}
    end
  end

  # `proof` is the contextual with-proof keyword (it lexes as an identifier since
  # 408d3049). It terminates the scrutinee list so `parse_optional_with_proof`
  # can claim `proof <ident>`; without this, multi-with collection eats it.
  defp with_scrutinee_start?(%Token{type: :identifier, value: "proof"}), do: false

  defp with_scrutinee_start?(%Token{type: type})
       when type in [
              :identifier,
              :integer,
              :float,
              :string,
              :bool,
              :atom,
              :char,
              :lparen,
              :lbracket,
              :tuple_open,
              :map_open,
              :binary_open
            ],
       do: true

  defp with_scrutinee_start?(_), do: false

  # Multiple-with surface sugar. `with e1 e2 … eN` with arms
  # `p1, p2, …, pN -> body` desugars to nested single-scrutinee `:with_abs`
  # nodes so the dependent elaborator's existing (single-scrutinee) handling
  # covers it unchanged — this parser produces exactly the `{:with_abs, meta,
  # [scrut | arms]}` shape it already dispatches on. Combining an LHS re-match
  # (`| pat`) or a `proof` binding with multiple scrutinees is out of scope in
  # this first slice and is reported as a clean parse error.
  defp parse_multi_with_abs(scruts, proof, base_meta, token, state) do
    n = length(scruts)

    {arms, state} =
      case peek(state) do
        %Token{type: :lbrace} = open_token ->
          state = advance(state)
          {arms, state} = parse_multi_with_inline_arms(state, n)

          {state, _close_token} =
            expect_container_close(state, :rbrace, :branch_block, open_token, arms, false, %{
              family: :multi_with,
              previous_span: arms |> List.last() |> multi_with_arm_span()
            })

          {arms, state}

        %Token{type: :indent} ->
          state = advance(state)
          {arms, state} = parse_multi_with_block_arms(state, n)
          state = expect_dedent(state)
          {arms, state}

        _ ->
          {[], state}
      end

    authored_terminal = arms |> List.last() |> multi_with_arm_span()

    cond do
      proof != nil ->
        state =
          add_error(
            state,
            {:with_multi_proof_unsupported, "`proof` binding is not supported together with multiple with-scrutinees",
             base_meta}
          )

        {ast, state} = {{:with_abs, base_meta, [hd(scruts)]}, state}
        {put_multi_with_source_info(ast, token, state, authored_terminal), state}

      arms == [] ->
        state =
          add_error(
            state,
            {:with_multi_no_arms, "with-abstraction over multiple scrutinees requires at least one arm", base_meta}
          )

        {ast, state} = {{:with_abs, base_meta, [hd(scruts)]}, state}
        {put_multi_with_source_info(ast, token, state, authored_terminal), state}

      true ->
        {ast, state} = build_multi_with(scruts, arms, base_meta, state)
        {put_multi_with_source_info(ast, token, state, authored_terminal), state}
    end
  end

  defp put_multi_with_source_info({:with_abs, meta, [scrutinee | _] = children}, token, state, terminal_span) do
    arms = Enum.drop(children, 1)
    meta = put_match_source_info(meta, token, scrutinee, arms, state, terminal_span)
    {:with_abs, meta, children}
  end

  # Block-form arms for a multiple-with. Each arm is a list of `n` comma-
  # separated patterns and a body; results are `{patterns, body}` tuples that
  # `build_multi_with/4` later desugars.
  defp parse_multi_with_block_arms(state, n) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_multi_with_arm(state, n)
        state = skip_newlines(state)
        {rest, state} = parse_multi_with_block_arms(state, n)
        {[arm | rest], state}
    end
  end

  # Inline (`{ … }`) form. Arms are separated by `,`; the pattern commas within
  # an arm are consumed by `parse_comma_pattern_list/1`, which stops at the `->`.
  defp parse_multi_with_inline_arms(state, n) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {[], state}

      _ ->
        {arm, state} = parse_multi_with_arm(state, n)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_multi_with_inline_arms(state, n)
            {[arm | rest], state}

          _ ->
            {[arm], state}
        end
    end
  end

  # A single multiple-with arm: `p1, …, pk -> body`. A trailing `| pat` marks the
  # rematch form, which is out of scope combined with multiple-with; a pattern
  # count other than `n` is an arity error. Both are reported but recovery still
  # consumes through the body so parsing continues.
  defp parse_multi_with_arm(state, n) do
    {patterns, state} = parse_comma_pattern_list(state)

    {patterns, state} =
      case peek(state) do
        %Token{type: :bar} ->
          state =
            add_error(
              state,
              {:with_multi_rematch_unsupported,
               "LHS re-match (`| pat`) combined with multiple with-scrutinees is not supported", []}
            )

          # Recover: consume the `| with-pattern` remainder before the body.
          state = advance(state)
          state = skip_newlines(state)
          {_wp, state} = parse_expr(state, 0)
          {patterns, state}

        _ ->
          {patterns, state}
      end

    state =
      if length(patterns) != n do
        add_error(
          state,
          {:with_multi_arity_mismatch, "with-arm has #{length(patterns)} pattern(s) but there are #{n} with-scrutinees",
           []}
        )
      else
        state
      end

    state = skip_newlines(state)
    state = expect_branch_arrow(state, :with_arm, List.last(patterns))
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)
    {{patterns, body}, state}
  end

  defp multi_with_arm_span({patterns, body}) do
    first = patterns |> List.first() |> first_node_source_span()
    last = first_node_source_span(body)

    case Range.through(first, last) do
      {:ok, span} -> span
      _ -> last || first
    end
  end

  defp multi_with_arm_span(_), do: nil

  # Comma-separated pattern list for one multiple-with arm. A top-level `,` never
  # occurs inside a single pattern (tuples are parenthesised), so it reliably
  # separates the per-scrutinee patterns; parsing stops at the first non-comma
  # (the `->`, or a `|` handled by the caller).
  defp parse_comma_pattern_list(state) do
    {first, state} = parse_expr(state, 0)
    {first, state} = maybe_wrap_as(first, state)
    parse_comma_pattern_list([first], state)
  end

  defp parse_comma_pattern_list(acc, state) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {pat, state} = parse_expr(state, 0)
        {pat, state} = maybe_wrap_as(pat, state)
        parse_comma_pattern_list(acc ++ [pat], state)

      _ ->
        {acc, state}
    end
  end

  # Desugar `n` scrutinees + `{patterns, body}` arms into nested single-scrutinee
  # `:with_abs` nodes. Base case (one scrutinee left): a flat `:with_abs` whose
  # arms are ordinary `{:match_arm, [pattern: p], [body]}`. Recursive case: group
  # arms by their FIRST pattern (structural equality, first-appearance order) and
  # emit one outer `{:match_arm, [pattern: p1], [inner]}` per group, where `inner`
  # is the desugar of the remaining scrutinees over that group's arms with their
  # first pattern stripped.
  defp build_multi_with([last], arms, meta, state) do
    match_arms =
      Enum.map(arms, fn {[p], body} -> {:match_arm, [pattern: p], [body]} end)

    {{:with_abs, meta, [last | match_arms]}, state}
  end

  defp build_multi_with([s | rest], arms, meta, state) do
    groups = group_arms_by_first(arms)
    state = check_group_head_consistency(groups, meta, state)

    {outer_arms, state} =
      Enum.map_reduce(groups, state, fn {p1, sub_arms}, st ->
        {inner, st} = build_multi_with(rest, sub_arms, meta, st)
        {{:match_arm, [pattern: p1], [inner]}, st}
      end)

    {{:with_abs, meta, [s | outer_arms]}, state}
  end

  # Group arms by their first pattern using structural equality that ignores
  # positional metadata (line/col), so e.g. two `S(j)` arms on different lines
  # share one outer branch. Preserves first-appearance order. Each group's
  # sub-arms have the grouped-on first pattern removed.
  defp group_arms_by_first(arms) do
    Enum.reduce(arms, [], fn {[p1 | rest_pats], body}, groups ->
      key = Metadata.semantic_key(p1)

      case Enum.find_index(groups, fn {gp, _} -> Metadata.semantic_key(gp) == key end) do
        nil ->
          groups ++ [{p1, [{rest_pats, body}]}]

        idx ->
          {gp, subs} = Enum.at(groups, idx)
          List.replace_at(groups, idx, {gp, subs ++ [{rest_pats, body}]})
      end
    end)
  end

  # First-slice consistency guard. Because groups are keyed by structural
  # equality, two distinct groups sharing one constructor head can only differ in
  # their sub-patterns/variable names — sharing an outer branch would require
  # renaming, which this slice does not do. Reject rather than risk mis-binding.
  defp check_group_head_consistency(groups, meta, state) do
    ctor_heads =
      groups
      |> Enum.map(fn {p1, _} -> pattern_ctor_head(p1) end)
      |> Enum.filter(&match?({:ctor, _}, &1))

    if length(Enum.uniq(ctor_heads)) == length(ctor_heads) do
      state
    else
      add_error(
        state,
        {:with_multi_inconsistent_pattern,
         "multiple-with arms share a constructor head with differing sub-patterns; this first " <>
           "slice requires structurally identical outer patterns (rename to a common form)", meta}
      )
    end
  end

  defp pattern_ctor_head({:function_call, meta, _args}), do: {:ctor, Keyword.get(meta, :name)}
  defp pattern_ctor_head(_), do: :other

  # Block-form with-clause arms. Distinct from `parse_block_match_arms` (used by
  # plain `match`) because a with-clause arm may RESTATE the parent LHS patterns
  # before the with-pattern — the Idris-parity LHS re-match form. Each arm is
  # either the ordinary `{:match_arm, …}` (no `… |` prefix) or the new
  # `{:with_rematch_arm, …}` (parent patterns `|` with-pattern).
  defp parse_with_block_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_with_clause_arm(state)
        state = skip_newlines(state)
        {rest, state} = parse_with_block_arms(state)
        {[arm | rest], state}
    end
  end

  # A single with-clause arm. Parse the first pattern, then disambiguate by the
  # following token (only in this with-clause-LHS position):
  #   - `|`      → rematch arm restating one parent pattern
  #   - `,` … `|`→ rematch arm restating several (comma-separated) parent patterns
  #   - anything → ordinary `{:match_arm}` (the existing no-rematch form)
  # A top-level `,` before `->` never occurs in a plain arm pattern (tuples are
  # parenthesised), so it unambiguously signals a multi-pattern rematch here.
  defp parse_with_clause_arm(state) do
    {first, state} = parse_expr(state, 0)

    case peek(state) do
      %Token{type: :bar} ->
        finish_with_rematch_arm([first], state)

      %Token{type: :comma} ->
        {parent_patterns, state} = parse_more_parent_patterns([first], state)
        finish_with_rematch_arm(parent_patterns, state)

      _ ->
        parse_match_arm_tail(first, state)
    end
  end

  # Collect the remaining comma-separated parent patterns (the first is already
  # parsed). Stops at the `|` separator (consumed by `finish_with_rematch_arm`).
  defp parse_more_parent_patterns(acc, state) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {pat, state} = parse_expr(state, 0)
        parse_more_parent_patterns(acc ++ [pat], state)

      _ ->
        {acc, state}
    end
  end

  # After the parent patterns: consume `|`, parse the with-pattern, then the
  # `->` body. Guards and `impossible` in rematch arms are deferred (out of the
  # faithful first slice). Produces `{:with_rematch_arm, meta, [body]}` with the
  # restated `:parent_patterns` and the with-`:pattern` in meta.
  defp finish_with_rematch_arm(parent_patterns, state) do
    separator_token = if match?(%Token{type: :bar}, peek(state)), do: peek(state)
    state = expect_with_rematch_separator(state, parent_patterns)
    state = skip_newlines(state)
    {with_pattern, state} = parse_expr(state, 0)
    state = skip_newlines(state)
    arrow_token = if match?(%Token{type: :arrow}, peek(state)), do: peek(state)
    state = expect_branch_arrow(state, :with_rematch_arm, with_pattern)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    parent_spans = Enum.map(parent_patterns, &first_node_source_span/1) |> Enum.reject(&is_nil/1)
    pattern_span = first_node_source_span(with_pattern)
    body_span = first_node_source_span(body)
    first_span = List.first(parent_spans) || pattern_span
    whole = through_spans(first_span, body_span || pattern_span || List.last(parent_spans))

    fields =
      %{}
      |> maybe_put_source_field(:rematch_separator, separator_token)

    meta =
      [parent_patterns: parent_patterns, pattern: with_pattern]
      |> Metadata.put_source_info(%SourceInfo{
        whole: whole,
        operator: arrow_token && arrow_token.span,
        operands: parent_spans,
        pattern: pattern_span,
        body: body_span,
        fields: fields
      })

    {{:with_rematch_arm, meta, [body]}, state}
  end

  defp expect_with_rematch_separator(state, parent_patterns) do
    case expect_token(state, :bar) do
      {:ok, _bar, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :with_rematch_separator_missing,
             expected: :bar,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: parent_patterns |> List.first() |> first_node_source_span(),
             previous_span: parent_patterns |> List.last() |> first_node_source_span(),
             parent_pattern_count: length(parent_patterns),
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # `proof <ident>` after a with-scrutinee. Returns the semantic name and the
  # exact token-owned clause roles when present, leaving the stream untouched
  # otherwise.
  defp parse_optional_with_proof(state) do
    case peek(state) do
      %Token{type: type, value: value} = proof_token
      when (type == :keyword and value == :proof) or (type == :identifier and value == "proof") ->
        case peek_at(state, 1) do
          %Token{type: :identifier, value: name} = name_token ->
            source = %{
              whole: through_spans(proof_token.span, name_token.span),
              keyword: proof_token.span,
              name: name_token.span
            }

            {name, source, state |> advance() |> advance()}

          _ ->
            {nil, nil, state}
        end

      _ ->
        {nil, nil, state}
    end
  end

  defp put_with_proof_source_info(ast, nil), do: ast

  defp put_with_proof_source_info({:with_abs, meta, children}, source) do
    case Metadata.source_info(meta) do
      %SourceInfo{} = info ->
        fields =
          info.fields
          |> Map.put(:proof_clause, source.whole)
          |> Map.put(:proof_keyword, source.keyword)
          |> Map.put(:proof_name, source.name)

        {:with_abs, Metadata.put_source_info(meta, %{info | fields: fields}), children}

      _ ->
        {:with_abs, meta, children}
    end
  end

  # True iff the token after `with` can begin a scrutinee expression. Keeps
  # `with` an ordinary identifier when it is a bare operand (`with + 1`, a
  # trailing `with`, etc.), so the contextual keyword never captures a value
  # named `with`.
  defp with_scrutinee_ahead?(state) do
    case peek_at(state, 1) do
      %Token{type: type}
      when type in [
             :identifier,
             :integer,
             :float,
             :string,
             :bool,
             :atom,
             :char,
             :lparen,
             :lbracket,
             :tuple_open,
             :map_open,
             :binary_open
           ] ->
        true

      _ ->
        false
    end
  end

  defp parse_inline_match_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {[], state}

      _ ->
        {arm, state} = parse_match_arm(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_inline_match_arms(state)
            {[arm | rest], state}

          _ ->
            {[arm], state}
        end
    end
  end

  defp parse_block_match_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_match_arm(state)
        state = skip_newlines(state)
        {rest, state} = parse_block_match_arms(state)
        {[arm | rest], state}
    end
  end

  defp parse_match_arm(state) do
    # Parse pattern
    {pattern, state} = parse_expr(state, 0)
    {pattern, state} = maybe_wrap_as(pattern, state)
    parse_match_arm_tail(pattern, state)
  end

  # As-pattern: `name @ <pattern>` binds the whole matched value to `name` in
  # addition to destructuring it. `@` (`:at`) is a decorator prefix only at
  # declaration position, so in value/pattern position it is unambiguously an
  # as-binding. Used both at a match arm's top level and inside constructor
  # arguments (`Cons(h, t @ Cons(x, y))`), so as-patterns nest.
  defp maybe_wrap_as({:variable, vm, name}, state) do
    case peek(state) do
      # A TYPED pattern: `n: Int`. Binds `name` at the annotated type — the
      # elimination form for anonymous unions (`match x { n: Int -> … }`). The
      # annotation may itself be a union (`rest: String | Bool`), which is why it
      # goes through the `|`-aware parse_type_expr/1.
      #
      # `:colon` has no infix binding power, so parse_expr(state, 0) already stops
      # cleanly here — this clause is purely additive.
      #
      # Brace-delimited record/map patterns are NOT covered: parse_map_pair/1's
      # explicit key:value branch already claims `identifier :` inside braces.
      %Token{type: :colon} ->
        state = advance(state)
        {type_ast, state} = parse_pattern_type(state)
        {{:typed_pattern, vm, [name, type_ast]}, state}

      %Token{type: :at} ->
        state = advance(state)
        {inner, state} = parse_expr(state, 0)
        {inner, state} = maybe_wrap_as(inner, state)
        {{:as_pattern, vm, [name, inner]}, state}

      _ ->
        {{:variable, vm, name}, state}
    end
  end

  defp maybe_wrap_as(pattern, state), do: {pattern, state}

  # The type annotation of a typed pattern (`n: Int`, `rest: String | Bool`).
  #
  # This is NOT `parse_type_expr/1`, and the difference is load-bearing. A match
  # arm is `pattern -> body`, and `parse_match_arm_tail/2` expects that `->`. But
  # `parse_type_arrow/1` is greedy: given `n: Int -> 1` it would read `Int -> 1` as
  # a FUNCTION TYPE, swallow the arm's arrow, and parse the body `1` as a codomain.
  # So a pattern annotation must not absorb a top-level `->`.
  #
  # Members are therefore parsed with `parse_type_atom/1` (`Name`, `Name(args)`,
  # `(T)`), which never consumes an arrow — the same restricted type grammar GADT
  # constructor signatures use. A function-typed annotation is consequently not
  # expressible here; that is out of scope (union members must be ground types).
  defp parse_pattern_type(state) do
    {first, state} = parse_pattern_type_member(state)
    {rest, state} = parse_pattern_type_members(state)

    case rest do
      [] -> {first, state}
      _ -> {{:union_type, [], [first | rest]}, state}
    end
  end

  defp parse_pattern_type_members(state) do
    case peek(state) do
      %Token{type: :bar} ->
        state = advance(state) |> skip_newlines()
        {member, state} = parse_pattern_type_member(state)
        {rest, state} = parse_pattern_type_members(state)
        {[member | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_pattern_type_member(state) do
    token = peek(state)

    if literal_token?(token) do
      {literal(literal_subtype(token.type), token), advance(state)}
    else
      # `parse_type_atom/1` alone stops at a bare `Name`/`Name(args)` and does not
      # know about `.` — so a QUALIFIED member (`n: Std.Nat.Nat`) failed with a hard
      # parse error (the `.` was left for `parse_match_arm_tail/2`, which expects
      # `->` and got `:dot` instead), even though the exact same qualified name
      # parses fine in ordinary parameter/return position via `parse_type_arrow/1`
      # (`maybe_parse_type_projection/2`). Chain the SAME dot-projection logic here
      # — deliberately NOT `maybe_parse_type_projection/2` itself, whose
      # `Mod.Name(args)` branch also calls `maybe_parse_function_type/2` and would
      # reintroduce exactly the arrow-swallowing hazard `parse_type_atom` was
      # chosen to avoid (`n: Std.List.List(Int) -> 1` would otherwise absorb the
      # arm's own `->` as a second application layer).
      {atom, state} = parse_type_atom(state)
      parse_pattern_type_projection(atom, state)
    end
  end

  # As `maybe_parse_type_projection/2`, but stops at the qualified application —
  # no `maybe_parse_function_type/2` call — so a pattern annotation never absorbs
  # the arm's `->`. See `parse_pattern_type_member/1`.
  defp parse_pattern_type_projection(inner, state) do
    case peek(state) do
      %Token{type: :dot} ->
        state = advance(state)
        attr_token = peek(state)
        attr = to_string(attr_token.value)
        state = advance(state)
        node = {:attribute_access, [attribute: attr], [inner]}
        parse_pattern_type_projection(node, state)

      %Token{type: :lparen} ->
        case qualified_type_name(inner) do
          {:ok, name} ->
            open_token = peek(state)
            state = advance(state)
            {params, state} = parse_type_atom_args(state)

            {state, _close_token} =
              expect_container_close(state, :rparen, :type_arguments, open_token, params, true, %{type: name})

            {{:function_call, [name: name, qualified: true], params}, state}

          :error ->
            {inner, state}
        end

      _ ->
        {inner, state}
    end
  end

  # The tail of a match arm after its pattern has been parsed: optional `when`
  # guard, the `->`, and the body (or `impossible`). Factored out so with-clause
  # arms can fall through to it once they have decided they are NOT a rematch arm
  # (see `parse_with_clause_arm`).
  defp expect_branch_arrow(state, family, previous) do
    {_arrow, state} = expect_branch_arrow_token(state, family, previous)
    state
  end

  defp expect_branch_arrow_token(state, family, previous) do
    case expect_token(state, :arrow) do
      {:ok, arrow, next_state} ->
        {arrow, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        previous_span =
          case previous do
            %Cure.Diagnostic.Span{} = span -> span
            node -> first_node_source_span(node)
          end

        error =
          {:branch_arrow_missing,
           %{
             family: family,
             expected: :arrow,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             previous_span: previous_span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp parse_match_arm_tail(pattern, state) do
    state = skip_newlines(state)

    # Optional guard: when expr
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    # Expect ->
    {arrow_token, state} = expect_branch_arrow_token(state, :match_arm, guard || pattern)
    state = skip_newlines(state)

    # `impossible` is a soft keyword recognized only as an entire arm body
    # (spec §4): `pat -> impossible`. Any other use stays an ordinary identifier.
    if impossible_body?(state) do
      impossible_token = peek(state)
      state = advance(state)

      meta =
        if guard, do: [pattern: pattern, guard: guard, impossible: true], else: [pattern: pattern, impossible: true]

      meta = put_match_arm_source_info(meta, pattern, guard, arrow_token, impossible_token.span)

      {{:match_arm, meta, [nil]}, state}
    else
      {body, state} = parse_expr_or_block(state)
      meta = if guard, do: [pattern: pattern, guard: guard], else: [pattern: pattern]
      meta = put_match_arm_source_info(meta, pattern, guard, arrow_token, ast_source_span(body))
      {{:match_arm, meta, [body]}, state}
    end
  end

  defp put_match_arm_source_info(meta, pattern, guard, arrow_token, body_span) do
    pattern_span = first_node_source_span(pattern)
    guard_span = first_node_source_span(guard)
    whole = through_spans(pattern_span, body_span)

    if whole do
      Metadata.put_source_info(meta, %SourceInfo{
        whole: whole,
        operator: arrow_token && arrow_token.span,
        pattern: pattern_span,
        guard: guard_span,
        body: body_span
      })
    else
      meta
    end
  end

  defp put_match_source_info(meta, match_token, scrutinee, arms, state, terminal_span \\ nil)

  defp put_match_source_info(meta, match_token, scrutinee, arms, _state, terminal_span) do
    match_span = if match_token.span, do: match_token.span, else: nil
    scrutinee_span = first_node_source_span(scrutinee)

    branch_spans =
      arms
      |> Enum.map(&match_arm_source_span/1)
      |> Enum.reject(&is_nil/1)

    terminal_span = terminal_span || List.last(branch_spans) || scrutinee_span
    whole = through_spans(match_span || scrutinee_span, terminal_span)

    if whole || branch_spans != [] do
      Metadata.put_source_info(meta, %SourceInfo{
        whole: whole,
        opener: match_span,
        operands: Enum.filter([scrutinee_span], & &1),
        branches: branch_spans
      })
    else
      meta
    end
  end

  defp match_arm_source_span({:match_arm, arm_meta, _}) when is_list(arm_meta) do
    case first_node_source_span({:match_arm, arm_meta, []}) do
      nil -> first_node_source_span(Keyword.get(arm_meta, :pattern))
      span -> span
    end
  end

  defp match_arm_source_span(arm), do: first_node_source_span(arm)

  defp put_conditional_source_info(meta, if_token, condition, then_branch, else_branch, then_token, else_token) do
    condition_span = first_node_source_span(condition)
    then_span = first_node_source_span(then_branch)
    else_span = first_node_source_span(else_branch)

    whole = through_spans(if_token.span, else_span || then_span || condition_span)

    fields =
      %{}
      |> maybe_put_source_field(:then_keyword, then_token)
      |> maybe_put_source_field(:else_keyword, else_token)

    if whole || condition_span || then_span || else_span do
      Metadata.put_source_info(
        meta,
        %SourceInfo{
          whole: whole,
          opener: if_token.span,
          condition: condition_span,
          then_branch: then_span,
          else_branch: else_span,
          fields: fields
        }
      )
    else
      meta
    end
  end

  defp maybe_put_source_field(fields, _role, nil), do: fields
  defp maybe_put_source_field(fields, role, %Token{span: span}), do: Map.put(fields, role, span)
  defp maybe_put_source_field(fields, role, %Cure.Diagnostic.Span{} = span), do: Map.put(fields, role, span)

  defp first_node_source_span(node) do
    case node_source_span(node) do
      [span | _] -> span
      _ -> nil
    end
  end

  # True iff the next token is the identifier `impossible` AND the token after it
  # ends the arm — so `impossible` alone is the body, but `impossible + 1` is not.
  defp impossible_body?(state) do
    case peek(state) do
      %Token{type: :identifier, value: "impossible"} ->
        case peek_at(state, 1) do
          %Token{type: type} when type in [:newline, :comma, :rbrace, :dedent, :eof] -> true
          nil -> true
          _ -> false
        end

      _ ->
        false
    end
  end

  # -- Pickup Expression -----------------------------------------------------
  #
  # `pickup` is the predicate-dispatch counterpart to `match` (see
  # `docs/PICKUP.md`). Grammar (PICKUP §4):
  #
  #   pickup_expr     ::= "pickup" NEWLINE INDENT clause_list DEDENT
  #   clause_list     ::= guard_clause { NEWLINE guard_clause } NEWLINE
  #                       terminal_clause [ NEWLINE ]
  #                     | terminal_clause [ NEWLINE ]
  #   guard_clause    ::= expression "->" expression
  #   terminal_clause ::= "else" "->" expression
  #                     | "true" "->" expression
  #
  # The AST shape is `{:pickup, meta, clauses}` where each clause is
  # either `{:pickup_clause, meta, [guard, body]}` (a guard clause) or
  # `{:pickup_else, meta, [body]}` (the mandatory terminator). The parser
  # itself enforces the well-formedness rules of PICKUP §5.2 and §4.1
  # (non-empty block, single terminator, terminator-last) so downstream
  # stages can rely on the structural shape; spec-mandated diagnostic
  # codes are surfaced with the same `add_error/2` channel the rest of
  # the parser uses.

  defp parse_pickup(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {clauses, state} = parse_pickup_clauses(state)
          state = expect_dedent(state)
          {clauses, state}

        _ ->
          # Inline form is not part of the spec, but we accept a
          # single-line `pickup else -> expr` so REPL one-liners still
          # parse. The well-formedness pass below will still catch a
          # missing terminator. `parse_pickup_inline/1` already wraps
          # the single clause in a list so the calling shape matches
          # the indented case below.
          parse_pickup_inline(state)
      end

    state = validate_pickup_clauses(clauses, token, state)

    branches = clauses |> Enum.map(&pickup_clause_span/1) |> Enum.reject(&is_nil/1)

    meta =
      Metadata.put_source_info([line: token.line, col: token.col], %SourceInfo{
        whole: through_spans(token.span, List.last(branches)) || token.span,
        opener: token.span,
        branches: branches
      })

    {{:pickup, meta, clauses}, state}
  end

  defp parse_pickup_inline(state) do
    {clause, state} = parse_pickup_clause(state)
    {[clause], state}
  end

  defp parse_pickup_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {clause, state} = parse_pickup_clause(state)
        state = skip_newlines(state)
        {rest, state} = parse_pickup_clauses(state)
        {[clause | rest], state}
    end
  end

  defp parse_pickup_clause(state) do
    case peek(state) do
      %Token{type: :keyword, value: :else} = tok ->
        state = advance(state)
        {arrow_token, state} = expect_branch_arrow_token(state, :pickup_else, tok.span)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)

        meta =
          put_pickup_clause_source_info(
            [line: tok.line, col: tok.col],
            tok,
            nil,
            arrow_token,
            body
          )

        {{:pickup_else, meta, [body]}, state}

      tok ->
        {guard, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        {arrow_token, state} = expect_branch_arrow_token(state, :pickup_clause, guard)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)

        meta =
          put_pickup_clause_source_info(
            [line: tok.line, col: tok.col],
            tok,
            guard,
            arrow_token,
            body
          )

        {{:pickup_clause, meta, [guard, body]}, state}
    end
  end

  defp put_pickup_clause_source_info(meta, token, guard, arrow_token, body) do
    body_span = first_node_source_span(body)

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(token.span, body_span) || token.span,
      name: token.span,
      operator: arrow_token && arrow_token.span,
      condition: first_node_source_span(guard),
      body: body_span
    })
  end

  # PICKUP §5.2 / §4.1 enforcement. The four well-formedness errors
  # carried here (E-PICKUP-NO-ELSE, E-PICKUP-ELSE-NOT-LAST,
  # E-PICKUP-MULTIPLE-ELSE, and the empty-body case) are raised at the
  # parser tier so a malformed `pickup` never leaks into the type checker
  # or codegen.
  defp validate_pickup_clauses([], token, state) do
    add_error(
      state,
      {:pickup_no_else, %{pickup: token.span, clauses: [], line: token.line, column: token.col}}
    )
  end

  defp validate_pickup_clauses(clauses, token, state) do
    indexed = Enum.with_index(clauses)
    else_clauses = Enum.filter(indexed, fn {clause, _idx} -> pickup_else?(clause) end)
    terminator_index = Enum.find_index(clauses, &pickup_terminator?(&1, false))
    last_index = length(clauses) - 1
    trailing_true? = pickup_terminator?(List.last(clauses), true)
    has_terminator? = else_clauses != [] or trailing_true?

    details = %{
      pickup: token.span,
      clauses: Enum.map(clauses, &pickup_clause_span/1),
      else_clauses: Enum.map(else_clauses, fn {clause, idx} -> {idx, pickup_else_span(clause)} end),
      line: token.line,
      column: token.col
    }

    state =
      cond do
        length(else_clauses) > 1 ->
          add_error(state, {:pickup_multiple_else, details})

        is_integer(terminator_index) and terminator_index < last_index ->
          add_error(state, {:pickup_else_not_last, Map.put(details, :terminator_index, terminator_index)})

        not has_terminator? ->
          add_error(state, {:pickup_no_else, details})

        true ->
          state
      end

    state
  end

  defp pickup_else?({:pickup_else, _, _}), do: true
  defp pickup_else?(_), do: false

  defp pickup_clause_span({_, meta, _}) when is_list(meta) do
    meta |> Metadata.source_info() |> source_whole()
  end

  defp pickup_clause_span(_), do: nil

  defp pickup_else_span({:pickup_else, meta, _}) when is_list(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      %SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp pickup_else_span(_), do: nil

  defp pickup_terminator?({:pickup_else, _, _}, _is_last), do: true

  defp pickup_terminator?({:pickup_clause, _meta, [guard, _body]}, true) do
    # Trailing `true ->` is the alternative form admitted by PICKUP §5.2.
    case guard do
      {:literal, _, true} -> true
      _ -> false
    end
  end

  defp pickup_terminator?(_, _), do: false

  # -- fn: named function or lambda ------------------------------------------

  defp parse_fn_or_lambda(state) do
    token = peek(state)
    state = advance(state)

    # fn followed by ( -> lambda
    # fn followed by identifier or (soft) keyword -> named function definition
    #
    # Some Cure keywords (spawn, send, receive, after) are ordinary
    # function names in other languages, and standard-library modules may define
    # similarly named functions. Let those words double as
    # function-definition names; they still behave as keywords in
    # statement position.
    case peek(state) do
      %Token{type: :lparen} ->
        parse_lambda_body(state, token)

      %Token{type: :identifier} ->
        parse_fn_def(state, token, :public)

      %Token{type: :keyword} ->
        parse_fn_def(state, token, :public)

      _ ->
        parse_lambda_body(state, token)
    end
  end

  # local fn name(...) -> private function
  defp parse_local(state) do
    token = peek(state)
    state = advance(state)

    # Expect fn keyword next
    case peek(state) do
      %Token{type: :keyword, value: :fn} = function_token ->
        state = advance(state)
        # After `local fn`, a name (identifier or soft keyword) must follow.
        case peek(state) do
          %Token{type: type} when type in [:identifier, :keyword] ->
            {ast, state} = parse_fn_def(state, token, :private)
            {put_local_function_keyword(ast, function_token), state}

          _ ->
            parse_lambda_body(state, token)
        end

      _ ->
        observed = peek(state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :local_function_keyword_missing,
             expected: :fn,
             observed: macro_separator_observed(observed),
             token_type: observed.type,
             span: observed.span,
             opener_span: token.span,
             previous_span: token.span,
             line: observed.line,
             column: observed.col
           }}

        state = add_error(state, error)
        {error_node(token), state}
    end
  end

  defp put_local_function_keyword({:function_def, meta, body}, %Token{} = function_token) do
    case Metadata.source_info(meta) do
      %SourceInfo{} = info ->
        fields = maybe_put_source_field(info.fields, :function_keyword, function_token)
        {:function_def, Metadata.put_source_info(meta, %{info | fields: fields}), body}

      _ ->
        {:function_def, meta, body}
    end
  end

  # -- Named Function Definition ---------------------------------------------

  defp parse_fn_def(state, fn_token, visibility) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Parse parameter list. Keep ownership here so a missing `(` does not let
    # the generic parameter parser consume `->` or `=` as a parameter name and
    # blame a later token for the declaration's real mistake.
    {params, parameter_span, state} = parse_function_params(state, name, name_token)

    # Optional return type: -> Type
    {return_type, return_arrow_token, state} =
      case peek(state) do
        %Token{type: :arrow} = arrow_token ->
          state = advance(state)
          {return_type, state} = parse_type_expr(state)
          {return_type, arrow_token, state}

        _ ->
          {nil, nil, state}
      end

    # Optional effect annotation: ! Effect, Effect2
    {effects, effects_span, state} =
      case peek(state) do
        %Token{type: :bang} = bang_token ->
          state = advance(state)
          {effects, last_effect_token, state} = parse_effect_list(state)
          span = through_spans(bang_token.span, last_effect_token.span) || bang_token.span
          {effects, span, state}

        _ ->
          {nil, nil, state}
      end

    # Optional guard: when expr
    # Parse at BP 6 to stop before `=` (BP 5) so the guard doesn't consume the body
    {guard, guard_span, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} = when_token ->
          state = advance(state)
          {g, state} = parse_expr(state, bp_above(state, "="))
          span = through_spans(when_token.span, ast_source_span(g)) || when_token.span
          {g, span, state}

        _ ->
          {nil, nil, state}
      end

    # Optional interface requirements: `requires Proto(T), ...`. The former
    # constraint-position `where` remains a deprecated migration spelling;
    # declaration-local `where` is reserved for the post-body definition block.
    requirements_token = peek(state)
    {constraints, state} = parse_requirements_clause(state)

    requirements_span =
      case constraints |> List.last() |> ast_source_span() do
        %Cure.Diagnostic.Span{} = last -> through_spans(requirements_token.span, last)
        _ -> nil
      end

    state = skip_newlines(state)

    # Check for multi-clause form (indented | patterns) or = body
    case peek(state) do
      %Token{type: :assign} ->
        assign_token = peek(state)
        state = advance(state)
        {body, state} = parse_required_function_body(state, assign_token)

        {where_bindings, where_span, state} = parse_post_body_where(state)

        meta =
          build_fn_meta(
            fn_token,
            name_token,
            name,
            params,
            return_type,
            visibility,
            guard,
            constraints,
            effects,
            parameter_span,
            return_arrow_token,
            effects_span,
            guard_span,
            requirements_span
          )
          |> put_function_body_source_info(body, assign_token, where_span)

        meta = if where_bindings == [], do: meta, else: Keyword.put(meta, :where, where_bindings)
        ast = {:function_def, meta, [body]}
        {ast, state}

      %Token{type: :indent} ->
        state = advance(state)

        case peek(skip_newlines(state)) do
          %Token{type: :assign} ->
            state = skip_newlines(state)
            assign_token = peek(state)
            state = advance(state)
            {body, state} = parse_required_function_body(state, assign_token)
            state = expect_dedent(state)

            {where_bindings, where_span, state} = parse_post_body_where(state)

            meta =
              build_fn_meta(
                fn_token,
                name_token,
                name,
                params,
                return_type,
                visibility,
                guard,
                constraints,
                effects,
                parameter_span,
                return_arrow_token,
                effects_span,
                guard_span,
                requirements_span
              )
              |> put_function_body_source_info(body, assign_token, where_span)

            meta = if where_bindings == [], do: meta, else: Keyword.put(meta, :where, where_bindings)

            ast = {:function_def, meta, [body]}
            {ast, state}

          _ ->
            # Could be multi-clause: indented | pattern -> body lines
            {clauses, state} = parse_fn_clauses(state)
            state = expect_dedent(state)

            meta =
              build_fn_meta(
                fn_token,
                name_token,
                name,
                params,
                return_type,
                visibility,
                guard,
                constraints,
                effects,
                parameter_span,
                return_arrow_token,
                effects_span,
                guard_span,
                requirements_span
              )

            meta = Keyword.put(meta, :clauses, clauses)
            meta = put_function_clause_source_info(meta, clauses)
            ast = {:function_def, meta, []}
            {ast, state}
        end

      _ ->
        # Function signature only (no body, e.g. in protocol)
        meta =
          build_fn_meta(
            fn_token,
            name_token,
            name,
            params,
            return_type,
            visibility,
            guard,
            constraints,
            effects,
            parameter_span,
            return_arrow_token,
            effects_span,
            guard_span,
            requirements_span
          )

        ast = {:function_def, meta, []}
        {ast, state}
    end
  end

  defp parse_function_params(state, name, name_token) do
    case expect_token(state, :lparen) do
      {:ok, open, state} ->
        {params, state} = parse_typed_params(state)
        {state, close} = expect_container_close(state, :rparen, :parameters, open, params, true)
        span = through_spans(open.span, close && close.span) || open.span
        {params, span, state}

      {:error, state} ->
        # Replace the generic error emitted by expect_token/2 with a declaration-
        # specific problem while retaining the observed token's exact range.
        [_generic | rest] = state.errors
        observed = peek(state)

        error =
          {:function_parameters_unparenthesized,
           %{
             function: name,
             name_span: name_token.span,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: observed.span,
             line: observed.line,
             column: observed.col
           }}

        {[], nil, %{state | errors: [error | rest]}}
    end
  end

  defp parse_required_function_body(state, %Token{} = assign_token) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        missing_function_body(state, assign_token)

      %Token{type: :keyword, value: :end} ->
        missing_function_body(state, assign_token)

      _ ->
        {body, state} = parse_expr_or_block(state)
        parse_expression_let_chain_body(body, state)
    end
  end

  defp missing_function_body(state, %Token{} = assign_token) do
    error =
      {:missing_function_body,
       %{
         expected: :expression,
         observed: peek(state).type,
         span: assign_token.span,
         line: assign_token.line,
         column: assign_token.col
       }}

    {error_node(assign_token), add_error(state, error)}
  end

  # A function-local `where` follows the function body at the function's own
  # indentation.  It is kept as metadata and lowered by the dependent
  # elaborator before signatures are registered.
  defp parse_post_body_where(state) do
    probe = skip_newlines(state)

    case peek(probe) do
      %Token{type: :keyword, value: :where} ->
        where_token = peek(probe)
        probe = advance(probe) |> skip_newlines()

        case expect_where_block_indent(probe, where_token) do
          {:ok, probe} ->
            {bindings, probe} = parse_where_bindings(probe, [], where_token)
            bindings = Enum.reverse(bindings)
            terminal = bindings |> List.last() |> ast_source_span()
            span = through_spans(where_token.span, terminal) || where_token.span
            {bindings, span, expect_dedent(probe)}

          {:error, probe} ->
            {[], where_token.span, probe}
        end

      _ ->
        {[], nil, state}
    end
  end

  defp expect_where_block_indent(state, where_token) do
    case expect_token(state, :indent) do
      {:ok, _indent, next_state} ->
        {:ok, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :where_block_indent_missing,
             expected: :indent,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: observed.span,
             observed_span: observed.span,
             opener_span: where_token.span,
             line: observed.line,
             column: observed.col
           }}

        {:error, %{next_state | errors: [error | rest]}}
    end
  end

  defp parse_where_bindings(state, acc, where_token) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :dedent} ->
        {acc, state}

      %Token{type: :eof} ->
        {acc, state}

      %Token{type: :keyword, value: :fn} = token ->
        {binding, state} = parse_fn_def(advance(state), token, :private)
        parse_where_bindings(state, [binding | acc], where_token)

      %Token{type: :identifier} = token ->
        name = to_string(token.value)
        {assign_token, state} = expect_where_binding_assign(advance(state), where_token, token, name)
        state = skip_newlines(state)
        {expr, state} = parse_expr_or_block(state)

        meta =
          Metadata.put_source_info([name: name, line: token.line, col: token.col], %SourceInfo{
            whole: through_spans(token.span, ast_source_span(expr)) || token.span,
            name: token.span,
            operator: assign_token && assign_token.span,
            body: ast_source_span(expr)
          })

        binding = {:where_value, meta, expr}
        parse_where_bindings(state, [binding | acc], where_token)

      _ ->
        {acc, state}
    end
  end

  defp expect_where_binding_assign(state, where_token, name_token, name) do
    case expect_token(state, :assign) do
      {:ok, assign, next_state} ->
        {assign, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :where_binding_assign_missing,
             declaration: name,
             expected: :assign,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: where_token.span,
             previous_span: name_token.span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp build_fn_meta(
         fn_token,
         name_token,
         name,
         params,
         return_type,
         visibility,
         guard,
         constraints,
         effects,
         parameter_span,
         return_arrow_token,
         effects_span,
         guard_span,
         requirements_span
       ) do
    meta = [
      name: name,
      params: params,
      visibility: visibility,
      arity: length(params),
      line: fn_token.line,
      col: fn_token.col
    ]

    meta = if return_type, do: Keyword.put(meta, :return_type, return_type), else: meta
    meta = if guard, do: Keyword.put(meta, :guards, guard), else: meta
    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta
    meta = if effects, do: Keyword.put(meta, :effects, effects), else: meta

    annotation_span = ast_source_span(return_type)

    terminal_span =
      requirements_span || guard_span || effects_span || annotation_span || parameter_span || name_token.span

    fields =
      %{}
      |> maybe_put_source_field(:parameters, parameter_span)
      |> maybe_put_source_field(:return_arrow, return_arrow_token)
      |> maybe_put_source_field(:effects, effects_span)
      |> maybe_put_source_field(:guard, guard_span)
      |> maybe_put_source_field(:requirements, requirements_span)

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(fn_token.span, terminal_span) || fn_token.span,
      opener: fn_token.span,
      name: name_token.span,
      annotation: annotation_span,
      guard: ast_source_span(guard),
      fields: fields
    })
  end

  defp put_function_body_source_info(meta, body, assign_token, where_span) do
    case {Metadata.source_info(meta), ast_source_span(body)} do
      {%SourceInfo{} = info, %Cure.Diagnostic.Span{} = body_span} ->
        fields =
          info.fields
          |> maybe_put_source_field(:separator, assign_token)
          |> maybe_put_source_field(:where, where_span)

        whole = through_spans(info.whole, where_span || body_span) || info.whole

        Metadata.put_source_info(meta, %{
          info
          | whole: whole,
            body: body_span,
            operator: assign_token.span,
            fields: fields
        })

      _ ->
        meta
    end
  end

  defp ast_source_span({_, meta, _}) when is_list(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp ast_source_span(_), do: nil

  defp parse_fn_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      %Token{type: :bar} ->
        bar_token = peek(state)
        state = advance(state)
        {clause, state} = parse_single_fn_clause(state, bar_token)
        state = skip_newlines(state)
        {rest, state} = parse_fn_clauses(state)
        {[clause | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_single_fn_clause(state, bar_token) do
    # Parse pattern(s) until -> or when
    {patterns, state} = parse_clause_patterns(state, [])

    # Optional guard
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    {arrow_token, state} = expect_branch_arrow_token(state, :function_clause, guard || List.last(patterns))
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    pattern_spans = patterns |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    pattern_span = through_spans(List.first(pattern_spans), List.last(pattern_spans))
    body_span = ast_source_span(body)

    info = %SourceInfo{
      whole: through_spans(bar_token.span, body_span) || bar_token.span,
      opener: bar_token.span,
      operator: arrow_token && arrow_token.span,
      arguments: pattern_spans,
      pattern: pattern_span,
      guard: ast_source_span(guard),
      body: body_span
    }

    clause = %{params: patterns, guard: guard, body: [body], source_info: info}
    {clause, state}
  end

  defp put_function_clause_source_info(meta, clauses) do
    case Metadata.source_info(meta) do
      %SourceInfo{} = info ->
        branches = clauses |> Enum.map(& &1.source_info.whole) |> Enum.reject(&is_nil/1)
        whole = through_spans(info.whole, List.last(branches)) || info.whole
        Metadata.put_source_info(meta, %{info | whole: whole, branches: branches})

      _ ->
        meta
    end
  end

  defp parse_clause_patterns(state, acc) do
    case peek(state) do
      %Token{type: :arrow} ->
        {Enum.reverse(acc), state}

      %Token{type: :keyword, value: :when} ->
        {Enum.reverse(acc), state}

      _ ->
        {pat, state} = parse_expr(state, bp_above(state, "<"))
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            parse_clause_patterns(state, [pat | acc])

          _ ->
            {Enum.reverse([pat | acc]), state}
        end
    end
  end

  defp put_let_source_info(meta, %Token{} = token, pattern, body, annotation, assign_token, grade_span) do
    body_span = ast_source_span(body)

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(token.span, body_span) || token.span,
      opener: token.span,
      name: ast_source_span(pattern),
      pattern: ast_source_span(pattern),
      operator: assign_token && assign_token.span,
      annotation: annotation,
      # The grade is a prefix decorator, so it is no longer part of the annotation.
      # Diagnostics that point at the grade read it from here.
      fields: if(grade_span, do: %{grade: grade_span}, else: %{}),
      body: body_span
    })
  end

  defp put_let_source_info(meta, _token, _pattern, _body, _annotation, _assign_token, _grade_span), do: meta

  # -- Typed Parameters  name: Type [= default] ------------------------------

  defp parse_typed_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} -> {[], state}
      %Token{type: type} when type in [:rbracket, :rbrace] -> {[], state}
      _ -> parse_typed_params_list(state)
    end
  end

  defp parse_typed_params_list(state) do
    {param, state} = parse_single_typed_param(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)

        {rest, state} =
          case peek(state) do
            %Token{type: type} when type in [:rbracket, :rbrace] -> {[], state}
            _ -> parse_typed_params_list(state)
          end

        {[param | rest], state}

      _ ->
        {[param], state}
    end
  end

  defp parse_single_typed_param(state) do
    case peek(state) do
      %Token{type: :lbrace} ->
        parse_implicit_param(state)

      %Token{type: type} when type in [:identifier, :keyword, :star] ->
        parse_explicit_param(state)

      %Token{type: :at} ->
        parse_explicit_param(state)

      %Token{type: :operator, value: "**"} ->
        parse_explicit_param(state)

      %Token{} = token ->
        error =
          {:invalid_parameter_name,
           %{
             observed: token.value || token.type,
             token_type: token.type,
             span: token.span,
             line: token.line,
             column: token.col
           }}

        placeholder = {:param, [invalid: true], "_invalid_parameter"}
        {placeholder, state |> add_error(error) |> advance()}
    end
  end

  # QTT grades (plan slice 5). Grades are binder decorators and sit before the
  # complete binder (including an external label): `@linear c : Chan(Cmd)`,
  # `{@erased n : Nat}`. An absent grade means
  # `ω`, so every existing program is unchanged.
  #
  # The grade belongs to the ARROW, not to the name and not to the type: Core spells
  # it `{:pi, g, dom, cod}` and `Conv` compares `g` as part of the Pi while `dom` is
  # an ordinary type. The decorator is parsed as part of the binder, rather than
  # being attached as a declaration-level decorator.
  #
  # `@unrestricted` is deliberately NOT a spelling: `ω` is written by omission.
  @grade_atoms [:erased, :linear, :affine]

  # Tokens that cannot begin a type, so finding one where a graded binder's type
  # belongs means the type is simply absent.
  @non_type_tokens [:rparen, :rbrace, :rbracket, :comma, :assign, :newline, :indent, :dedent, :eof]

  # Parse the grade decorator used on parameters and local bindings. This is
  # intentionally separate from parse_at/1: a binder decorator is part of the
  # binder grammar, not a declaration-level decorator attached to an AST node.
  defp parse_binder_grade_prefix(state) do
    case peek(state) do
      %Token{type: :at} = at_token ->
        state = advance(state)

        case peek(state) do
          %Token{type: type, value: value} = name_token
          when type in [:identifier, :keyword] ->
            grade =
              case value do
                :erased -> :erased
                :linear -> :linear
                :affine -> :affine
                "erased" -> :erased
                "linear" -> :linear
                "affine" -> :affine
                _ -> nil
              end

            if grade in @grade_atoms do
              {{:grade_prefix, grade, at_token, name_token}, advance(state)}
            else
              {nil, unknown_grade_error(state, at_token, name_token, value)}
            end

          %Token{} = bad_token ->
            {nil, unknown_grade_error(state, at_token, bad_token, bad_token.value || bad_token.type)}
        end

      _ ->
        {nil, state}
    end
  end

  # Only a grade may decorate a binder, so an unrecognised one is reported as an
  # unknown grade: the diagnostic names the supported grades and offers a typo
  # repair over the whole decorator, `@` included, so the edit is applicable.
  defp unknown_grade_error(state, %Token{} = at_token, %Token{} = offending, spelling) do
    span = through_spans(at_token.span, offending.span) || at_token.span

    add_error(state, {
      :unknown_grade,
      %{
        grade: spelling,
        span: span,
        supported: @grade_atoms,
        line: at_token.line,
        column: at_token.col
      }
    })
  end

  # The span of a `@linear`/`@affine`/`@erased` decorator, `@` through the grade name.
  # A grade no longer sits in the annotation slot, so a diagnostic that points at the
  # grade has to reach for the prefix rather than the annotation span.
  defp grade_prefix_span({:grade_prefix, _grade, %Token{span: at_span}, %Token{span: name_span}}),
    do: through_spans(at_span, name_span) || at_span

  defp grade_prefix_span(_prefix), do: nil

  # A graded binder must state a type -- the grade restricts how a value of that type
  # may be used, so `@linear c` and `@linear c :` are both errors. The empty annotation
  # is caught BEFORE `parse_type_expr` runs: handing it a `)` makes it read past the
  # end of the binder and report whatever follows, burying the grade under a generic
  # "expected )". Ungraded binders keep the plain annotation path, where an omitted
  # type is legal and inferred.
  defp parse_graded_binder_annotation(state, name, nil), do: parse_binder_annotation(state, name)

  defp parse_graded_binder_annotation(state, name, grade_prefix) do
    case {peek(state), peek_at(state, 1)} do
      {%Token{type: :colon}, %Token{type: type}} when type in @non_type_tokens ->
        {nil, nil, missing_grade_type(advance(state), name, grade_prefix), grade_prefix_span(grade_prefix)}

      {%Token{type: type}, _next} when type in @non_type_tokens ->
        {nil, nil, missing_grade_type(state, name, grade_prefix), grade_prefix_span(grade_prefix)}

      _ ->
        {_ignored_grade, type_ast, state, annotation_span} = parse_binder_annotation(state, name)

        if type_ast do
          {nil, type_ast, state, annotation_span}
        else
          {nil, nil, missing_grade_type(state, name, grade_prefix), grade_prefix_span(grade_prefix)}
        end
    end
  end

  defp missing_grade_type(state, name, grade_prefix) do
    span = grade_prefix_span(grade_prefix)
    observed = peek(state)

    add_error(state, {
      :grade_requires_type,
      %{
        name: name,
        grade: elem(grade_prefix, 1),
        span: span,
        observed_span: observed && observed.span,
        line: span && span.start_line,
        column: span && span.start_column
      }
    })
  end

  # A binder's annotation: `: Type`. `name` labels the binder
  # for diagnostics.
  # `stop_on` lists the tokens that may legally stand where the type would go, for
  # binders whose type may be omitted and inferred. Consuming the `:` and stopping
  # there keeps the binder intact; handing `=` to parse_type_expr instead makes it
  # read past the binding and report whatever follows it.
  defp parse_binder_annotation(state, _name, stop_on \\ []) do
    annotation_start = peek(state)

    case peek(state) do
      %Token{type: :colon} ->
        next = peek_at(state, 1)

        if next && next.type in stop_on do
          {nil, nil, advance(state), nil}
        else
          {type_ast, state} = parse_type_expr(advance(state))
          {nil, type_ast, state, annotation_span(annotation_start, type_ast, state)}
        end

      _ ->
        {nil, nil, state, nil}
    end
  end

  defp annotation_span(%Token{span: %Cure.Diagnostic.Span{} = first}, type_ast, _state) do
    case ast_source_span(type_ast) do
      %Cure.Diagnostic.Span{} = last -> through_spans(first, last) || first
      _ -> first
    end
  end

  defp annotation_span(_start, _type_ast, _state), do: nil

  defp put_binder_meta(meta, grade, type_ast) do
    meta = if type_ast, do: Keyword.put(meta, :type, type_ast), else: meta
    if grade, do: Keyword.put(meta, :grade, grade), else: meta
  end

  # `{name}` or `{name: Type}` — an implicit, erased argument (design spec §6).
  # Its type may be omitted and inferred by the elaborator from later parameter
  # types / the return type. `{name :g Type}` overrides the erased default.
  defp parse_implicit_param(state) do
    start_token = peek(state)
    state = advance(state)
    {grade_prefix, state} = parse_binder_grade_prefix(state)
    name_token = peek(state)

    {name, state} =
      case name_token do
        %Token{type: type} when type in [:identifier, :keyword] ->
          {to_string(name_token.value), advance(state)}

        %Token{} ->
          error =
            {:invalid_parameter_name,
             %{
               implicit: true,
               observed: name_token.value || name_token.type,
               token_type: name_token.type,
               opener_span: start_token.span,
               span: name_token.span,
               line: name_token.line,
               column: name_token.col
             }}

          state = add_error(state, error)
          state = if name_token.type == :rbrace, do: state, else: advance(state)
          {"_invalid_implicit_parameter", state}
      end

    {_ignored_grade, type_ast, state, annotation_span} =
      parse_graded_binder_annotation(state, name, grade_prefix)

    grade = grade_prefix && elem(grade_prefix, 1)

    {state, close_token} =
      expect_container_close(state, :rbrace, :implicit_parameter, start_token, [type_ast], false, %{
        binder: name,
        binder_span: name_token.span,
        closing_tokens: [:comma, :rparen]
      })

    meta = put_binder_meta([implicit: true], grade, type_ast)

    meta =
      put_param_source_info(meta, start_token, name_token,
        annotation_span: annotation_span,
        terminal_span: (close_token && close_token.span) || annotation_span || name_token.span,
        opener: start_token.span,
        closer: close_token && close_token.span
      )

    {{:param, meta, name}, state}
  end

  # `lambda?` marks the anonymous-fn parameter list. `parse_single_typed_param/1`
  # screens the named-function path before calling here, but a lambda's list is
  # parsed straight from the source, so this has to cope with whatever was
  # written -- and a lambda has no caller-facing labels to parse.
  defp parse_explicit_param(state, lambda? \\ false) do
    {grade_prefix, state} = parse_binder_grade_prefix(state)
    start_token = (grade_prefix && elem(grade_prefix, 2)) || peek(state)

    # Check for variadic: *name or **name
    {kind, marker_span, state} =
      case peek(state) do
        %Token{type: :operator, value: "**"} = marker ->
          {:keyword_variadic, marker.span, advance(state)}

        %Token{type: :star} = marker ->
          next = peek_at(state, 1)

          if next && next.type == :star do
            {_, state} = {nil, advance(state) |> advance()}
            span = through_spans(marker.span, next.span) || marker.span
            {:keyword_variadic, span, state}
          else
            {_, state} = {nil, advance(state)}
            {:variadic, marker.span, state}
          end

        _ ->
          {:positional, nil, state}
      end

    name_token = peek(state)

    {name, name_token, explicit_fresh?, state} =
      case {name_token, peek_at(state, 1), peek_at(state, 2), peek_at(state, 3)} do
        {%Token{type: :lt}, %Token{type: :identifier, value: "fresh"},
         %Token{type: :identifier, value: name} = binder_token, %Token{type: :gt}} ->
          state = state |> advance() |> advance() |> advance() |> advance()
          {to_string(name), binder_token, true, state}

        {%Token{type: type}, _, _, _} when type in [:identifier, :keyword] ->
          {to_string(name_token.value), name_token, false, advance(state)}

        {%Token{}, _, _, _} when kind in [:variadic, :keyword_variadic] ->
          error =
            {:variadic_parameter_name_missing,
             %{
               kind: kind,
               observed: name_token.value || name_token.type,
               token_type: name_token.type,
               marker_span: marker_span,
               observed_span: name_token.span,
               span: parameter_name_site(name_token),
               line: name_token.line,
               column: name_token.col
             }}

          state = add_error(state, error)

          state =
            if name_token.type in [:rparen, :rbracket, :rbrace, :comma, :newline, :eof],
              do: state,
              else: advance(state)

          {"_missing_variadic_parameter", name_token, false, state}

        {%Token{}, _, _, _} ->
          # Nothing that can name a parameter. Reaching the end of this case
          # without a clause used to raise a CaseClauseError out of the whole
          # compile, so a lambda like `fn(42) -> 1` crashed instead of being
          # reported.
          name_details = %{
            observed: name_token.value || name_token.type,
            token_type: name_token.type,
            span: name_token.span,
            line: name_token.line,
            column: name_token.col
          }

          error =
            {:invalid_parameter_name, if(lambda?, do: Map.put(name_details, :lambda, true), else: name_details)}

          state = add_error(state, error)

          # A closing or separating token belongs to the enclosing list, which
          # reports it in its own terms; consuming it here would hide that.
          state =
            if name_token.type in [:rparen, :rbracket, :rbrace, :comma, :newline, :eof],
              do: state,
              else: advance(state)

          {"_invalid_parameter", name_token, false, state}
      end

    # Two-name label form `label internal: T` (Swift). A second identifier before
    # the annotation means the first name was the EXTERNAL caller-facing label and
    # this second one is the INTERNAL body binder. Single-name params carry no
    # label (the one name serves as both, and any call label is optional).
    # A lambda is applied positionally and has no caller-facing labels, so a
    # second name there is not the label form -- it is a parameter that lost its
    # comma. Leaving it unconsumed lets the parameter list report the missing
    # separator, instead of silently reading `fn(x y)` as one labelled binder.
    {label, label_span, name, name_token, state} =
      case peek(state) do
        %Token{type: :identifier} = internal_token when not lambda? and not explicit_fresh? ->
          {name, name_token.span, to_string(internal_token.value), internal_token, advance(state)}

        _ ->
          {nil, nil, name, name_token, state}
      end

    # Optional type annotation `: Type`. A graded binder must have one.
    {_ignored_grade, type_ast, state, annotation_span} =
      parse_graded_binder_annotation(state, name, grade_prefix)

    grade = grade_prefix && elem(grade_prefix, 1)

    # Optional default value: = expr
    {default, assign_token, state} =
      case peek(state) do
        %Token{type: :assign} = assign_token ->
          state = advance(state)
          state = skip_newlines(state)
          {d, state} = parse_expr(state, bp_above(state, "="))
          {d, assign_token, state}

        _ ->
          {nil, nil, state}
      end

    param_meta = put_binder_meta([], grade, type_ast)
    param_meta = if label, do: Keyword.put(param_meta, :label, label), else: param_meta
    param_meta = if default, do: Keyword.put(param_meta, :default, default), else: param_meta
    param_meta = if kind != :positional, do: Keyword.put(param_meta, :kind, kind), else: param_meta
    param_meta = if explicit_fresh?, do: Keyword.put(param_meta, :explicit_fresh, true), else: param_meta

    terminal_span = ast_source_span(default) || annotation_span || name_token.span

    param_meta =
      put_param_source_info(param_meta, start_token, name_token,
        annotation_span: annotation_span,
        terminal_span: terminal_span,
        label_span: label_span,
        operator: assign_token && assign_token.span,
        marker_span: marker_span
      )

    {{:param, param_meta, name}, state}
  end

  defp parameter_name_site(%Token{type: type, span: %Cure.Diagnostic.Span{} = span})
       when type in [:rparen, :rbracket, :rbrace, :comma, :newline, :eof],
       do: %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column}

  defp parameter_name_site(%Token{span: span}), do: span

  defp put_param_source_info(meta, %Token{} = start_token, %Token{} = name_token, roles) do
    fields =
      case Keyword.get(roles, :label_span) do
        %Cure.Diagnostic.Span{} = span -> %{label: span}
        _ -> %{}
      end

    fields = maybe_put_source_field(fields, :variadic_marker, Keyword.get(roles, :marker_span))

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(start_token.span, Keyword.get(roles, :terminal_span)) || name_token.span,
      name: name_token.span,
      operator: Keyword.get(roles, :operator),
      annotation: Keyword.get(roles, :annotation_span),
      body: ast_source_span(Keyword.get(meta, :default)),
      opener: Keyword.get(roles, :opener),
      closer: Keyword.get(roles, :closer),
      fields: fields
    })
  end

  # -- Lambda (anonymous fn) -------------------------------------------------
  #
  # v0.22.0 introduces two new multi-statement body shapes in addition
  # to the historical indented-block and single-expression forms:
  #
  #   fn (x) -> { stmt1; stmt2; final }     (brace-delimited)
  #   fn (x) ->
  #     stmt1
  #     stmt2
  #   end                                   (end-terminated)
  #
  # Both compile to the same `{:block, meta, exprs}` AST node that the
  # v0.19.0 indented form already produces; the only user-visible
  # difference is that these two forms work inside argument lists,
  # where the lexer suppresses newlines and `:indent`/`:dedent` are
  # never emitted.
  defp parse_lambda_body(state, token) do
    {open_token, state} = expect_lambda_open(state, token)
    {params, state} = parse_lambda_params(state)

    {state, close_token} =
      if open_token do
        expect_container_close(state, :rparen, :lambda_parameters, open_token, params, true)
      else
        case peek(state) do
          %Token{type: :rparen} = close -> {advance(state), close}
          _ -> {state, nil}
        end
      end

    {state, arrow_token} =
      if close_token, do: expect_lambda_arrow(state, token, close_token), else: {state, nil}

    state = skip_newlines(state)
    {body, state} = parse_lambda_block_body(state, token)

    meta = [params: params, line: token.line, col: token.col]

    meta =
      put_lambda_source_info(
        meta,
        token,
        open_token,
        close_token,
        arrow_token,
        lambda_terminal_token(state),
        params,
        body
      )

    ast = {:lambda, meta, [body]}
    {ast, state}
  end

  defp put_lambda_source_info(
         meta,
         lambda_token,
         open_token,
         close_token,
         arrow_token,
         terminal_token,
         params,
         body
       ) do
    body_span = ast_source_span(body)
    terminal_span = (terminal_token && terminal_token.span) || body_span
    parameter_spans = params |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)

    parameter_range =
      case {open_token, close_token} do
        {%Token{span: opener}, %Token{span: closer}} -> through_spans(opener, closer)
        _ -> nil
      end

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(lambda_token.span, terminal_span) || lambda_token.span,
      opener: lambda_token.span,
      closer: terminal_token && terminal_token.span,
      operator: arrow_token && arrow_token.span,
      arguments: parameter_spans,
      body: body_span,
      fields: %{
        parameters: parameter_range,
        parameter_opener: open_token && open_token.span,
        parameter_closer: close_token && close_token.span
      }
    })
  end

  defp lambda_terminal_token(state) do
    case peek_at(state, -1) do
      %Token{type: :rbrace} = token -> token
      %Token{type: :keyword, value: :end} = token -> token
      _ -> nil
    end
  end

  defp expect_lambda_open(state, lambda_token) do
    case expect_token(state, :lparen) do
      {:ok, open, next_state} ->
        {open, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)
        insertion = zero_width_start(observed.span)

        error =
          {:lambda_parameters_unparenthesized,
           %{
             expected: :lparen,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: insertion,
             observed_span: observed.span,
             lambda_span: lambda_token.span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp expect_lambda_arrow(state, lambda_token, close_token) do
    case expect_token(state, :arrow) do
      {:ok, arrow, next_state} ->
        {next_state, arrow}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:lambda_arrow_missing,
           %{
             expected: :arrow,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             lambda_span: lambda_token.span,
             previous_span: close_token.span,
             line: observed.line,
             column: observed.col
           }}

        {%{next_state | errors: [error | rest]}, nil}
    end
  end

  defp zero_width_start(%Cure.Diagnostic.Span{} = span),
    do: %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column}

  # The observed token can be the EOF token `peek/1` synthesizes once `pos`
  # runs past the last token; the lexer never authored a span for it. Running
  # out of input is an ordinary syntax error, so narrowing a missing span has
  # to yield a missing span rather than raise — `Cure.Diagnostic.Adapter`
  # already falls back to the caller-supplied span when `:span` is nil, and
  # the diagnostic still carries the token's line/column. Raising here instead
  # escapes even the tolerant passes: `Cure.Compiler.Parser.harvest/4` promises
  # never to raise, and `Cure.Compiler.SourceResolver` harvests every `.cure`
  # file under the source roots to resolve a module by name.
  defp zero_width_start(nil), do: nil

  # Route the lambda body to one of four shapes: indented block, brace
  # block, end-terminated block, or single expression. The brace and end
  # forms emit a `{:block, [block_shape: :brace | :end, ...], exprs}`
  # node so the Printer and AlgebraFormatter can round-trip the
  # author's chosen shape.
  defp parse_lambda_block_body(state, token) do
    case peek(state) do
      %Token{type: :indent} ->
        parse_indented_lambda_body(state, token)

      %Token{type: :lbrace} ->
        parse_brace_lambda_body(state, token)

      _ ->
        parse_bare_lambda_body(state, token)
    end
  end

  # Indented block, optionally followed by an `end` terminator:
  #
  #   fn (x) ->
  #     stmt1
  #     stmt2
  #   end
  #
  # The `end` is optional; when present the block shape is tagged so
  # the formatter can keep it. Without `end` the block reverts to the
  # v0.19.0 indented form.
  defp parse_indented_lambda_body(state, token) do
    {body, state} = parse_block(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :keyword, value: :end} ->
        state = advance(state)
        {tag_block_shape(body, :end, token), state}

      _ ->
        {body, state}
    end
  end

  # Brace block `{ stmt1; stmt2; final }`. Statement separator is `;`,
  # with newlines accepted as a synonym when the brace body happens to
  # live outside a paren scope. Empty braces compile to `:ok`.
  defp parse_brace_lambda_body(state, token) do
    open_token = peek(state)
    state = advance(state)
    state = skip_stmt_seps(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        state = advance(state)
        {{:literal, [subtype: :null, line: token.line, col: token.col], nil}, state}

      _ ->
        {exprs, state} = parse_brace_block_body(state, [])

        state =
          case expect_token(state, :rbrace) do
            {:ok, _close, next_state} ->
              next_state

            {:error, next_state} ->
              [_generic | rest] = next_state.errors
              observed = peek(next_state)

              error =
                {:lambda_block_unterminated,
                 %{
                   expected: :rbrace,
                   observed: observed.type,
                   span: observed.span,
                   opener_span: open_token.span,
                   previous_span: exprs |> List.last() |> first_node_source_span(),
                   body_style: :brace,
                   line: observed.line,
                   column: observed.col
                 }}

              %{next_state | errors: [error | rest]}
          end

        {build_block(exprs, :brace, token), state}
    end
  end

  # Bare (no leading `{` or `:indent`) body. When the first expression
  # is followed by a statement separator *and* an `end` keyword
  # eventually appears, treat the sequence as an end-terminated block;
  # otherwise parse a single expression as the lambda body.
  defp parse_bare_lambda_body(state, token) do
    saved_pos = state.pos
    {first, state} = parse_expr(state, 0)

    case peek(state) do
      %Token{type: :keyword, value: :end} ->
        state = advance(state)
        {build_block([first], :end, token), state}

      %Token{type: :semicolon} ->
        state = %{state | pos: saved_pos}
        parse_end_terminated_lambda_body(state, token)

      _ ->
        {first, state}
    end
  end

  # `fn (x) -> stmt1; stmt2; ... end` -- explicit `end` terminator, with
  # `;` (and when available, newlines) as the statement separator.
  defp parse_end_terminated_lambda_body(state, token) do
    {exprs, state} = parse_brace_block_body(state, [])
    state = skip_stmt_seps(state)

    case peek(state) do
      %Token{type: :keyword, value: :end} ->
        state = advance(state)
        {build_block(exprs, :end, token), state}

      %Token{} = other ->
        error =
          {:lambda_block_unterminated,
           %{
             expected: :end,
             observed: other.type,
             span: other.span,
             opener_span: token.span,
             line: other.line,
             column: other.col
           }}

        state = add_error(state, error)
        {build_block(exprs, :end, token), state}
    end
  end

  # Parse a sequence of statements separated by `;` or newlines. Stops
  # when the next token is `:rbrace`, `:keyword :end`, or `:eof`.
  defp parse_brace_block_body(state, acc) do
    state = skip_stmt_seps(state)

    case peek(state) do
      %Token{type: type} when type in [:rbrace, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :keyword, value: :end} ->
        {Enum.reverse(acc), state}

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_stmt_seps(state)
        parse_brace_block_body(state, [expr | acc])
    end
  end

  defp skip_stmt_seps(state) do
    case peek(state) do
      %Token{type: :semicolon} -> skip_stmt_seps(advance(state))
      %Token{type: :newline} -> skip_stmt_seps(advance(state))
      _ -> state
    end
  end

  defp build_block(exprs, shape, token) do
    case exprs do
      [] -> {:literal, [subtype: :null, line: token.line, col: token.col], nil}
      [single] -> single
      many -> {:block, [block_shape: shape, line: token.line, col: token.col], many}
    end
  end

  defp tag_block_shape({:block, meta, exprs}, shape, _token) when is_list(meta) do
    {:block, Keyword.put(meta, :block_shape, shape), exprs}
  end

  defp tag_block_shape(expr, shape, token) do
    {:block, [block_shape: shape, line: token.line, col: token.col], [expr]}
  end

  defp parse_lambda_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {param, state} = parse_explicit_param(state, true)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_lambda_params(state)
            {[param | rest], state}

          _ ->
            {[param], state}
        end
    end
  end

  # -- Module  mod Name.Path -------------------------------------------------

  defp parse_module(state) do
    token = peek(state)
    state = advance(state)

    # Parse module name (dotted path)
    name_start = peek(state)
    {name, name_end, state} = parse_dotted_name_owned(state)
    state = skip_newlines(state)

    # Parse indented body. Leading `##` docs immediately after `mod Name`
    # describe the *module* itself, not the first definition inside the
    # body, so pull them back onto the container's `:doc` meta.
    outer_module = state.enclosing_module
    state = %{state | enclosing_module: join_module_name(outer_module, name)}
    {body_stmts, leading_doc, state} = parse_definition_block_with_lead_doc(state)
    state = %{state | enclosing_module: outer_module}

    meta = [container_type: :module, name: name, language: :cure, line: token.line, col: token.col]
    meta = put_body_declaration_source_info(meta, token, name_start, name_end, body_stmts)
    meta = if leading_doc != "", do: Keyword.put(meta, :doc, leading_doc), else: meta
    ast = {:container, meta, body_stmts}
    {ast, state}
  end

  # -- Proof container  proof Name.Path (v0.19.0) ----------------------------
  #
  # Mirrors `parse_module/1` but emits `container_type: :proof`. Every
  # binding inside a proof container is expected to elaborate to an
  # `Eq(T, a, b)` proof; the type checker reports mismatches under code `E026`.
  defp parse_proof_container(state) do
    token = peek(state)
    state = advance(state)

    name_start = peek(state)
    {name, name_end, state} = parse_dotted_name_owned(state)
    state = skip_newlines(state)
    {body_stmts, state} = parse_definition_block(state)

    meta = [
      container_type: :proof,
      name: name,
      language: :cure,
      line: token.line,
      col: token.col
    ]

    meta = put_body_declaration_source_info(meta, token, name_start, name_end, body_stmts)

    {{:container, meta, body_stmts}, state}
  end

  defp put_body_declaration_source_info(meta, keyword, name_start, name_end, body) do
    branches = body |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    name = through_spans(name_start.span, name_end.span) || name_start.span

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(keyword.span, List.last(branches) || name) || keyword.span,
      opener: keyword.span,
      name: name,
      branches: branches
    })
  end

  # -- Fixity declarations (Phase 3) -----------------------------------------
  #
  # `precedencegroup`/`infix`/`prefix`/`postfix` build inert
  # `{:precedencegroup, …}` and `{:fixity, …}` AST nodes. This is purely
  # additive: later Phase-3 tasks feed these into `Cure.Compiler.Parser.FixityTable`
  # ahead of expression parsing, then flip the Pratt loop onto it. In this task
  # nothing downstream consumes them, and the static `Precedence` table still
  # governs how expressions bind.

  # True at the distinctive `<op> : Group` shape a fixity declaration takes.
  # The missing-colon spelling `<op> Group` is also recognized so it can receive
  # the declaration-specific repair; `prefix + 1`, `prefix: x`, and a bare
  # `infix` still remain ordinary identifiers.
  defp fixity_decl_ahead?(state) do
    op = peek_at(state, 1)
    separator_or_group = peek_at(state, 2)

    op != nil and separator_or_group != nil and
      separator_or_group.type in [:colon, :identifier] and fixity_op_token?(op)
  end

  # An operator lexeme is any symbolic-operator token or a word/backtick
  # identifier used as an operator name — anything that is not a delimiter.
  defp fixity_op_token?(%Token{type: type}),
    do: type not in [:colon, :newline, :indent, :dedent, :eof, :comma, :assign]

  defp fixity_op_token?(_), do: false

  # `infix|prefix|postfix <op> : Group`. Whether the operator conflicts with an
  # existing declaration is not decided here — it is decided when the module's
  # declarations are folded into `fixity(M)`
  # (`Cure.Compiler.Parser.FixityResolver.assemble/5`): a same-lexeme
  # different-group (or same-group-name different-body) redeclaration is a
  # `:conflicting_operator_fixity` / `:conflicting_precedence_group` error; an
  # identical redeclaration is a no-op.
  defp parse_fixity(state) do
    kw = peek(state)
    fixity = String.to_atom(to_string(kw.value))
    state = advance(state)

    op_token = peek(state)
    lexeme = fixity_lexeme(op_token)
    state = advance(state)

    {colon_token, state} = expect_fixity_colon(state, kw, op_token, fixity, lexeme)

    {group, group_token, state} =
      case peek(state) do
        %Token{type: :identifier, value: v} = token -> {String.to_atom(v), token, advance(state)}
        _ -> {nil, nil, state}
      end

    meta = [
      fixity: fixity,
      operator: lexeme,
      group: group,
      line: kw.line,
      col: kw.col
    ]

    meta = put_fixity_source_info(meta, kw, op_token, colon_token, group_token)

    {{:fixity, meta, []}, state}
  end

  defp expect_fixity_colon(state, keyword_token, operator_token, fixity, operator) do
    case expect_token(state, :colon) do
      {:ok, colon, next_state} ->
        {colon, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :fixity_colon_missing,
             family: fixity,
             declaration: operator,
             expected: :colon,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: keyword_token.span,
             previous_span: operator_token.span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp put_fixity_source_info(meta, %Token{} = first, %Token{} = operator, colon, group) do
    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(first.span, (group && group.span) || operator.span) || first.span,
      opener: first.span,
      operator: operator.span,
      name: group && group.span,
      fields: maybe_put_source_field(%{}, :separator, colon)
    })
  end

  defp fixity_lexeme(%Token{value: v}) when is_binary(v), do: v
  defp fixity_lexeme(%Token{value: v}), do: to_string(v)

  # `precedencegroup Name` with an optional indented body of
  # `associativity:`/`higher_than:`/`lower_than:` lines.
  defp parse_precedencegroup(state) do
    kw = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = String.to_atom(to_string(name_token.value))
    state = advance(state)
    state = skip_newlines(state)

    {fields, field_spans, source_fields, state} = parse_precedencegroup_body(state, name, name_token)
    meta = [name: name, line: kw.line, col: kw.col] ++ fields

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(kw.span, List.last(field_spans) || name_token.span) || kw.span,
        opener: kw.span,
        name: name_token.span,
        branches: field_spans,
        fields: source_fields
      })

    {{:precedencegroup, meta, []}, state}
  end

  defp parse_precedencegroup_body(state, group, group_token) do
    case peek(state) do
      %Token{type: :indent} -> collect_precedencegroup_fields(advance(state), [], [], %{}, group, group_token)
      _ -> {[], [], %{}, state}
    end
  end

  defp collect_precedencegroup_fields(state, acc, span_acc, source_fields, group, group_token) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :dedent} ->
        {Enum.reverse(acc), Enum.reverse(span_acc), source_fields, advance(state)}

      %Token{type: :eof} ->
        {Enum.reverse(acc), Enum.reverse(span_acc), source_fields, state}

      %Token{type: :identifier, value: field} ->
        field_token = peek(state)
        {state, colon_token} = expect_precedencegroup_field_colon(advance(state), field_token, group, group_token)
        {value, value_span, state} = parse_precedencegroup_value(field, state)

        field_span =
          through_spans(field_token.span, value_span || (colon_token && colon_token.span) || field_token.span)

        {acc, span_acc, source_fields} =
          case precedencegroup_field_key(field) do
            nil ->
              {acc, [field_span | span_acc], source_fields}

            key ->
              fields =
                source_fields
                |> Map.put({key, :whole}, field_span)
                |> Map.put({key, :name}, field_token.span)
                |> maybe_put_source_field({key, :separator}, colon_token)
                |> maybe_put_source_field({key, :value}, value_span)

              {[{key, value} | acc], [field_span | span_acc], fields}
          end

        collect_precedencegroup_fields(state, acc, span_acc, source_fields, group, group_token)

      _ ->
        # Unrecognised line: skip to the block's end rather than loop.
        {Enum.reverse(acc), Enum.reverse(span_acc), source_fields, skip_to_dedent(state)}
    end
  end

  defp expect_precedencegroup_field_colon(state, field_token, group, group_token) do
    case expect_token(state, :colon) do
      {:ok, colon, next_state} ->
        {next_state, colon}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :precedencegroup_field_colon_missing,
             family: group,
             declaration: to_string(field_token.value),
             expected: :colon,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: group_token.span,
             previous_span: field_token.span,
             line: observed.line,
             column: observed.col
           }}

        {%{next_state | errors: [error | rest]}, nil}
    end
  end

  defp precedencegroup_field_key("associativity"), do: :assoc
  defp precedencegroup_field_key("higher_than"), do: :higher_than
  defp precedencegroup_field_key("lower_than"), do: :lower_than
  defp precedencegroup_field_key(_), do: nil

  defp parse_precedencegroup_value("associativity", state) do
    case peek(state) do
      %Token{type: :identifier, value: v} = token -> {String.to_atom(v), token.span, advance(state)}
      _ -> {nil, nil, state}
    end
  end

  defp parse_precedencegroup_value(_field, state), do: collect_group_names(state, [], nil, nil)

  # Collect group-name identifiers on the current line, tolerating `[ ]` and `,`.
  # Stops at the first non-name, non-delimiter token (newline/dedent/eof).
  defp collect_group_names(state, acc, first_span, last_span) do
    case peek(state) do
      %Token{type: :identifier, value: v} = token ->
        collect_group_names(advance(state), [String.to_atom(v) | acc], first_span || token.span, token.span)

      %Token{type: t} = token when t in [:comma, :lbracket, :rbracket] ->
        collect_group_names(advance(state), acc, first_span || token.span, token.span)

      _ ->
        {Enum.reverse(acc), through_spans(first_span, last_span) || first_span || last_span, state}
    end
  end

  defp skip_to_dedent(state) do
    case peek(state) do
      %Token{type: :dedent} -> advance(state)
      %Token{type: :eof} -> state
      _ -> skip_to_dedent(advance(state))
    end
  end

  # -- Record  rec Name [(TypeParams)] ---------------------------------------

  defp parse_record(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional type params: (A, B)
    {type_params, type_parameter_spans, type_parameter_span, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          open_token = peek(state)
          state = advance(state)
          {tp, tp_spans, state} = parse_name_list_with_spans(state, :rparen)

          {state, close_token} =
            expect_container_close(state, :rparen, :type_parameters, open_token, tp, true, %{
              declaration: name,
              declaration_kind: :record
            })

          span = through_spans(open_token.span, close_token && close_token.span) || open_token.span
          {tp, tp_spans, span, state}

        _ ->
          {[], [], nil, state}
      end

    state = skip_newlines(state)

    # Parse indented fields: name: Type
    {fields, state} = parse_record_fields(state, name)

    meta = [container_type: :struct, name: name, line: token.line, col: token.col]
    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
    branches = fields |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    terminal_span = List.last(branches) || type_parameter_span || name_token.span
    source_fields = if type_parameter_span, do: %{type_parameters: type_parameter_span}, else: %{}

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_token.span,
        arguments: type_parameter_spans,
        branches: branches,
        fields: source_fields
      })

    ast = {:container, meta, fields}
    {ast, state}
  end

  defp parse_record_fields(state, record) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {fields, state} = parse_record_field_list(state, record)
        state = expect_dedent(state)
        {fields, state}

      _ ->
        {[], state}
    end
  end

  defp parse_record_field_list(state, record) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        name_token = peek(state)
        state = advance(state)
        annotation_start = peek(state)
        state = expect_record_field_colon(state, name_token, record)
        {type_ast, state} = parse_type_expr(state)
        field_annotation_span = annotation_span(annotation_start, type_ast, state)

        # v0.19.0: optional `= default_expr` per record field.
        {default_ast, assign_token, state} =
          case peek(state) do
            %Token{type: :assign} = assign_token ->
              state = advance(state)
              state = skip_newlines(state)
              {default_ast, state} = parse_expr(state, 0)
              {default_ast, assign_token, state}

            _ ->
              {nil, nil, state}
          end

        state = skip_newlines(state)

        meta = [type: type_ast]
        meta = if default_ast, do: Keyword.put(meta, :default, default_ast), else: meta

        meta =
          put_param_source_info(
            meta,
            name_token,
            name_token,
            annotation_span: field_annotation_span,
            terminal_span: ast_source_span(default_ast) || field_annotation_span || name_token.span,
            operator: assign_token && assign_token.span
          )

        field = {:param, meta, to_string(name_token.value)}
        {rest, state} = parse_record_field_list(state, record)
        {[field | rest], state}
    end
  end

  defp expect_record_field_colon(state, field_token, record) do
    case expect_token(state, :colon) do
      {:ok, _colon, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :record_field_colon_missing,
             family: record,
             declaration: to_string(field_token.value),
             expected: :colon,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             previous_span: field_token.span,
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # -- Type  type Name[(Params)] = ... ---------------------------------------
  #
  # v0.21.0: the RHS of a `type` declaration may span multiple lines with
  # the canonical ADT `|` separator on continuation lines, and accept an
  # optional leading `|` before the first variant:
  #
  #     type Shape =
  #       | Circle(Int)
  #       | Square(Int)
  #       | Triangle(Int, Int, Int)
  #
  #     type Shape =
  #       Circle(Int)
  #       | Square(Int)
  #
  # Both are equivalent to the single-line form `type Shape = Circle(Int) | Square(Int)`.
  # The lexer emits a single `:indent`/`:dedent` pair around the continuation
  # block; `parse_type_def/1` absorbs it so the variants themselves can be
  # parsed by the existing `parse_type_variant/1` / `parse_more_variants/1`.

  # `typealias NAME(type_params?) = RHS` — a TRANSPARENT type synonym. Unlike
  # `type NAME = Ctor(...)` (a nominal single-constructor ADT), the RHS is always
  # parsed as a type EXPRESSION and the result is a `:type_annotation` node, which
  # the elaborator lowers to a nullary def whose δ-unfolding makes `NAME`
  # definitionally interchangeable with `RHS`. This disambiguates the applied-type
  # synonym `typealias Char = Bounded(1114112)` from the identically-shaped
  # single-variant ADT `type Color = RGB(Int)`, without disturbing the ADT path.
  defp parse_typealias(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {head_params, type_parameter_span, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          open_token = peek(state)
          state = advance(state)
          {tp, state} = parse_typed_params(state)

          {state, close_token} =
            expect_container_close(state, :rparen, :type_parameters, open_token, tp, true, %{
              declaration: name,
              declaration_kind: :typealias,
              closing_tokens: [:assign]
            })

          span = through_spans(open_token.span, close_token && close_token.span) || open_token.span
          {tp, span, state}

        _ ->
          {[], nil, state}
      end

    assign_token = if match?(%Token{type: :assign}, peek(state)), do: peek(state)
    state = expect_type_declaration_assign(state, :typealias, token, name_token, name, type_parameter_span)
    state = skip_newlines(state)
    {rhs, state} = parse_type_expr(state)

    # Keep the explicit spelling distinguishable from the deliberately
    # ambiguous `type X = Y` node. The elaborator's header pass uses this bit
    # to predeclare transparent aliases without accidentally turning a
    # forward-referenced one-constructor ADT into an alias.
    meta = [name: name, line: token.line, col: token.col, typealias: true]
    type_params = Enum.map(head_params, fn {:param, _meta, n} -> n end)
    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
    meta = if head_params != [], do: Keyword.put(meta, :params, head_params), else: meta

    rhs_span = ast_source_span(rhs)

    source_fields =
      %{}
      |> maybe_put_source_field(:type_parameters, type_parameter_span)
      |> maybe_put_source_field(:separator, assign_token)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, rhs_span || type_parameter_span || name_token.span) || token.span,
        opener: token.span,
        name: name_token.span,
        annotation: rhs_span,
        fields: source_fields
      })

    {{:type_annotation, meta, [rhs]}, state}
  end

  defp expect_type_declaration_assign(state, family, keyword_token, name_token, name, previous_span) do
    case expect_token(state, :assign) do
      {:ok, _assign, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        previous = previous_span || name_token.span

        error =
          {:declaration_separator_missing,
           %{
             kind: :type_declaration_assign_missing,
             family: family,
             declaration: name,
             expected: :assign,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: keyword_token.span,
             previous_span: previous,
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # `primitive Name` → a constructor-less primitive-type container. The optional
  # `@builtin(:tag)` decorator is threaded on by `attach_decorator/3` when the
  # form is written `@builtin(:tag) primitive Name`.
  defp parse_primitive_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = skip_newlines(state)

    meta = [
      container_type: :primitive,
      name: name,
      language: :cure,
      line: token.line,
      col: token.col
    ]

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, name_token.span) || token.span,
        opener: token.span,
        name: name_token.span
      })

    {{:container, meta, []}, state}
  end

  defp parse_type_def(state, opts \\ []) do
    opaque? = Keyword.get(opts, :opaque, false)
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional head params, parsed permissively (typed `a: Type` or bare `a`).
    # The ordinary-ADT path projects out just the names; the indexed-family path
    # (`type NAME(params) indices (idx)`) keeps the full typed telescope.
    {head_params, type_parameter_span, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          open_token = peek(state)
          state = advance(state)
          {tp, state} = parse_typed_params(state)

          {state, close_token} =
            expect_container_close(state, :rparen, :type_parameters, open_token, tp, true, %{
              declaration: name,
              declaration_kind: :type,
              closing_tokens: [:assign],
              closing_values: [:indices]
            })

          span = through_spans(open_token.span, close_token && close_token.span) || open_token.span
          {tp, span, state}

        _ ->
          {[], nil, state}
      end

    cond do
      # `opaque type Name(params)` — no `= …` body, no indices, no ctors. The
      # head params become the family's uniform parameters; the empty variant
      # list plus the `:opaque` container tag drive the non-eliminable marker.
      opaque? ->
        type_params = Enum.map(head_params, fn {:param, _meta, n} -> n end)
        meta = [container_type: :opaque, name: name, line: token.line, col: token.col]
        meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
        meta = if head_params != [], do: Keyword.put(meta, :params, head_params), else: meta

        meta =
          Metadata.put_source_info(meta, %SourceInfo{
            whole: through_spans(token.span, type_parameter_span || name_token.span) || token.span,
            opener: token.span,
            name: name_token.span,
            fields: maybe_put_source_field(%{}, :type_parameters, type_parameter_span)
          })

        {{:container, meta, []}, state}

      match?(%Token{type: :keyword, value: :indices}, peek(state)) ->
        parse_indexed_family(state, name, head_params, token, name_token, type_parameter_span)

      true ->
        type_params = Enum.map(head_params, fn {:param, _meta, n} -> n end)
        parse_type_def_adt(state, name, type_params, token, name_token, type_parameter_span)
    end
  end

  # Indexed (GADT) family: `type NAME(params) indices (idx)` followed by an
  # indentation-delimited block of constructor signatures. Head-paren args are
  # parameters (uniform, never matched); the `indices (…)` clause are indices.
  defp parse_indexed_family(state, name, params, token, name_token, type_parameter_span) do
    indices_token = peek(state)
    state = advance(state)
    {state, open_token} = expect_index_list_opener(state, name, indices_token)
    {idx_tele, state} = parse_typed_params(state)

    {state, close_token} =
      case open_token do
        %Token{} ->
          expect_container_close(state, :rparen, :type_indices, open_token, idx_tele, true, %{
            declaration: name
          })

        nil ->
          case peek(state) do
            %Token{type: :rparen} = close_token -> {advance(state), close_token}
            _ -> {state, nil}
          end
      end

    state = skip_newlines_and_comments(state)

    {opened_block, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state)}
        _ -> {false, state}
      end

    {ctors, state} = parse_gadt_ctors(state, [], name)

    state =
      if opened_block do
        state |> skip_newlines() |> expect_dedent()
      else
        state
      end

    meta = [name: name, params: params, indices: idx_tele, line: token.line, col: token.col]
    branches = ctors |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)

    indices_span =
      through_spans(indices_token.span, close_token && close_token.span) ||
        through_spans(indices_token.span, open_token && open_token.span) || indices_token.span

    terminal_span = List.last(branches) || indices_span || type_parameter_span || name_token.span

    source_fields =
      %{}
      |> maybe_put_source_field(:type_parameters, type_parameter_span)
      |> maybe_put_source_field(:indices, indices_span)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_token.span,
        branches: branches,
        fields: source_fields
      })

    {{:indexed_type, meta, ctors}, state}
  end

  defp expect_index_list_opener(state, declaration, indices_token) do
    case expect_token(state, :lparen) do
      {:ok, open_token, next_state} ->
        {next_state, open_token}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:indexed_type_syntax,
           %{
             kind: :type_indices_opener_missing,
             declaration: declaration,
             expected: :lparen,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             previous_span: indices_token.span,
             line: observed.line,
             column: observed.col
           }}

        {%{next_state | errors: [error | rest]}, nil}
    end
  end

  # Ordinary ADT / alias body: `type NAME(type_params) = …`.
  defp parse_type_def_adt(state, name, type_params, token, name_token, type_parameter_span) do
    state = skip_newlines(state)

    {pre_assign_block, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state)}
        _ -> {false, state}
      end

    assign_token = if match?(%Token{type: :assign}, peek(state)), do: peek(state)
    state = expect_type_declaration_assign(state, :type, token, name_token, name, type_parameter_span)
    state = skip_newlines(state)

    # v0.21.0: allow the RHS to live inside an indented block so the
    # multi-line ADT layout parses. Track whether we entered a block so
    # we can consume the matching `:dedent` on exit.
    {opened_block, state} =
      case peek(state) do
        %Token{type: :indent} -> {true, advance(state)}
        _ -> {false, state}
      end

    state = skip_newlines(state)

    {ast, state} =
      case {peek(state), peek_at(state, 1)} do
        {%Token{type: :lbrace}, _} ->
          {rhs, state} = parse_refinement_type(state)
          meta = [name: name, line: token.line, col: token.col]
          meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
          {{:type_annotation, meta, [rhs]}, state}

        {%Token{type: :lparen}, %Token{type: :rparen}} ->
          # `type Unit = ()` — the Swift-style unit type: `Unit` is the type, `()`
          # its sole value. `= ()` is RESERVED to `Unit`; `()` names the one
          # built-in unit type and is not a spelling other types may borrow, so
          # any other name declared as `()` is a hard error. When permitted, this
          # builds exactly the nullary single-`unit`-ctor family the compiler
          # seeds into every module (see program.ex seed_with_telescope_support/1).
          unit_span =
            case Range.through(peek(state), peek_at(state, 1)) do
              {:ok, span} -> span
              {:error, _reason} -> peek(state).span
            end

          state = advance(advance(state))

          meta = [container_type: :enum, name: name, line: token.line, col: token.col]
          meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta

          if name == "Unit" do
            variant_meta = Metadata.put_source_info([variant: true], %SourceInfo{whole: unit_span})
            {{:container, meta, [{:variable, variant_meta, "unit"}]}, state}
          else
            state =
              add_error(state, {
                :unit_type_reserved,
                %{
                  name: name,
                  span: name_token.span,
                  unit_span: unit_span,
                  line: name_token.line,
                  column: name_token.col
                }
              })

            {{:container, meta, []}, state}
          end

        {%Token{type: :lparen}, _} ->
          # A function-type (or grouped/tuple) alias RHS: `type Endo = (Nat) -> Nat`.
          # The arrow ladder handles the arrow; the result is a plain type alias
          # (`:type_annotation`).
          #
          # `parse_type_arrow/1`, NOT `parse_type_expr/1`: this branch has no
          # bar-continuation logic of its own, so a stray `|` here is a parse error
          # today. Routing it through the `|`-aware entry point would silently start
          # accepting `type Endo = (Nat) -> Nat | X` as a union-typed alias RHS — a
          # semantics change to this branch. Keep the strict, conservative behaviour.
          {rhs, state} = parse_type_arrow(state)
          meta = [name: name, line: token.line, col: token.col]
          meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
          {{:type_annotation, meta, [rhs]}, state}

        _ ->
          # v0.21.0: accept an optional leading `|` before the first variant.
          {leading_bar_token, state} =
            case peek(state) do
              %Token{type: :bar} = bar_token ->
                s = advance(state)
                {bar_token, skip_newlines(s)}

              _ ->
                {nil, state}
            end

          # `type Empty = |` declares an explicit CONSTRUCTOR-LESS (uninhabited)
          # type. After the leading bar, end-of-declaration — a dedent/eof or the
          # keyword/decorator that starts the next sibling declaration — means there
          # are no variants at all. The leading bar is required so a bare
          # `type Foo =` (a genuinely missing RHS) still errors rather than silently
          # becoming an empty type.
          {ast, state} =
            if leading_bar_token && no_more_variants?(state) do
              meta = [container_type: :enum, name: name, line: token.line, col: token.col]
              meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
              {{:container, meta, []}, state}
            else
              # Parse as ADT variants (A(T) | B | C) or type alias
              {first_variant, state} = parse_type_variant(state)
              state = skip_newlines(state)

              case peek(state) do
                %Token{type: :bar} ->
                  # ADT: multiple variants separated by |
                  {rest_variants, state} = parse_more_variants(state)
                  variants = [first_variant | rest_variants]
                  meta = [container_type: :enum, name: name, line: token.line, col: token.col]
                  meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
                  {{:container, meta, variants}, state}

                _ ->
                  if variant_ctor?(first_variant) do
                    # Single-constructor ADT: `type Box = MkBox(Nat)` is a one-ctor
                    # inductive family, not a type alias. (A constructor variant carries
                    # `variant: true`; a genuine alias RHS — `type Celsius = Int` — is a
                    # plain type expression and stays a `:type_annotation`.)
                    meta = [container_type: :enum, name: name, line: token.line, col: token.col]
                    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
                    {{:container, meta, [first_variant]}, state}
                  else
                    # Type alias: type Name = ExistingType
                    meta = [name: name, line: token.line, col: token.col]
                    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
                    {{:type_annotation, meta, [first_variant]}, state}
                  end
              end
            end

          {put_leading_variant_separator(ast, leading_bar_token), state}
      end

    # An optional `deriving Iface{, Iface}` suffix follows the last variant on
    # the same line, so it must be consumed BEFORE the block-closing dedent.
    {ast, deriving_span, state} = maybe_attach_deriving(ast, state)

    # Close the optional wrapping block by consuming the matching `:dedent`.
    # Surrounding newlines are skipped for us by the caller's own
    # `skip_newlines` but we also tolerate any trailing newline inside the
    # block.
    close_count = layout_block_count(opened_block, pre_assign_block)

    state =
      Enum.reduce(1..close_count//1, state, fn
        _, acc when close_count > 0 -> acc |> skip_newlines() |> expect_dedent()
        _, acc -> acc
      end)

    ast =
      put_type_decl_source_info(
        ast,
        token,
        name_token,
        type_parameter_span,
        assign_token,
        deriving_span
      )

    {ast, state}
  end

  defp put_type_decl_source_info(
         {tag, meta, payload},
         %Token{} = token,
         %Token{} = name_token,
         type_parameter_span,
         assign_token,
         deriving_span
       )
       when is_list(meta) do
    payload_spans = payload |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    annotation_span = if tag == :type_annotation, do: List.first(payload_spans)
    branches = if tag == :container, do: payload_spans, else: []
    existing_info = Metadata.source_info(meta) || %SourceInfo{}

    terminal_span =
      deriving_span || List.last(branches) || annotation_span || existing_info.whole ||
        (assign_token && assign_token.span) || type_parameter_span || name_token.span

    fields =
      existing_info.fields
      |> maybe_put_source_field(:type_parameters, type_parameter_span)
      |> maybe_put_source_field(:separator, assign_token)
      |> maybe_put_source_field(:deriving, deriving_span)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_token.span,
        annotation: annotation_span,
        branches: branches,
        fields: fields
      })

    {tag, meta, payload}
  end

  defp put_leading_variant_separator({tag, meta, payload}, %Token{} = bar_token) when is_list(meta) do
    info = %SourceInfo{whole: bar_token.span, fields: %{leading_separator: bar_token.span}}
    {tag, Metadata.put_source_info(meta, info), payload}
  end

  defp put_leading_variant_separator(ast, _bar_token), do: ast

  defp layout_block_count(opened_block, pre_assign_block) do
    Enum.count([opened_block, pre_assign_block], & &1)
  end

  # `deriving` attaches a list of interface names to a constructor-bearing type
  # (`:container` with `:enum` container_type). Type aliases can't derive, so
  # non-container asts pass through untouched.
  defp maybe_attach_deriving({:container, meta, body}, state) do
    case peek(state) do
      %Token{type: :keyword, value: :deriving} = deriving_token ->
        state = advance(state)
        {names, name_tokens, last_name_token, state} = parse_deriving_names(state, [])
        span = through_spans(deriving_token.span, last_name_token.span) || deriving_token.span

        source_info = Metadata.source_info(meta) || %SourceInfo{}

        fields =
          Enum.reduce(name_tokens, source_info.fields, fn {name, token}, fields ->
            Map.put(fields, {:deriving_interface, name}, token.span)
          end)

        meta =
          meta
          |> Keyword.put(:deriving, names)
          |> Metadata.put_source_info(%{source_info | fields: fields})

        {{:container, meta, body}, span, state}

      _ ->
        {{:container, meta, body}, nil, state}
    end
  end

  defp maybe_attach_deriving(ast, state), do: {ast, nil, state}

  defp parse_deriving_names(state, acc) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    entries = [{name, name_token} | acc]

    case peek(state) do
      %Token{type: :comma} ->
        parse_deriving_names(advance(state), entries)

      _ ->
        entries = Enum.reverse(entries)
        {Enum.map(entries, &elem(&1, 0)), entries, name_token, state}
    end
  end

  defp parse_gadt_ctors(state, acc, family) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      # A `##`/`#` comment still at constructor indent (no intervening `:dedent`, which the
      # clause above would have caught) sits BETWEEN constructors — skip it and continue, so a
      # constructor can be documented in place (E5). A comment that ends the block is preceded
      # by `:dedent` and never reaches here.
      %Token{type: type} when type in [:doc_comment, :line_comment] ->
        parse_gadt_ctors(advance(state), acc, family)

      _ ->
        cname_token = peek(state)
        cname = to_string(cname_token.value)
        state = advance(state)
        {state, colon_token} = expect_gadt_constructor_colon(state, cname_token, family)
        {sig, signature_span, state} = parse_ctor_signature(state)
        meta = [name: cname, line: cname_token.line, col: cname_token.col]

        meta =
          Metadata.put_source_info(meta, %SourceInfo{
            whole: through_spans(cname_token.span, signature_span || cname_token.span) || cname_token.span,
            name: cname_token.span,
            annotation: signature_span,
            fields: maybe_put_source_field(%{}, :separator, colon_token)
          })

        parse_gadt_ctors(state, [{:gadt_ctor, meta, [sig]} | acc], family)
    end
  end

  defp expect_gadt_constructor_colon(state, constructor_token, family) do
    case expect_token(state, :colon) do
      {:ok, colon, next_state} ->
        {next_state, colon}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :gadt_constructor_colon_missing,
             family: family,
             declaration: to_string(constructor_token.value),
             expected: :colon,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             previous_span: constructor_token.span,
             line: observed.line,
             column: observed.col
           }}

        {%{next_state | errors: [error | rest]}, nil}
    end
  end

  # A constructor signature is an arrow chain `Dom -> Dom -> ... -> Result`
  # where each element is a full type application (`SF(as, bs, d1)`). The
  # general `parse_type_expr` is unusable here: its `maybe_parse_function_type`
  # splices a domain application's *arguments* into the arrow's parameter list
  # and discards the head (so `SF(as, bs, d1) -> …` loses `SF`). This dedicated
  # parser keeps each application intact and yields a canonical `:arrow_chain`
  # node with the last atom as the result type.
  defp parse_ctor_signature(state) do
    {first, first_span, state} = parse_ctor_dom(state)
    collect_arrow_chain(state, [first], first_span, first_span)
  end

  defp collect_arrow_chain(state, acc, first_span, last_span) do
    case peek(state) do
      %Token{type: :arrow} ->
        state = advance(state)
        {atom, atom_span, state} = parse_ctor_dom(state)
        collect_arrow_chain(state, [atom | acc], first_span, atom_span || last_span)

      _ ->
        signature_span = through_spans(first_span, last_span) || first_span || last_span

        chain_meta =
          if signature_span do
            Metadata.put_source_info([], %SourceInfo{whole: signature_span})
          else
            []
          end

        {{:arrow_chain, chain_meta, Enum.reverse(acc)}, signature_span, state}
    end
  end

  # A single element of a constructor's arrow chain. Ordinarily a bare type
  # application (`SNat(k)`), but a DOMAIN position may carry a NAMED dependent
  # binder `(name: Type)` — needed when a later argument type or the result
  # index depends on this explicit argument (`(k: Nat) -> SNat(k) -> NVv(S(k))`).
  # The named form yields a canonical `:named_dom` node; everything else
  # falls through to `parse_type_atom` byte-for-byte (unnamed args unchanged).
  defp parse_ctor_dom(state) do
    la2 =
      case peek_at(state, 1) do
        %Token{type: :at} = at -> at
        _ -> peek_at(state, 2)
      end

    case {peek(state), la2} do
      {%Token{type: :lparen}, %Token{type: kind}}
      when kind == :colon or kind == :at ->
        open_token = peek(state)
        state = advance(state)
        {grade_prefix, state} = parse_binder_grade_prefix(state)
        name_token = peek(state)
        name = to_string(name_token.value)
        state = advance(state)

        {grade, state} =
          case grade_prefix do
            {:grade_prefix, prefix_grade, _at_token, _grade_token} ->
              case expect_token(state, :colon) do
                {:ok, _colon, next} -> {prefix_grade, next}
                {:error, next} -> {prefix_grade, next}
              end

            nil ->
              case expect_token(state, :colon) do
                {:ok, _token, next} -> {nil, next}
                {:error, next} -> {nil, next}
              end
          end

        {inner, state} = parse_type_atom(state)

        {state, close_token} =
          expect_container_close(state, :rparen, :named_constructor_domain, open_token, [inner], false, %{
            binder_span: name_token.span
          })

        span = through_spans(open_token.span, close_token && close_token.span) || open_token.span

        meta =
          [name: name, line: open_token.line, col: open_token.col]
          |> then(fn meta -> if grade, do: Keyword.put(meta, :grade, grade), else: meta end)
          |> Metadata.put_source_info(%SourceInfo{
            whole: span,
            name: name_token.span,
            opener: open_token.span,
            closer: close_token && close_token.span
          })

        {{:named_dom, meta, [inner]}, span, state}

      # A RELEVANT IMPLICIT domain `{k: Type}` (Idris `{k : Nat}`): implicit at
      # application/pattern (solved by unification, never positional) but
      # runtime-relevant (quantity ω, retained) — the fourth quadrant Cure's
      # inferred-index (implicit+erased) and explicit-dom (explicit+ω) categories
      # can't spell. Distinguished from a REFINEMENT type `{x: T | P}` (which
      # `parse_type_atom` routes to `parse_refinement_type`) by the ABSENCE of a
      # top-level `|` before the closing `}`: `parse_refinement_type` requires the
      # bar, so a bar-less `{ident: …}` is never a valid refinement here.
      {%Token{type: :lbrace}, %Token{type: kind}}
      when kind == :colon or kind == :at ->
        if implicit_dom_brace?(state) do
          open_token = peek(state)
          state = advance(state)
          {grade_prefix, state} = parse_binder_grade_prefix(state)
          name_token = peek(state)
          name = to_string(name_token.value)
          state = advance(state)

          {grade, state} =
            case grade_prefix do
              {:grade_prefix, prefix_grade, _at_token, _grade_token} ->
                case expect_token(state, :colon) do
                  {:ok, _colon, next} -> {prefix_grade, next}
                  {:error, next} -> {prefix_grade, next}
                end

              nil ->
                case expect_token(state, :colon) do
                  {:ok, _colon, next} -> {nil, next}
                  {:error, next} -> {nil, next}
                end
            end

          {inner, state} = parse_type_atom(state)

          {state, close_token} =
            expect_container_close(state, :rbrace, :implicit_constructor_domain, open_token, [inner], false, %{
              binder_span: name_token.span
            })

          span = through_spans(open_token.span, close_token && close_token.span) || open_token.span

          meta =
            [name: name, line: open_token.line, col: open_token.col]
            |> then(fn meta -> if grade, do: Keyword.put(meta, :grade, grade), else: meta end)
            |> Metadata.put_source_info(%SourceInfo{
              whole: span,
              name: name_token.span,
              opener: open_token.span,
              closer: close_token && close_token.span
            })

          {{:implicit_dom, meta, [inner]}, span, state}
        else
          {atom, state} = parse_type_atom(state)
          {atom, ast_source_span(atom), state}
        end

      _ ->
        {atom, state} = parse_type_atom(state)
        {atom, ast_source_span(atom), state}
    end
  end

  # Peek: does the brace group at `state` (peek == `{`) close WITHOUT a top-level
  # `|`? True → relevant-implicit domain `{k: T}`; false → refinement `{x: T | P}`.
  # Scans from just inside the `{`, tracking nested-brace depth so a `|` inside a
  # nested group doesn't count. A malformed/unterminated group returns true and
  # lets the domain parser surface the error normally.
  defp implicit_dom_brace?(state), do: scan_implicit_dom_brace(state, 1, 0)

  defp scan_implicit_dom_brace(state, offset, depth) do
    case peek_at(state, offset) do
      %Token{type: :lbrace} -> scan_implicit_dom_brace(state, offset + 1, depth + 1)
      %Token{type: :rbrace} when depth == 0 -> true
      %Token{type: :rbrace} -> scan_implicit_dom_brace(state, offset + 1, depth - 1)
      %Token{type: :bar} when depth == 0 -> false
      nil -> true
      _ -> scan_implicit_dom_brace(state, offset + 1, depth)
    end
  end

  # A single type application: `Name`, `Name(arg, ...)`, or `(atom)`.
  defp parse_type_atom(state) do
    token = peek(state)

    case token.type do
      # Constructor result indices use this arrow-free parser rather than the
      # general type-expression ladder. Preserve character terms here as well;
      # otherwise `Witness('a')` becomes the Nat-shaped name "97".
      :char ->
        {literal(:char, token), advance(state)}

      :lbrace ->
        parse_refinement_type(state)

      :lparen ->
        open_token = token
        state = advance(state)
        # Reuse the constructor-domain parser inside the group as well. This
        # admits a named dependent domain in a higher-order field type:
        # `Mk : ((x: A) -> B(x)) -> T`. Previously the general type parser
        # accepted this Π shape while this constructor-only path accepted only
        # anonymous `(A) -> B`, creating two subtly different type grammars.
        {inner, _inner_span, state} = parse_ctor_dom(state)
        # A PARENTHESISED function type (`(A) -> B`, `(A) -> B -> C`) is ONE grouped
        # type — e.g. a higher-order constructor field `MkPid : ((m) -> R) -> Pid(m)`.
        # The closing `)` bounds the arrow chain, so absorbing `->` here is
        # unambiguous, unlike the ctor's own top-level arrow chain (which uses `->`
        # to separate fields from the result index). `parse_type_atom` stays
        # arrow-free everywhere else.
        {inner, state} = parse_paren_arrow_tail(state, inner)

        {state, _close_token} =
          expect_container_close(state, :rparen, :grouped_type, open_token, [inner], false)

        {inner, state}

      _ ->
        name = to_string(token.value)
        state = advance(state)

        case peek(state) do
          %Token{type: :lparen} ->
            open_token = peek(state)
            state = advance(state)
            {args, state} = parse_type_atom_args(state)

            {state, close_token} =
              expect_container_close(state, :rparen, :type_arguments, open_token, args, true, %{type: name})

            meta = [name: name, line: token.line, col: token.col]
            meta = put_type_application_source_info(meta, token, args, close_token)
            {{:function_call, meta, args}, state}

          _ ->
            {type_variable(token), state}
        end
    end
  end

  # Inside a `(...)` group only: if an `->` follows the first atom, collect the
  # whole arrow chain `A -> B -> …  -> Ret` into the same `Function` node
  # `parse_type_arrow` produces, so a parenthesised function type is one grouped
  # type. Absent an arrow this is the identity (a plain parenthesised type).
  defp parse_paren_arrow_tail(state, first) do
    case peek(state) do
      %Token{type: :arrow} ->
        {parts, state} = collect_paren_arrow(state, [first])
        {paren_arrow_ast(parts), state}

      _ ->
        {first, state}
    end
  end

  defp collect_paren_arrow(state, acc) do
    case peek(state) do
      %Token{type: :arrow} ->
        state = advance(state)
        {atom, _atom_span, state} = parse_ctor_dom(state)
        collect_paren_arrow(state, [atom | acc])

      _ ->
        {Enum.reverse(acc), state}
    end
  end

  defp paren_arrow_ast(parts) do
    {domains, [ret]} = Enum.split(parts, length(parts) - 1)

    if Enum.any?(domains, &match?({:named_dom, _, _}, &1)) do
      binders =
        Enum.map(domains, fn
          {:named_dom, meta, _} -> Keyword.fetch!(meta, :name)
          _ -> nil
        end)

      doms =
        Enum.map(domains, fn
          {:named_dom, _meta, [inner]} -> inner
          other -> other
        end)

      {:pi_type, [binders: binders], doms ++ [ret]}
    else
      {:function_call, [name: "Function", function_type: true], parts}
    end
  end

  defp parse_type_atom_args(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} -> {[], state}
      _ -> parse_type_atom_args_list(state)
    end
  end

  defp parse_type_atom_args_list(state) do
    {arg, state} = parse_type_app_arg(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_type_atom_args_list(state)
        {[arg | rest], state}

      _ ->
        {[arg], state}
    end
  end

  # A type-application argument is normally a type (`Vector(a, Z)`). But a
  # decidable-boolean reflection type such as `IsTrue(claim: Bool)` is applied to
  # a *proposition* — a comparison or boolean-connective expression: `IsTrue(5 > 0)`,
  # `IsTrue(0 <= p and p <= 100)`. Comparison/boolean operators never legitimately
  # follow a type in ordinary type syntax (arrows use `->`, Cure has no angle-bracket
  # generics), so a trailing one is an unambiguous signal that this argument is a
  # proposition.
  defp parse_type_app_arg(state), do: parse_type_or_proposition(state, &parse_type_atom/1)

  # Parse a type-position argument with `parse_fun`; if a comparison/boolean operator
  # immediately follows, the argument is actually a proposition, so reparse it from the
  # original state with the full expression parser. That yields the same `{:binary_op, ...}`
  # node an expression would, which the index elaborator routes through the type-directed
  # term elaborator (so its literals get the right primitive type and the spine folds).
  @type_prop_ops [:eq, :neq, :lt, :gt, :lte, :gte, :and_op, :or_op]
  defp parse_type_or_proposition(state, parse_fun) do
    {parsed, after_state} = parse_fun.(state)

    case peek(after_state) do
      %Token{type: t} when t in @type_prop_ops -> parse_expr(state, 0)
      _ -> {parsed, after_state}
    end
  end

  # A parsed type-body variant that is genuinely a constructor (has fields, so it
  # carries `variant: true`) rather than a type-alias RHS.
  defp variant_ctor?({:function_def, meta, _}), do: Keyword.get(meta, :variant, false)
  defp variant_ctor?(_), do: false

  # True when the parser is positioned at end-of-declaration rather than at a
  # constructor variant: a closing dedent/eof, the keyword/decorator that begins
  # the next sibling declaration, or a comment (a doc/line comment can never
  # start a variant — it belongs to the following declaration). Used to recognise
  # the constructor-less `type Empty = |` form. Omitting the comment tokens here
  # let a `## doc` on the *next* declaration be mis-parsed as a variant of the
  # empty type, silently turning `type Empty = |` into `type Empty = <docword>`.
  defp no_more_variants?(state) do
    case peek(state) do
      %Token{type: t} when t in [:dedent, :eof, :keyword, :at, :doc_comment, :line_comment] -> true
      _ -> false
    end
  end

  defp parse_type_variant(state) do
    name_token = peek(state)
    name = to_string(name_token.value)

    # A DOTTED name in variant position is never a constructor being declared —
    # a declaration introduces an unqualified name into this module. It is a
    # qualified reference to someone else's type, so `type T = Other.Mod.F(T)`
    # is an alias RHS and belongs to the type-expression parser. Reading only the
    # first segment here left `.Mod.F(T)` behind, and the declaration was
    # discarded entirely: the module's dependency on `Other.Mod` disappeared, and
    # the manifest reported a missing module named after the middle segment
    # instead of the compile-time cycle that is actually there.
    if match?(%Token{type: :dot}, peek_at(state, 1)) do
      parse_type_expr(state)
    else
      parse_type_variant_named(advance(state), name_token, name)
    end
  end

  defp parse_type_variant_named(state, name_token, name) do
    case peek(state) do
      %Token{type: :lparen} ->
        # Constructor with params: Some(T)
        open_token = peek(state)
        state = advance(state)
        {params, state} = parse_type_param_list(state)

        {state, close_token} =
          expect_container_close(state, :rparen, :constructor_parameters, open_token, params, true, %{
            constructor: name
          })

        variant_meta =
          [name: name, params: params, variant: true]
          |> put_token_source_info(name_token, :name)
          |> extend_source_info_whole(close_token)

        ast = {:function_def, variant_meta, []}
        {ast, state}

      _ ->
        # Nullary constructor: None
        {{:variable, put_token_source_info([variant: true], name_token, :name), name}, state}
    end
  end

  # v0.21.0: skip any newlines before peeking for the next `|` so multi-line
  # ADT declarations parse identically to their single-line counterparts.
  defp parse_more_variants(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :bar} ->
        state = advance(state)
        state = skip_newlines(state)
        {variant, state} = parse_type_variant(state)
        state = skip_newlines(state)
        {rest, state} = parse_more_variants(state)
        {[variant | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_type_param_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {t, state} = parse_type_or_proposition(state, &parse_type_expr/1)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_type_param_list(state)
            {[t | rest], state}

          _ ->
            {[t], state}
        end
    end
  end

  # Like `parse_type_param_list`, but each element may carry an optional binder
  # name (`x: A`). Used only for a standalone parenthesised type that may become a
  # dependent function type `(x: A) -> …`. Returns `{binder | nil, type_ast}`
  # pairs so the caller can build a dependent Π (binders present) or the existing
  # non-dependent arrow (all binders nil).
  defp parse_paren_type_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {binder, state} = parse_optional_binder(state)
        {t, state} = parse_type_expr(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_paren_type_list(state)
            {[{binder, t} | rest], state}

          _ ->
            {[{binder, t}], state}
        end
    end
  end

  # An optional `name :` binder prefix inside a parenthesised arrow domain. Only
  # consumes when an identifier is immediately followed by `:` — so `(N)` stays a
  # plain domain while `(n: N)` binds `n`. (A type element in this position is
  # never otherwise followed by `:`.)
  defp parse_optional_binder(state) do
    case {peek(state), peek(advance(state))} do
      {%Token{type: :identifier, value: v}, %Token{type: :colon}} ->
        {to_string(v), advance(advance(state))}

      _ ->
        {nil, state}
    end
  end

  # -- Protocol  proto Name(T) -----------------------------------------------

  defp parse_proto(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Type params: (T) or (T, U)
    {type_params, type_parameter_spans, type_parameter_span, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          open_token = peek(state)
          state = advance(state)
          {tp, tp_spans, state} = parse_name_list_with_spans(state, :rparen)

          {state, close_token} =
            expect_container_close(state, :rparen, :type_parameters, open_token, tp, true, %{
              declaration: name,
              declaration_kind: :protocol
            })

          span = through_spans(open_token.span, close_token && close_token.span) || open_token.span
          {tp, tp_spans, span, state}

        _ ->
          {[], [], nil, state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    meta = [
      container_type: :protocol,
      name: name,
      type_params: type_params,
      line: token.line,
      col: token.col
    ]

    branches = body |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    terminal_span = List.last(branches) || type_parameter_span || name_token.span
    source_fields = if type_parameter_span, do: %{type_parameters: type_parameter_span}, else: %{}

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_token.span,
        arguments: type_parameter_spans,
        branches: branches,
        fields: source_fields
      })

    ast = {:container, meta, body}
    {ast, state}
  end

  # -- Implementation  impl Proto for Type -----------------------------------

  defp parse_impl(state) do
    token = peek(state)
    state = advance(state)

    # Protocol name
    proto_start = peek(state)
    {proto_name, proto_end, state} = parse_dotted_name_owned(state)

    protocol_span = through_spans(proto_start.span, proto_end.span) || proto_start.span
    {for_token, state} = expect_implementation_for(state, token, protocol_span, proto_name, :protocol)

    # Type being implemented
    {for_type, state} = parse_type_expr(state)

    # Optional implementation requirements.
    requirements_token = peek(state)
    {constraints, state} = parse_requirements_clause(state)

    requirements_span =
      case constraints |> List.last() |> ast_source_span() do
        %Cure.Diagnostic.Span{} = last -> through_spans(requirements_token.span, last)
        _ -> nil
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    for_name =
      case for_type do
        {:variable, _, n} -> n
        {:function_call, m, _} -> Keyword.get(m, :name, "unknown")
        _ -> "unknown"
      end

    meta = [
      container_type: :trait,
      name: "#{proto_name}.#{for_name}",
      protocol: proto_name,
      for: for_name,
      for_type: for_type,
      line: token.line,
      col: token.col
    ]

    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta

    for_type_span = ast_source_span(for_type)
    branches = body |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    terminal_span = List.last(branches) || requirements_span || for_type_span || protocol_span

    source_fields =
      %{}
      |> maybe_put_source_field(:for_keyword, for_token)
      |> maybe_put_source_field(:for_type, for_type_span)
      |> maybe_put_source_field(:requirements, requirements_span)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: protocol_span,
        annotation: for_type_span,
        branches: branches,
        fields: source_fields
      })

    ast = {:container, meta, body}
    {ast, state}
  end

  # -- Interface  interface Name(a) ------------------------------------------
  #
  # Compile-time typeclass declaration (the successor to `proto`). The head
  # params are the type/higher-kinded variables the interface is indexed by
  # (`interface Functor(f)`). The body is a definition block of method
  # signatures; any method that carries a `= body` is a DEFAULT, captured
  # separately in `meta[:defaults]` (name → body expr) so the elaborator can
  # fill it into implementations that omit the method. The full body list is
  # returned as the node's methods (each a `{:function_def, meta, exprs}`,
  # `exprs == []` for a bare signature).
  defp parse_interface(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {params, type_parameter_spans, type_parameter_span, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          open_token = peek(state)
          state = advance(state)
          {tp, tp_spans, state} = parse_name_list_with_spans(state, :rparen)

          {state, close_token} =
            expect_container_close(state, :rparen, :type_parameters, open_token, tp, true, %{
              declaration: name,
              declaration_kind: :interface
            })

          span = through_spans(open_token.span, close_token && close_token.span) || open_token.span
          {tp, tp_spans, span, state}

        _ ->
          {[], [], nil, state}
      end

    # `requires` is a CONTEXTUAL keyword: it lexes as an ordinary identifier and
    # is promoted only here, right after the interface param list, so existing
    # code using `requires` as an identifier is unaffected. The clause names the
    # superinterfaces this interface extends (`interface Big(t) requires Small(t)`)
    # — every `implementation Big for T` must then already have an `implementation
    # Small for T`. We reuse the constraint parser and keep only the interface
    # names (the descriptor does not need the type variables).
    {requires, requires_span, state} =
      case peek(state) do
        %Token{type: :identifier, value: "requires"} = requires_token ->
          state = advance(state)
          {constraints, state} = parse_constraint_list(state)
          last_span = constraints |> List.last() |> ast_source_span()
          span = through_spans(requires_token.span, last_span) || requires_token.span
          {superinterface_names(constraints), span, state}

        _ ->
          {[], nil, state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    defaults =
      body
      |> Enum.flat_map(fn
        {:function_def, m, [expr | _]} -> [{Keyword.get(m, :name), expr}]
        _ -> []
      end)
      |> Map.new()

    meta = [
      name: name,
      params: params,
      requires: requires,
      defaults: defaults,
      line: token.line,
      col: token.col
    ]

    branches = body |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    terminal_span = List.last(branches) || requires_span || type_parameter_span || name_token.span

    source_fields =
      %{}
      |> maybe_put_source_field(:type_parameters, type_parameter_span)
      |> maybe_put_source_field(:requires, requires_span)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_token.span,
        arguments: type_parameter_spans,
        branches: branches,
        fields: source_fields
      })

    {{:interface, meta, body}, state}
  end

  # Extract the interface names from a parsed constraint list (`Small(t)` →
  # `"Small"`), dropping the type variables the descriptor does not need.
  defp superinterface_names(constraints) do
    Enum.map(constraints, fn
      {:function_call, m, _args} -> Keyword.get(m, :name)
      {:variable, _m, name} -> name
    end)
  end

  # -- Implementation  implementation Iface for Type [as Name] ----------------
  #
  # An instance of an interface for a concrete head type. `as Name` marks a
  # NAMED implementation (selectable explicitly, exempt from global coherence);
  # its absence is an anonymous instance keyed on `(interface, head ctor)`.
  defp parse_implementation(state) do
    token = peek(state)
    state = advance(state)

    iface_start = peek(state)
    {iface_name, iface_end, state} = parse_dotted_name_owned(state)

    interface_span = through_spans(iface_start.span, iface_end.span) || iface_start.span
    {for_token, state} = expect_implementation_for(state, token, interface_span, iface_name, :interface)

    {for_type, state} = parse_type_expr(state)

    {as_name, as_keyword_token, as_name_token, state} =
      case peek(state) do
        %Token{type: :keyword, value: :as} = as_keyword_token ->
          s = advance(state)
          as_token = peek(s)
          {to_string(as_token.value), as_keyword_token, as_token, advance(s)}

        _ ->
          {nil, nil, nil, state}
      end

    requirements_token = peek(state)
    {constraints, state} = parse_requirements_clause(state)

    requirements_span =
      case constraints |> List.last() |> ast_source_span() do
        %Cure.Diagnostic.Span{} = last -> through_spans(requirements_token.span, last)
        _ -> nil
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    for_name =
      case for_type do
        {:variable, _, n} -> n
        {:function_call, m, _} -> Keyword.get(m, :name, "unknown")
        _ -> "unknown"
      end

    meta = [
      interface: iface_name,
      for: for_name,
      for_type: for_type,
      as: as_name,
      line: token.line,
      col: token.col
    ]

    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta

    for_type_span = ast_source_span(for_type)
    branches = body |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)

    terminal_span =
      List.last(branches) || requirements_span || (as_name_token && as_name_token.span) || for_type_span ||
        interface_span

    source_fields =
      %{}
      |> maybe_put_source_field(:for_keyword, for_token)
      |> maybe_put_source_field(:for_type, for_type_span)
      |> maybe_put_source_field(:as_keyword, as_keyword_token)
      |> maybe_put_source_field(:as_name, as_name_token)
      |> maybe_put_source_field(:requirements, requirements_span)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: interface_span,
        annotation: for_type_span,
        branches: branches,
        fields: source_fields
      })

    {{:implementation, meta, body}, state}
  end

  # -- Import  use Path.{items} [as Alias] -----------------------------------

  defp parse_use(state, opts \\ []) do
    token = peek(state)
    state = advance(state)

    # Parse module path
    path_start = peek(state)
    {path, path_end, state} = parse_dotted_name_owned(state)

    # Check for selective import: .{a, b, c}
    {items, selection_span, state} =
      case peek(state) do
        %Token{type: :dot} ->
          next = peek_at(state, 1)

          if next && next.type == :lbrace do
            open_token = next
            state = advance(state) |> advance()
            {names, state} = parse_name_list(state, :rbrace)

            {state, close_token} =
              expect_container_close(state, :rbrace, :selective_import, open_token, names, true, %{
                module: path,
                closing_values: [:as]
              })

            {names, through_spans(open_token.span, close_token && close_token.span) || open_token.span, state}
          else
            {[], nil, state}
          end

        _ ->
          {[], nil, state}
      end

    # Check for alias: as Name
    {alias_name, as_token, alias_token, state} =
      case peek(state) do
        %Token{type: :keyword, value: :as} = as_token ->
          state = advance(state)
          a = peek(state)
          state = advance(state)
          {to_string(a.value), as_token, a, state}

        _ ->
          {nil, nil, nil, state}
      end

    meta = [source: path, import_type: :use, language: :cure, line: token.line, col: token.col]
    meta = if Keyword.get(opts, :public?, false), do: Keyword.put(meta, :public, true), else: meta
    meta = if items != [], do: Keyword.put(meta, :items, items), else: meta
    meta = if alias_name, do: Keyword.put(meta, :alias, alias_name), else: meta
    terminal_span = (alias_token && alias_token.span) || selection_span || path_end.span

    fields =
      %{}
      |> maybe_put_source_field(:alias_keyword, as_token)
      |> maybe_put_source_field(:alias, alias_token)
      |> then(fn fields -> if selection_span, do: Map.put(fields, :selection, selection_span), else: fields end)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: through_spans(path_start.span, path_end.span) || path_start.span,
        fields: fields
      })

    ast = {:import, meta, []}
    {ast, state}
  end

  # -- macro-produced lifted module ------------------------------------------

  # -- macro container (SP1) --------------------------------------------------
  # `macro Name` … indented `syntax`/`literal` rules. Soft-keyword; closes by
  # dedent (no `end`) and emits a {:macro_def, ...} AST node.
  defp parse_macro_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {leading_segments, leading_segment_span, state} = parse_rule_segments(state, [])
    state = skip_macro_trivia(state)
    {rules, state} = parse_macro_block(state, token)

    state =
      case MacroFamily.validate(rules) do
        :ok ->
          state

        {:error, reason} ->
          details = macro_family_error_details(reason, rules, state, token)
          add_error(state, {:invalid_macro_family, details})
      end

    meta = [name: name, leading_segments: leading_segments, line: token.line, col: token.col]
    rule_spans = rules |> Enum.map(&Map.get(&1, :source_span)) |> Enum.reject(&is_nil/1)
    terminal_span = List.last(rule_spans) || leading_segment_span || name_token.span

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_token.span,
        branches: rule_spans
      })

    {{:macro_def, meta, rules}, state}
  end

  defp macro_family_error_details(reason, rules, state, token) do
    families = Enum.filter(rules, &(&1[:kind] == :syntax_family))

    {span, related_spans} =
      case reason do
        {:unknown_syntax_family, name} ->
          include =
            Enum.find_value(families, fn family ->
              Enum.find(family.includes, fn
                {include_name, _line, _col} -> include_name == name
                _ -> false
              end)
            end)

          case include do
            {^name, line, _col} -> {token_span_on_line(state, line, name) || token.span, []}
            _ -> {token.span, []}
          end

        {:syntax_family_cycle, names} ->
          spans =
            names
            |> Enum.uniq()
            |> Enum.flat_map(fn name ->
              case Enum.find(families, &(&1.name == name)) do
                %{source_span: %Cure.Diagnostic.Span{} = span} -> [span]
                _ -> []
              end
            end)

          {List.first(spans) || token.span, Enum.drop(spans, 1)}

        {:duplicate_syntax_family_field, pairs} ->
          spans =
            Enum.flat_map(pairs, fn {family_name, field_name} ->
              case Enum.find(families, &(&1.name == family_name)) do
                %{fields: fields} ->
                  fields
                  |> Enum.filter(&(&1.name == field_name))
                  |> Enum.flat_map(fn
                    %{source_span: %Cure.Diagnostic.Span{} = span} -> [span]
                    _ -> []
                  end)

                _ ->
                  []
              end
            end)

          {List.last(spans) || token.span, spans |> Enum.drop(-1)}

        {:duplicate_syntax_family, names} ->
          spans =
            families
            |> Enum.filter(&(&1.name in names))
            |> Enum.map(&(Map.get(&1, :name_span) || Map.get(&1, :source_span)))
            |> Enum.reject(&is_nil/1)

          {List.last(spans) || token.span, Enum.drop(spans, -1)}

        reason
        when reason in [
               :accepts_without_syntax_family,
               :accepts_without_expander,
               :multiple_accepts_declarations
             ] ->
          spans =
            rules
            |> Enum.filter(&(&1[:kind] == :accepts))
            |> Enum.map(&(Map.get(&1, :name_span) || Map.get(&1, :source_span)))
            |> Enum.reject(&is_nil/1)

          {List.last(spans) || token.span, Enum.drop(spans, -1)}

        reason when reason in [:expander_without_accepts, :multiple_expands_declarations] ->
          spans =
            rules
            |> Enum.filter(&(&1[:kind] == :expands_with))
            |> Enum.map(&Map.get(&1, :source_span))
            |> Enum.reject(&is_nil/1)

          {List.last(spans) || token.span, Enum.drop(spans, -1)}

        _ ->
          {token.span, []}
      end

    %{
      reason: reason,
      span: span,
      related_spans: related_spans,
      line: (span && span.start_line) || token.line,
      column: (span && span.start_column) || token.col
    }
  end

  defp token_span_on_line(state, line, value) do
    tokens = if is_tuple(state.tokens), do: Tuple.to_list(state.tokens), else: state.tokens

    Enum.find_value(tokens, fn
      %Token{line: ^line, value: token_value, span: %Cure.Diagnostic.Span{} = span} ->
        if to_string(token_value) == to_string(value), do: span

      _ ->
        nil
    end)
  end

  defp macro_rule_source_span(%Token{span: %Cure.Diagnostic.Span{} = first}, %Cure.Diagnostic.Span{} = last),
    do: through_spans(first, last) || first

  defp macro_rule_source_span(%Token{span: %Cure.Diagnostic.Span{} = first}, _last), do: first
  defp macro_rule_source_span(_token, _last), do: nil

  # Pure surface representation for §14's `lift module` value. The resulting
  # node contains quoted callback bodies and declarations; the generic module
  # collector validates and emits it later, with the compiler as the only
  # code-loading boundary.
  defp parse_lift_module(state, token) do
    state = advance(state)
    state = advance(state)
    name_token = peek(state)
    {name, name_end_token, state} = parse_dotted_name_owned(state)

    name =
      case macro_module_marker(name) do
        {:single, hole} -> {:macro_hole, hole}
        {:path, prefix, hole} -> {:macro_path_hole, prefix, hole}
        :none -> name
      end

    state = skip_newlines(state)

    {behaviour, behaviour_span, callbacks, declarations, state} =
      case peek(state) do
        %Token{type: :indent} ->
          parse_lift_module_block(advance(state), nil, nil, [], [])

        _ ->
          {nil, nil, [], [], state}
      end

    source_provenance = %{file: state.file, line: token.line, col: token.col}

    meta = [
      module: name,
      behaviour: behaviour,
      callbacks: callbacks,
      declarations: declarations,
      line: token.line,
      col: token.col
    ]

    name_span = through_spans(name_token.span, name_end_token.span) || name_token.span

    branch_spans =
      (Enum.map(callbacks, &Map.get(&1, :source_span)) ++ Enum.map(declarations, &ast_source_span/1))
      |> Enum.reject(&is_nil/1)
      |> Enum.sort_by(& &1.start_byte)

    terminal_span =
      [behaviour_span | branch_spans]
      |> Enum.reject(&is_nil/1)
      |> Enum.max_by(& &1.end_byte, fn -> name_span end)

    meta =
      Metadata.put_source_info(meta, %SourceInfo{
        whole: through_spans(token.span, terminal_span) || token.span,
        opener: token.span,
        name: name_span,
        branches: branch_spans,
        fields: maybe_put_source_field(%{}, :behaviour, behaviour_span)
      })
      |> Keyword.put(:source_provenance, source_provenance)

    {{:lift_module, meta, []}, state}
  end

  # A lower-case single-segment name in a macro template is a substituted
  # identifier hole (`lift module name`). Ordinary lifted modules require a
  # validated `Cure.X` name, so this marker cannot collide with a valid source
  # module name and keeps the hole visible until macro substitution.
  defp macro_module_marker(name) when is_binary(name) do
    case String.split(name, ".") do
      [hole] ->
        if Regex.match?(~r/^[a-z][A-Za-z0-9_]*$/, hole), do: {:single, hole}, else: :none

      segments when length(segments) > 1 ->
        hole = List.last(segments)

        if hole =~ ~r/^[a-z][A-Za-z0-9_]*$/,
          do: {:path, Enum.drop(segments, -1) |> Enum.join("."), hole},
          else: :none

      _ ->
        :none
    end
  end

  defp macro_module_marker(_name), do: :none

  defp parse_lift_module_block(state, behaviour, behaviour_span, callbacks, declarations) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :dedent} ->
        {behaviour, behaviour_span, Enum.reverse(callbacks), Enum.reverse(declarations), advance(state)}

      %Token{type: :eof} ->
        {behaviour, behaviour_span, Enum.reverse(callbacks), Enum.reverse(declarations), state}

      %Token{type: :identifier, value: "behaviour"} = behaviour_keyword ->
        state = advance(state)
        behaviour_token = peek(state)
        behaviour = String.to_atom(to_string(behaviour_token.value))
        span = through_spans(behaviour_keyword.span, behaviour_token.span) || behaviour_keyword.span
        parse_lift_module_block(advance(state), behaviour, span, callbacks, declarations)

      %Token{type: :identifier, value: "callback"} ->
        {callback, state} = parse_lift_callback(state, behaviour)
        parse_lift_module_block(state, behaviour, behaviour_span, [callback | callbacks], declarations)

      _ ->
        {declaration, state} = parse_expr_or_block(state)
        parse_lift_module_block(state, behaviour, behaviour_span, callbacks, [declaration | declarations])
    end
  end

  defp parse_lift_callback(state, behaviour) do
    token = peek(state)
    state = advance(state)
    name_token = peek(state)
    name = String.to_atom(to_string(name_token.value))
    state = advance(state)

    {params, parameter_span, state} =
      parse_macro_typed_parameters(state, token, name_token, :lift_callback_parameters, name)

    {return_type, returns_token, state} =
      case peek(state) do
        %Token{type: :identifier, value: "returns"} = returns_token ->
          {return_type, state} = parse_type_expr(advance(state))
          {return_type, returns_token, state}

        _ ->
          {nil, nil, state}
      end

    {separator_token, state} = expect_lift_callback_body_separator(state, token, name_token, name, return_type)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    parameter_spans = params |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
    body_span = ast_source_span(body)

    source_info = %SourceInfo{
      whole: through_spans(token.span, body_span || name_token.span) || token.span,
      opener: token.span,
      name: name_token.span,
      arguments: parameter_spans,
      annotation: ast_source_span(return_type),
      operator: separator_token && separator_token.span,
      body: body_span,
      fields:
        %{}
        |> maybe_put_source_field(:parameters, parameter_span)
        |> maybe_put_source_field(:returns, returns_token)
    }

    callback = %{
      name: name,
      arity: length(params),
      params: params,
      return_type: return_type,
      body: body,
      source_span: source_info.whole,
      source_info: source_info,
      line: token.line,
      callback_context: %{
        behaviour: behaviour,
        callback: name,
        arity: length(params),
        parameter_names: Enum.map(params, fn {:param, _, parameter} -> parameter end),
        parameter_types:
          Enum.map(params, fn {:param, parameter_meta, _parameter} ->
            Keyword.get(parameter_meta, :type)
          end),
        return_annotation: if(return_type, do: :declared, else: :inferred),
        return_type: return_type
      }
    }

    {callback, state}
  end

  defp expect_lift_callback_body_separator(state, callback_token, name_token, name, return_type) do
    expected = if return_type, do: :assign, else: :arrow

    case expect_token(state, expected) do
      {:ok, separator, next_state} ->
        {separator, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :lift_callback_body_separator_missing,
             declaration: name,
             annotated: not is_nil(return_type),
             expected: expected,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: callback_token.span,
             previous_span: first_node_source_span(return_type) || name_token.span,
             name_span: name_token.span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp parse_macro_block(state, macro_token) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {rules, state} = parse_macro_rules(state, [], macro_token)
        state = expect_dedent(state)
        {rules, state}

      _ ->
        {[], state}
    end
  end

  # `##`/`###` doc-comments are ALWAYS emitted as `:doc_comment` tokens
  # (independent of `preserve_comments`; see Lexer moduledoc), and plain `#`
  # comments surface as `:line_comment` tokens whenever the caller sets
  # `preserve_comments: true` (e.g. the source formatter). Neither is captured
  # as a rule-attached AST node in this milestone — they are trivia here — but
  # they MUST be skipped rather than mistaken for the end of the macro's
  # indented block (would silently empty it) or for a malformed rule line
  # (would raise a spurious :expected/:syntax_rule error).
  defp skip_macro_trivia(state) do
    case peek(state) do
      %Token{type: :newline} -> skip_macro_trivia(advance(state))
      %Token{type: :doc_comment} -> skip_macro_trivia(advance(state))
      %Token{type: :line_comment} -> skip_macro_trivia(advance(state))
      _ -> state
    end
  end

  defp parse_macro_rules(state, acc, macro_token) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :identifier, value: "syntax"} ->
        {rule, state} =
          case peek_at(state, 1) do
            %Token{type: :identifier, value: "family"} -> parse_syntax_family(state)
            _ -> parse_macro_rule(state)
          end

        parse_macro_rules(state, [rule | acc], macro_token)

      %Token{type: :identifier, value: "accepts"} ->
        {entry, state} = parse_macro_accepts(state)
        parse_macro_rules(state, [entry | acc], macro_token)

      %Token{type: :identifier, value: "expands"} ->
        {entry, state} = parse_macro_expands_with(state)
        parse_macro_rules(state, [entry | acc], macro_token)

      %Token{type: :identifier, value: "literal"} ->
        {rule, state} = parse_literal_rule(state)
        parse_macro_rules(state, [rule | acc], macro_token)

      %Token{type: :identifier, value: "explain"} ->
        {entry, state} = parse_explain_block(state)
        parse_macro_rules(state, [entry | acc], macro_token)

      %Token{type: :identifier, value: "fail"} ->
        {entry, state} = parse_fail_declaration(state)
        parse_macro_rules(state, [entry | acc], macro_token)

      %Token{type: :identifier, value: "open"} ->
        {entry, state} = parse_open_category(state)
        parse_macro_rules(state, [entry | acc], macro_token)

      observed ->
        state =
          add_error(
            state,
            {:syntax_family_definition_syntax,
             %{
               kind: :macro_definition_entry_invalid,
               expected: :syntax,
               alternatives: [:accepts, :expands, :literal, :explain, :fail, :open],
               observed: macro_separator_observed(observed),
               token_type: observed.type,
               span: observed.span,
               opener_span: macro_token.span,
               previous_span: previous_authored_span(state, macro_token.span),
               line: observed.line,
               column: observed.col
             }}
          )

        # Recover: skip a token so one bad line does not eat the block.
        parse_macro_rules(advance(state), acc, macro_token)
    end
  end

  defp parse_macro_accepts(state) do
    token = peek(state)
    state = advance(state)
    family_start = peek(state)
    {family, family_end, state} = parse_dotted_name_owned(state)
    family_span = through_spans(family_start.span, family_end.span) || family_start.span

    {%{
       kind: :accepts,
       family: family,
       name_span: family_span,
       line: token.line,
       col: token.col,
       source_span: macro_rule_source_span(token, family_span)
     }, state}
  end

  defp parse_macro_expands_with(state) do
    token = peek(state)
    state = advance(state)
    state = expect_macro_rule_keyword(state, :with, :macro_expands_with_missing, token)

    {expander, state} = parse_expr(state, 0)

    {%{
       kind: :expands_with,
       expander: expander,
       line: token.line,
       col: token.col,
       source_span: macro_rule_source_span(token, ast_source_span(expander))
     }, state}
  end

  defp parse_syntax_family(state) do
    syntax_token = peek(state)
    family_token = peek_at(state, 1)
    state = advance(state)
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)
    state = skip_macro_trivia(state)

    family_context = %{
      family: name,
      opener_span: syntax_token.span,
      family_keyword_span: family_token.span,
      name_span: name_token.span
    }

    case peek(state) do
      %Token{type: :indent} ->
        {fields, includes, productions, include_spans, state} =
          parse_syntax_family_fields(advance(state), [], [], [], [], family_context)

        state = expect_dedent(state)

        child_spans =
          (Enum.map(fields, & &1.source_span) ++ Enum.map(productions, & &1.source_span) ++ include_spans)
          |> Enum.reject(&is_nil/1)
          |> Enum.sort_by(& &1.start_byte)

        terminal_span = List.last(child_spans) || name_token.span

        {%{
           kind: :syntax_family,
           name: name,
           name_span: name_token.span,
           fields: fields,
           includes: includes,
           productions: productions,
           line: family_token.line,
           col: family_token.col,
           source_span: macro_rule_source_span(syntax_token, terminal_span)
         }, state}

      observed ->
        state =
          add_error(
            state,
            {:syntax_family_definition_syntax,
             Map.merge(family_context, %{
               kind: :syntax_family_indent_missing,
               expected: :indent,
               observed: macro_separator_observed(observed),
               token_type: observed.type,
               span: zero_width_start(observed.span),
               observed_span: observed.span,
               previous_span: name_token.span,
               line: observed.line,
               column: observed.col
             })}
          )

        {%{
           kind: :syntax_family,
           name: name,
           name_span: name_token.span,
           fields: [],
           line: family_token.line,
           col: family_token.col,
           source_span: macro_rule_source_span(syntax_token, name_token.span)
         }, state}
    end
  end

  defp parse_syntax_family_fields(state, fields, includes, productions, include_spans, family_context) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(fields), Enum.reverse(includes), Enum.reverse(productions), Enum.reverse(include_spans), state}

      %Token{type: :identifier, value: "syntax"} = token ->
        {segments, segment_span, state} = parse_rule_segments(advance(state), [])
        state = consume_line_end(state)

        production = %{
          kind: :family_production,
          segments: segments,
          fields: macro_syntax_fields(segments),
          field_types: macro_syntax_field_types(segments),
          line: token.line,
          col: token.col,
          source_span: macro_rule_source_span(token, segment_span || token.span)
        }

        parse_syntax_family_fields(state, fields, includes, [production | productions], include_spans, family_context)

      %Token{type: :identifier, value: "includes"} = token ->
        include_start = peek(advance(state))
        {include, include_end, state} = parse_dotted_name_owned(advance(state))
        include_span = through_spans(token.span, include_end.span) || token.span
        state = consume_line_end(state)

        parse_syntax_family_fields(
          state,
          fields,
          [{include, token.line, token.col} | includes],
          productions,
          [include_span || include_start.span | include_spans],
          family_context
        )

      %Token{type: :identifier} = token ->
        {cardinality, state} = parse_family_cardinality(state)
        field_token = peek(state)
        field = to_string(field_token.value)
        state = advance(state)
        shape_token = peek(state)
        shape = to_string(shape_token.value)
        state = advance(state)
        {obligations, state} = parse_capture_obligations(state, [field])
        state = consume_line_end(state)
        terminal_span = obligations |> List.last() |> then(&(&1 && &1.source_span)) || shape_token.span

        field_entry = %{
          kind: :family_field,
          name: field,
          shape: shape,
          obligations: obligations,
          cardinality: cardinality,
          line: token.line,
          col: token.col,
          source_span: macro_rule_source_span(token, terminal_span)
        }

        parse_syntax_family_fields(
          state,
          [field_entry | fields],
          includes,
          productions,
          include_spans,
          family_context
        )

      observed ->
        state =
          add_error(
            state,
            {:syntax_family_definition_syntax,
             Map.merge(family_context, %{
               kind: :syntax_family_member_invalid,
               expected: :family_field,
               alternatives: [:includes, :syntax],
               observed: macro_separator_observed(observed),
               token_type: observed.type,
               span: observed.span,
               previous_span: previous_authored_span(state, family_context.name_span),
               line: observed.line,
               column: observed.col
             })}
          )

        parse_syntax_family_fields(
          advance(state),
          fields,
          includes,
          productions,
          include_spans,
          family_context
        )
    end
  end

  defp parse_family_cardinality(state) do
    case peek(state) do
      %Token{type: :identifier, value: "optional"} -> {:optional, advance(state)}
      %Token{type: :identifier, value: "repeated"} -> {:repeated, advance(state)}
      %Token{type: :identifier, value: "one_or_more"} -> {:one_or_more, advance(state)}
      _ -> {:required, state}
    end
  end

  defp consume_line_end(state) do
    case peek(state) do
      %Token{type: :newline} -> advance(state)
      _ -> state
    end
  end

  # `fail Name(args)` declares an author-defined semantic Diagnosis point for
  # a Tier-3 computed elab. Retain its typed argument declarations in the
  # macro AST; execution/lowering consumes them in the check/fail slice.
  defp parse_fail_declaration(state) do
    token = peek(state)
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    {params, parameter_span, state} =
      parse_macro_typed_parameters(state, token, name_token, :failure_parameters, name)

    {%{
       kind: :fail,
       name: name,
       params: params,
       line: token.line,
       source_span: macro_rule_source_span(token, parameter_span || name_token.span)
     }, state}
  end

  defp parse_macro_typed_parameters(state, owner_token, name_token, container, declaration) do
    case expect_token(state, :lparen) do
      {:ok, open_token, next_state} ->
        {params, next_state} = parse_typed_params(next_state)

        context =
          %{
            declaration: declaration,
            owner_span: owner_token.span,
            name_span: name_token.span
          }
          |> Map.merge(macro_parameter_boundaries(container))

        {next_state, close_token} =
          expect_container_close(next_state, :rparen, container, open_token, params, true, context)

        span = through_spans(open_token.span, close_token && close_token.span) || open_token.span
        {params, span, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:container_elements_syntax,
           %{
             kind: :container_opener_missing,
             container: container,
             declaration: declaration,
             expected: :lparen,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: owner_token.span,
             owner_span: owner_token.span,
             previous_span: name_token.span,
             name_span: name_token.span,
             line: observed.line,
             column: observed.col
           }}

        next_state = %{next_state | errors: [error | rest]}
        {params, next_state} = parse_typed_params(next_state)
        next_state = if peek(next_state).type == :rparen, do: advance(next_state), else: next_state
        {params, nil, next_state}
    end
  end

  defp macro_parameter_boundaries(:lift_callback_parameters),
    do: %{closing_tokens: [:arrow, :assign], closing_values: ["returns"]}

  defp macro_parameter_boundaries(_container), do: %{}

  defp parse_open_category(state) do
    token = peek(state)
    name_start = peek(advance(state))
    {name, name_end, state} = parse_dotted_name_owned(advance(state))
    name_span = through_spans(name_start.span, name_end.span) || name_start.span

    {%{
       kind: :open_category,
       name: name,
       line: token.line,
       source_span: macro_rule_source_span(token, name_span)
     }, state}
  end

  defp parse_macro_rule(state) do
    kw_token = peek(state)
    state = advance(state)

    keyword_token = peek(state)
    keyword = to_string(keyword_token.value)
    state = advance(state)

    segment_start = state.pos
    {segments, _segment_span, state} = parse_rule_segments(state, [])
    field_spans = macro_rule_field_spans(state, segment_start, state.pos)
    {category, state} = parse_rule_category(state)
    {obligations, state} = parse_capture_obligations(state, macro_syntax_fields(segments))

    {contextual, state} =
      case peek(state) do
        %Token{type: :identifier, value: "contextual"} -> {true, advance(state)}
        _ -> {false, state}
      end

    case peek(state) do
      %Token{type: :identifier, value: "computed"} ->
        parse_computed_rule(state, kw_token, keyword, segments, field_spans, category, contextual, obligations)

      _ ->
        parse_becomes_rule(state, kw_token, keyword, segments, field_spans, category, contextual, obligations)
    end
  end

  defp parse_capture_obligations(state, capture_names, obligations \\ []) do
    case peek(state) do
      %Token{value: value} = token when value in ["where", :where] ->
        interface_start = peek_at(state, 1)
        {interface, interface_end, state} = parse_dotted_name_owned(advance(state))

        interface_span =
          case {interface_start, interface_end} do
            {%Token{span: first}, %Token{span: last}} ->
              case Range.through(first, last) do
                {:ok, span} -> span
                _ -> first
              end

            _ ->
              nil
          end

        {open_token, state} =
          expect_macro_obligation_open(state, token, interface, interface_span)

        capture_token = peek(state)
        capture = to_string(capture_token.value)
        state = advance(state)

        {state, close_token} =
          close_macro_obligation(
            state,
            token,
            open_token,
            interface,
            interface_span,
            capture_token
          )

        state =
          if capture in capture_names do
            state
          else
            add_error(state, {
              :unknown_macro_obligation_capture,
              %{
                capture: capture,
                interface: interface,
                available_captures: capture_names,
                span: capture_token.span,
                line: capture_token.line,
                column: capture_token.col
              }
            })
          end

        obligation_span =
          through_spans(token.span, (close_token && close_token.span) || capture_token.span) || token.span

        obligation = %{
          interface: interface,
          capture: capture,
          line: token.line,
          col: token.col,
          source_span: obligation_span
        }

        parse_capture_obligations(state, capture_names, obligations ++ [obligation])

      _ ->
        {obligations, state}
    end
  end

  defp expect_macro_obligation_open(state, where_token, interface, interface_span) do
    case expect_token(state, :lparen) do
      {:ok, open_token, next_state} ->
        {open_token, next_state}

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:container_elements_syntax,
           %{
             kind: :container_opener_missing,
             container: :macro_obligation_capture,
             interface: interface,
             expected: :lparen,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: where_token.span,
             owner_span: where_token.span,
             previous_span: interface_span,
             interface_span: interface_span,
             line: observed.line,
             column: observed.col
           }}

        {nil, %{next_state | errors: [error | rest]}}
    end
  end

  defp close_macro_obligation(state, _where_token, nil, _interface, _interface_span, _capture_token) do
    case peek(state) do
      %Token{type: :rparen} = close_token -> {advance(state), close_token}
      _ -> {state, nil}
    end
  end

  defp close_macro_obligation(state, where_token, open_token, interface, interface_span, capture_token) do
    {state, close_token} =
      expect_container_close(state, :rparen, :macro_obligation_capture, open_token, [], false, %{
        interface: interface,
        owner_span: where_token.span,
        interface_span: interface_span,
        previous_span: capture_token.span,
        capture: to_string(capture_token.value),
        closing_values: ["where", "computed", "contextual", "becomes"]
      })

    {state, close_token}
  end

  # Tier-2: `becomes <template>` (unchanged behaviour, just extracted).
  defp parse_becomes_rule(state, kw_token, keyword, segments, field_spans, category, contextual, obligations) do
    state = expect_macro_rule_keyword(state, :becomes, :macro_rule_becomes_missing, kw_token)

    {template, state} = parse_expr(state, 0)
    {examples, state} = parse_rule_examples(state, kw_token)
    terminal_span = examples |> List.last() |> then(&(&1 && &1.source_span)) || ast_source_span(template)

    rule = %{
      kind: :syntax,
      keyword: keyword,
      segments: segments,
      field_spans: field_spans,
      template: template,
      body_span: ast_source_span(template),
      examples: examples,
      category: category,
      contextual: contextual,
      obligations: obligations,
      module_rule: keyword == "module",
      progress: nil,
      line: kw_token.line,
      head_span: macro_rule_source_span(kw_token, ast_source_span(template)),
      source_span: macro_rule_source_span(kw_token, terminal_span)
    }

    {rule, state}
  end

  # Tier-3: `computed by <elab-fn>` (base design §3). Captures the elab
  # reference; running it is a later slice. NOT harvested into active_macros
  # (harvest filters kind: :syntax), so a computed macro's use-site is inert
  # until the execution slice lands.
  defp parse_computed_rule(state, kw_token, keyword, segments, field_spans, category, contextual, obligations) do
    state = advance(state)

    # Optional `directly` opt-in: the elab fn receives each matched hole as its
    # own argument (multi-arg) rather than one synthesized input record. This
    # lets a rule whose holes differ from the keyword's shared synthesized
    # record still reach a typed adapter. Absent => single-record input (default).
    {direct_inputs, state} =
      case peek(state) do
        %Token{type: :identifier, value: "directly"} -> {true, advance(state)}
        _ -> {false, state}
      end

    state = expect_macro_rule_keyword(state, :by, :computed_rule_by_missing, kw_token)

    {elab, state} = parse_expr(state, 0)
    {examples, state} = parse_rule_examples(state, kw_token)
    terminal_span = examples |> List.last() |> then(&(&1 && &1.source_span)) || ast_source_span(elab)

    rule = %{
      kind: :computed,
      keyword: keyword,
      segments: segments,
      syntax_type: macro_syntax_type(keyword),
      syntax_fields: macro_syntax_fields(segments),
      field_spans: field_spans,
      syntax_repeated_fields: macro_syntax_repeated_fields(segments),
      syntax_field_types: macro_syntax_field_types(segments),
      direct_inputs: direct_inputs,
      elab: elab,
      body_span: ast_source_span(elab),
      examples: examples,
      category: category,
      contextual: contextual,
      obligations: obligations,
      module_rule: keyword == "module",
      progress: nil,
      line: kw_token.line,
      head_span: macro_rule_source_span(kw_token, ast_source_span(elab)),
      source_span: macro_rule_source_span(kw_token, terminal_span)
    }

    {rule, state}
  end

  defp macro_syntax_type(keyword), do: MacroFamily.syntax_type(keyword)

  defp macro_rule_field_spans(state, start_pos, end_pos) when end_pos > start_pos do
    Enum.reduce(start_pos..(end_pos - 1), %{}, fn index, spans ->
      case {token_at(state, index), token_at(state, index + 1), token_at(state, index + 2)} do
        {%Token{type: :lt} = opener, %Token{type: :identifier, value: name}, %Token{type: :colon}} ->
          closer =
            Enum.find_value(Elixir.Range.new(index + 3, end_pos - 1, 1), fn closer_index ->
              case token_at(state, closer_index) do
                %Token{type: :gt} = token -> token
                _ -> nil
              end
            end)

          span = closer && (through_spans(opener.span, closer.span) || opener.span)

          if span do
            Map.update(spans, to_string(name), [span], &[span | &1])
          else
            spans
          end

        _ ->
          spans
      end
    end)
    |> Map.new(fn {name, spans} -> {name, Enum.reverse(spans)} end)
  end

  defp macro_rule_field_spans(_state, _start_pos, _end_pos), do: %{}

  # A rule may optionally declare the category it produces. Categories are
  # metadata for the macro grammar; expansion remains ordinary AST rewriting.
  defp parse_rule_category(state) do
    case peek(state) do
      %Token{type: :identifier, value: "is"} ->
        state = advance(state)
        {category, state} = parse_dotted_name(state)
        {category, state}

      _ ->
        {nil, state}
    end
  end

  defp macro_syntax_fields(segments) do
    Enum.flat_map(segments, &segment_hole_names/1)
    |> Enum.uniq()
  end

  defp macro_syntax_repeated_fields(segments) do
    segments
    |> Enum.flat_map(&segment_repeated_hole_names/1)
    |> Enum.uniq()
  end

  defp macro_syntax_field_types(segments) do
    segments
    |> Enum.flat_map(&segment_field_types/1)
    |> Map.new()
  end

  defp segment_field_types({:hole, %{name: name, kind: kind}}) when kind in ["Int", "Float", "Atom", "Bool"],
    do: [{name, {:primitive, kind}}]

  defp segment_field_types({:repeat, segment}), do: segment_field_types(segment)

  defp segment_field_types({:optional, segments}),
    do: Enum.flat_map(segments, &segment_field_types/1)

  defp segment_field_types(_segment), do: []

  defp segment_hole_names({:hole, %{name: name}}), do: [name]
  defp segment_hole_names({:code_hole, %{name: name}}), do: [name]
  defp segment_hole_names({:raw_hole, %{name: name}}), do: [name]
  defp segment_hole_names({:declarations_hole, %{name: name}}), do: [name]
  defp segment_hole_names({:family, %{name: name}}), do: [name]
  defp segment_hole_names({:repeat, segment}), do: segment_hole_names(segment)
  defp segment_hole_names({:optional, segments}), do: Enum.flat_map(segments, &segment_hole_names/1)
  defp segment_hole_names(_segment), do: []

  defp segment_repeated_hole_names({:repeat, segment}), do: segment_hole_names(segment)

  defp segment_repeated_hole_names({:optional, segments}),
    do: Enum.flat_map(segments, &segment_repeated_hole_names/1)

  defp segment_repeated_hole_names(_segment), do: []

  defp segment_inputs({:hole, %{name: name}}, bindings), do: [Map.fetch!(bindings, name)]
  defp segment_inputs({:code_hole, %{name: name}}, bindings), do: [Map.fetch!(bindings, name)]
  defp segment_inputs({:raw_hole, %{name: name}}, bindings), do: [Map.fetch!(bindings, name)]
  defp segment_inputs({:declarations_hole, %{name: name}}, bindings), do: [Map.fetch!(bindings, name)]
  defp segment_inputs({:family, %{name: name}}, bindings), do: [Map.fetch!(bindings, name)]
  defp segment_inputs({:repeat, segment}, bindings), do: [segment_inputs(segment, bindings)]
  # Optional groups still occupy a stable reflected-record slot. An absent
  # optional hole is represented by `nil`, which MacroSyntax reflects as
  # `Raw(SOpaque)`; dropping the slot would shift every later field left and
  # make the typed computed input unsound.
  defp segment_inputs({:optional, segments}, bindings),
    do: Enum.flat_map(segments, &optional_segment_inputs(&1, bindings))

  defp segment_inputs(_segment, _bindings), do: []

  defp optional_segment_inputs({:hole, %{name: name}}, bindings), do: [Map.get(bindings, name)]
  defp optional_segment_inputs({:code_hole, %{name: name}}, bindings), do: [Map.get(bindings, name)]
  defp optional_segment_inputs({:raw_hole, %{name: name}}, bindings), do: [Map.get(bindings, name)]

  defp optional_segment_inputs({:declarations_hole, %{name: name}}, bindings),
    do: [Map.get(bindings, name)]

  defp optional_segment_inputs({:repeat, segment}, bindings), do: optional_segment_inputs(segment, bindings)

  defp optional_segment_inputs({:optional, segments}, bindings),
    do: Enum.flat_map(segments, &optional_segment_inputs(&1, bindings))

  defp optional_segment_inputs(_segment, _bindings), do: []

  # After a syntax rule's template, an OPTIONAL indented block of `example …`
  # lines (self-proving §5). Consumes the nested indent/dedent so the macro-body
  # loop stays at the rule level. Returns [] when no example block follows.
  defp parse_rule_examples(state, rule_token) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {examples, state} = parse_example_lines(state, [], rule_token)
        state = expect_dedent(state)
        {examples, state}

      _ ->
        {[], state}
    end
  end

  defp parse_example_lines(state, acc, rule_token) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :identifier, value: "example"} ->
        {ex, state} = parse_one_example(state)
        parse_example_lines(state, [ex | acc], rule_token)

      observed ->
        state =
          add_error(
            state,
            {:macro_nested_syntax,
             %{
               kind: :macro_example_entry_invalid,
               expected: :example,
               observed: macro_separator_observed(observed),
               token_type: observed.type,
               span: observed.span,
               opener_span: rule_token.span,
               previous_span: acc |> List.first() |> then(&(&1 && &1.source_span)) || rule_token.span,
               line: observed.line,
               column: observed.col
             }}
          )

        # Recover: skip one token so a bad line does not eat the block.
        parse_example_lines(advance(state), acc, rule_token)
    end
  end

  # `example <use-site tokens…> expands <expected>` where <expected> is either
  # `: <Type>` (a type-only pin, §5.2) or an expansion expression. The use-site
  # is captured as raw tokens — it names the macro's own keyword and cannot be
  # expanded at macro-def parse time; slice 2b feeds these tokens through the
  # rule to check the expansion.
  defp parse_one_example(state) do
    kw = peek(state)
    state = advance(state)
    {use_site, state} = collect_until_expands(state, [])
    use_site = Enum.reverse(use_site)

    use_site_span =
      case use_site do
        [] -> nil
        tokens -> through_spans(List.first(tokens).span, List.last(tokens).span) || List.first(tokens).span
      end

    state = expect_macro_rule_keyword(state, :expands, :macro_example_expands_missing, kw)

    {expected, state} =
      case peek(state) do
        %Token{type: :colon} ->
          {ty, state} = parse_expr(advance(state), 0)
          {{:type, ty}, state}

        _ ->
          {ast, state} = parse_expr(state, 0)
          {{:expansion, ast}, state}
      end

    expected_span = expected |> elem(1) |> ast_source_span()

    {%{
       use_site: use_site,
       expected: expected,
       line: kw.line,
       keyword_span: kw.span,
       use_site_span: use_site_span,
       expected_span: expected_span,
       source_span: macro_rule_source_span(kw, expected_span)
     }, state}
  end

  # Collect the filled use-site tokens up to the `expands` keyword (or end of
  # line). Guards on :newline/:dedent/:eof so a missing `expands` cannot run off
  # the block.
  defp collect_until_expands(state, acc) do
    case peek(state) do
      %Token{type: :identifier, value: "expands"} -> {acc, state}
      %Token{type: type} when type in [:newline, :dedent, :eof] -> {acc, state}
      tok -> collect_until_expands(advance(state), [tok | acc])
    end
  end

  # `literal <n: Number> ms becomes <template>` — a Tier-1 units rule (base
  # §111). Unlike `syntax`, there is NO leading keyword; the rule is triggered
  # at a use-site by a NUMBER followed by the suffix (Task 2). Segments reuse
  # parse_rule_segments (a leading number-hole + a `{:lit, suffix}`).
  defp parse_literal_rule(state) do
    kw_token = peek(state)
    state = advance(state)

    {segments, _segment_span, state} = parse_rule_segments(state, [])

    case peek(state) do
      %Token{type: :identifier, value: "computed"} ->
        state = advance(state)

        state =
          case peek(state) do
            %Token{type: :identifier, value: "directly"} -> advance(state)
            _ -> state
          end

        state = expect_macro_rule_keyword(state, :by, :computed_literal_rule_by_missing, kw_token)

        {elab, state} = parse_expr(state, 0)

        rule = %{
          kind: :computed_literal,
          keyword: nil,
          token_kind: literal_token_kind(segments),
          segments: segments,
          elab: elab,
          progress: nil,
          line: kw_token.line,
          source_span: macro_rule_source_span(kw_token, ast_source_span(elab))
        }

        {rule, state}

      _ ->
        state = expect_macro_rule_keyword(state, :becomes, :literal_rule_becomes_missing, kw_token)

        {template, state} = parse_expr(state, 0)

        rule = %{
          kind: :literal,
          keyword: nil,
          segments: segments,
          suffix: literal_suffix(segments),
          template: template,
          progress: nil,
          line: kw_token.line,
          source_span: macro_rule_source_span(kw_token, ast_source_span(template))
        }

        {rule, state}
    end
  end

  defp expect_macro_rule_keyword(state, expected, kind, opener_token) do
    expected_value = Atom.to_string(expected)

    case peek(state) do
      %Token{type: :identifier, value: ^expected_value} ->
        advance(state)

      observed ->
        add_error(
          state,
          {:macro_rule_separator_syntax,
           %{
             kind: kind,
             expected: expected,
             observed: macro_separator_observed(observed),
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: opener_token.span,
             previous_span: previous_authored_span(state, opener_token.span),
             line: observed.line,
             column: observed.col
           }}
        )
    end
  end

  defp macro_separator_observed(%Token{type: type}) when type in [:newline, :dedent, :eof], do: type
  defp macro_separator_observed(%Token{value: value, type: type}), do: value || type

  # The dispatch suffix is the first literal segment following the leading
  # number-hole (`[{:hole,_}, {:lit, s} | _]`). A malformed literal rule
  # (no hole-then-lit prefix) has no suffix and is un-triggerable (harvest
  # skips it, Task 2); T4 does not diagnose that (error-floor task).
  defp literal_suffix([{:hole, _}, {:lit, s} | _]), do: s
  defp literal_suffix(_), do: nil

  defp literal_token_kind([{:lit, name} | _]) when is_binary(name), do: String.to_atom(name)
  defp literal_token_kind(_), do: nil

  # `explain` <INDENT> (<point> => <message>)+ <DEDENT> — the author's failure
  # descriptions (self-proving §3.2). Attached to the macro_def as one entry;
  # exhaustiveness over the derived Diagnosis is checked separately (MacroValidate).
  defp parse_explain_block(state) do
    kw = peek(state)
    state = advance(state)
    state = skip_macro_trivia(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {cs, state} = parse_explain_clauses(state, [], kw)
          state = expect_dedent(state)
          {cs, state}

        _ ->
          {[], state}
      end

    {%{
       kind: :explain,
       clauses: clauses,
       line: kw.line,
       source_span: macro_rule_source_span(kw, clauses |> List.last() |> then(&(&1 && &1.source_span)))
     }, state}
  end

  defp parse_explain_clauses(state, acc, explain_token) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      _ ->
        clause_start = peek(state)

        previous_span =
          acc |> List.first() |> then(&(&1 && &1.source_span)) || explain_token.span

        {point, point_span, state} = parse_explain_point(state, explain_token, previous_span)
        state = expect_explain_clause_arrow(state, clause_start, point_span)
        state = skip_macro_trivia(state)
        {body, state} = parse_expr(state, 0)

        clause = %{
          point: point,
          body: body,
          line: peek(state).line,
          source_span: macro_rule_source_span(clause_start, ast_source_span(body))
        }

        parse_explain_clauses(state, [clause | acc], explain_token)
    end
  end

  defp expect_explain_clause_arrow(state, clause_start, point_span) do
    case expect_token(state, :fat_arrow) do
      {:ok, _arrow, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        point_span = through_spans(clause_start.span, point_span) || clause_start.span

        error =
          {:branch_arrow_missing,
           %{
             family: :explain_clause,
             expected: :fat_arrow,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: clause_start.span,
             previous_span: point_span,
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # A point is `keyword "w"` (a literal-token failure) or a bare `Category`
  # identifier (a typed-hole failure). Backticked/qualified categories are out
  # of scope for this slice. A total fallback is REQUIRED: a malformed point
  # (a stray `=>` with no preceding point) would otherwise crash the whole parse
  # with a CaseClauseError — record a recoverable diagnostic instead and do NOT
  # advance past the offending token (so the caller's expect/2 reports cleanly).
  defp parse_explain_point(state, explain_token, previous_span) do
    case peek(state) do
      %Token{type: :identifier, value: "keyword"} ->
        keyword_token = peek(state)
        state = advance(state)
        w = peek(state)
        state = advance(state)
        span = through_spans(keyword_token.span, w.span) || keyword_token.span
        {{:keyword, to_string(w.value)}, span, state}

      %Token{type: :identifier, value: cat} = token ->
        {{:category, cat}, token.span, advance(state)}

      observed ->
        error =
          {:macro_nested_syntax,
           %{
             kind: :macro_explain_point_invalid,
             expected: :failure_category,
             alternatives: [:keyword],
             observed: macro_separator_observed(observed),
             token_type: observed.type,
             span: observed.span,
             opener_span: explain_token.span,
             previous_span: previous_span,
             line: observed.line,
             column: observed.col
           }}

        state = add_error(state, error)
        {{:category, "?"}, observed.span, state}
    end
  end

  # Ordered segments between a rule's keyword and `becomes`: literal tokens,
  # typed holes, line-oriented repetitions, and optional groups.
  defp parse_rule_segments(state, acc), do: parse_rule_segments(state, acc, :rule, nil)

  defp parse_rule_segments(state, acc, mode, last_span) do
    case peek(state) do
      %Token{type: :rparen} when mode == :group ->
        {Enum.reverse(acc), last_span, state}

      # Stop at either tier verb — `becomes` (Tier-2 template) or `computed`
      # (Tier-3 elab). `contextual` declares that proof is deferred until the
      # use site supplies an enclosing type/context. Without stopping at
      # `computed`, it (and `by`) would be
      # swallowed as literal segments and the verb branch could never fire.
      #
      # Deliberate restriction (parity with the pre-existing `becomes`
      # behaviour, not new to this change): a rule's OWN segments can no
      # longer contain a literal token spelled `computed` (e.g.
      # `syntax do computed becomes X` used to parse `computed` as a plain
      # `{:lit, "computed"}` segment; it now mis-stops and reports
      # `{:expected, :by, ...}`). `becomes`/`computed`/`by` are reserved verbs
      # across the whole rule grammar, not just after a rule's segments —
      # same trade-off `becomes` already made alone. No known `.cure` source
      # relies on `computed` as a matched token.
      %Token{type: :identifier, value: v} when v in ["becomes", "computed", "is", "contextual"] ->
        {Enum.reverse(acc), last_span, state}

      %Token{value: value} when value in ["where", :where] and mode == :rule ->
        {Enum.reverse(acc), last_span, state}

      %Token{type: type} when type in [:newline, :dedent, :eof] ->
        {Enum.reverse(acc), last_span, state}

      %Token{type: :lt} ->
        case {peek_at(state, 1), peek_at(state, 2), peek_at(state, 3), peek_at(state, 4), peek_at(state, 5),
              peek_at(state, 6), peek_at(state, 7)} do
          {%Token{type: :identifier, value: name}, %Token{type: :colon}, %Token{type: :identifier, value: "delayed"},
           %Token{type: :identifier, value: "raw"}, %Token{type: :identifier, value: "until"},
           %Token{type: :identifier, value: delimiter}, %Token{type: :gt}} ->
            terminal_span = peek_at(state, 7).span

            hole =
              {:raw_hole, %{name: name, delimiter: delimiter, delayed: true, line: peek(state).line}}

            state = Enum.reduce(1..8, state, fn _, acc_state -> advance(acc_state) end)
            parse_rule_segments(state, [hole | acc], mode, terminal_span)

          {%Token{type: :identifier, value: name}, %Token{type: :colon}, %Token{type: :identifier, value: "raw"},
           %Token{type: :identifier, value: "until"}, %Token{type: :identifier, value: delimiter}, %Token{type: :gt}, _} ->
            terminal_span = peek_at(state, 6).span
            hole = {:raw_hole, %{name: name, delimiter: delimiter, line: peek(state).line}}
            state = Enum.reduce(1..7, state, fn _, acc_state -> advance(acc_state) end)
            parse_rule_segments(state, [hole | acc], mode, terminal_span)

          {%Token{type: :identifier, value: name}, %Token{type: :colon}, %Token{type: :identifier, value: "Code"},
           %Token{type: :identifier, value: "until"}, %Token{type: :identifier, value: delimiter}, %Token{type: :gt}, _} ->
            terminal_span = peek_at(state, 6).span
            hole = {:code_hole, %{name: name, delimiter: delimiter, line: peek(state).line}}
            state = Enum.reduce(1..7, state, fn _, acc_state -> advance(acc_state) end)
            parse_rule_segments(state, [hole | acc], mode, terminal_span)

          # A positional declarations block hole: `<name: Declarations until X>`
          # captures the indented run of definitions the same way the structured
          # family `body Declarations` section does (parse_definition_block), but
          # in a positional rule slot so a raw Tier-0 template can funnel its
          # trailing body block through `computed`. The only delimiter in use is
          # `dedent` (the block's own indentation boundary).
          {%Token{type: :identifier, value: name}, %Token{type: :colon},
           %Token{type: :identifier, value: "Declarations"}, %Token{type: :identifier, value: "until"},
           %Token{type: :identifier, value: delimiter}, %Token{type: :gt}, _} ->
            terminal_span = peek_at(state, 6).span
            hole = {:declarations_hole, %{name: name, delimiter: delimiter, line: peek(state).line}}
            state = Enum.reduce(1..7, state, fn _, acc_state -> advance(acc_state) end)
            parse_rule_segments(state, [hole | acc], mode, terminal_span)

          _ ->
            with %Token{type: :identifier, value: name} <- peek_at(state, 1),
                 %Token{type: :colon} <- peek_at(state, 2),
                 %Token{type: :identifier, value: kind} <- peek_at(state, 3),
                 %Token{type: :gt} = close_token <- peek_at(state, 4) do
              hole = {:hole, %{name: name, kind: kind, line: peek(state).line}}
              state = state |> advance() |> advance() |> advance() |> advance() |> advance()
              parse_rule_segments(state, [hole | acc], mode, close_token.span)
            else
              _ ->
                opener = peek(state)
                observed = peek_at(state, 4)

                state =
                  add_error(state, {
                    :malformed_hole,
                    %{
                      opener_span: opener.span,
                      span: observed.span || opener.span,
                      observed: observed.value || observed.type,
                      line: observed.line,
                      column: observed.col
                    }
                  })

                {Enum.reverse(acc), opener.span || last_span, advance(state)}
            end
        end

      %Token{type: :ellipsis} = ellipsis_token ->
        case acc do
          [segment | rest] ->
            parse_rule_segments(advance(state), [{:repeat, segment} | rest], mode, ellipsis_token.span)

          [] ->
            parse_rule_segments(advance(state), [{:lit, "..."} | acc], mode, ellipsis_token.span)
        end

      %Token{type: :lparen} = open_token ->
        if optional_group_start?(state) do
          {group, _group_span, state} = parse_rule_segments(advance(state), [], :group, open_token.span)
          close_token = peek(state)
          state = advance(state)
          question_token = peek(state)
          state = advance(state)
          terminal_span = (question_token && question_token.span) || close_token.span
          parse_rule_segments(state, [{:optional, group} | acc], mode, terminal_span)
        else
          parse_rule_segments(advance(state), [{:lit, "("} | acc], mode, open_token.span)
        end

      %Token{value: v} = token ->
        parse_rule_segments(advance(state), [{:lit, to_string(v)} | acc], mode, token.span)
    end
  end

  defp optional_group_start?(%{pos: pos} = state) do
    result =
      state
      |> tokens_from(pos + 1)
      |> Enum.with_index()
      |> Enum.find_value(:not_found, fn
        {%Token{type: :rparen}, index} ->
          case token_at(state, pos + index + 2) do
            %Token{type: :hole, value: ""} -> true
            _ -> false
          end

        {%Token{type: type}, _index} when type in [:newline, :dedent, :eof] ->
          :stop

        _ ->
          false
      end)

    result == true
  end

  # -- Enhanced Type Expression Parser ----------------------------------------

  # Type-expression entry point. `|` binds LOOSER than `->`, so `A -> B | C` is
  # `(A -> B) | C`. A leading `|` is permitted.
  #
  # Members are collected in SOURCE order; canonicalisation (flatten, dedupe,
  # sort) is the elaborator's job — see `Cure.Elab.Union`.
  defp parse_type_expr(state) do
    state =
      case peek(state) do
        %Token{type: :bar} -> advance(state) |> skip_newlines()
        _ -> state
      end

    {first, state} = parse_union_first_member(state)
    {rest, state} = parse_union_members(state)

    case rest do
      [] -> {first, state}
      _ -> {{:union_type, [], [first | rest]}, state}
    end
  end

  # The first candidate member of a possible union. A literal-shaped token is ONLY
  # treated as a literal member if a `|` immediately follows — e.g. the `3` in
  # `3 | String`. If no `|` follows, fall through to `parse_type_arrow/1` unchanged,
  # so every existing non-union numeral-in-type-position use (`Bounded(3)`,
  # `Bounded(1114112)`, `Equivalent(Int, 3, 3)`) keeps parsing to
  # `{:variable, [scope: :local], "N"}` and keeps working through idx_to_core's
  # existing numeric_index_value path.
  defp parse_union_first_member(state) do
    token = peek(state)
    next = peek_at(state, 1)

    if literal_token?(token) and match?(%Token{type: :bar}, next) do
      {literal(literal_subtype(token.type), token), advance(state)}
    else
      parse_type_arrow(state)
    end
  end

  # A subsequent member, reached only after a `|` has already been consumed — so,
  # unlike the first member, we already KNOW we are inside a union. A literal-shaped
  # token is unconditionally a literal member; no lookahead needed (this covers the
  # `4` in `3 | 4`, which is not itself followed by another `|`).
  defp parse_union_member(state) do
    token = peek(state)

    if literal_token?(token) do
      {literal(literal_subtype(token.type), token), advance(state)}
    else
      parse_type_arrow(state)
    end
  end

  # NOTE: no `skip_newlines` before peeking for `:bar`. That is deliberate — a
  # newline terminates the type annotation, and skipping it would let the parser
  # swallow the `|` of a following ADT variant.
  defp parse_union_members(state) do
    case peek(state) do
      %Token{type: :bar} ->
        state = advance(state) |> skip_newlines()
        {member, state} = parse_union_member(state)
        {rest, state} = parse_union_members(state)
        {[member | rest], state}

      _ ->
        {[], state}
    end
  end

  defp literal_token?(%Token{type: t}), do: t in [:integer, :float, :string, :atom, :char, :bool]
  defp literal_token?(_), do: false

  defp literal_subtype(:integer), do: :integer
  defp literal_subtype(:float), do: :float
  defp literal_subtype(:string), do: :string
  defp literal_subtype(:atom), do: :symbol
  defp literal_subtype(:char), do: :char
  defp literal_subtype(:bool), do: :boolean

  # The arrow ladder. Handles: PascalCase, Type(A, B), A -> B, (A, B) -> C.
  # Callers that must NOT absorb a `|` (arrow codomains, the ADT alias-RHS probe)
  # call this directly rather than `parse_type_expr/1`.
  defp parse_type_arrow(state) do
    token = peek(state)

    # A `fn(y) -> …` LAMBDA literal appearing in a dependent index/term position
    # (e.g. `Equivalent(Eff, bind(m, fn(y) -> Pure(y)), m)`). `fn` lexes as
    # `%Token{type: :keyword, value: :fn}`, so it is caught here before the
    # `token.type` dispatch below. Without it the `fn` fell through to the
    # "Simple type" arm, `(y)` was read as a type-param list and the trailing
    # `->` turned the whole thing into a bogus arrow type `Function(y, …)` — `y`
    # then dangled as `{:global, :y}` and normalisation crashed (E10a). Reuse the
    # expression lambda entry so the SAME `{:lambda,…}` AST is produced here as in
    # term position; a lambda is a complete term, so (unlike the arrow arms) it is
    # NOT chained through `maybe_parse_function_type`.
    if token.type == :keyword and token.value == :fn do
      parse_fn_or_lambda(state)
    else
      parse_type_arrow_dispatch(state, token)
    end
  end

  defp parse_type_arrow_dispatch(state, token) do
    case token.type do
      # Character literals in dependent indices are terms, not type names. The
      # generic simple-type branch stringifies the decoded codepoint (`'a'` ->
      # "97"), which loses the literal kind and later lowers it as Nat. Preserve
      # the literal AST so index elaboration can produce `:bounded_lit`.
      :char ->
        {literal(:char, token), advance(state)}

      :lbrace ->
        parse_refinement_type(state)

      # Tuple type `%[A, B]` — the canonical tuple-type sigil, mirroring the value tuple `%[a, b]` and removing
      # the value/type inconsistency where values were `%[a, b]` but their types were `(A, B)`. It produces the
      # SAME `{:tuple_type, …}` node as `Tuple(A, B)` — including optional per-position binders `%[x: A, B(x)]`
      # for a dependent telescope — so resolution, display, and codegen are unchanged. `%[]` is the empty tuple.
      # (Original `%[A, B]` proposal: Aleksei Matiushkin / am-kantox; adapted here to the dependent parser.)
      :tuple_open ->
        open_token = token
        state = advance(state)

        case peek(state) do
          %Token{type: :rbracket} ->
            {{:tuple_type, [arity: 0, binders: []], []}, advance(state)}

          _ ->
            {positions, state} = parse_tuple_positions(state, [])
            binders = Enum.map(positions, &elem(&1, 0))
            types = Enum.map(positions, &elem(&1, 1))

            {state, close_token} =
              expect_container_close(state, :rbracket, :tuple_type_sigil, open_token, types, true)

            meta = [arity: length(positions), binders: binders]
            meta = put_container_source_info(meta, open_token, state, close_token)
            {{:tuple_type, meta, types}, state}
        end

      :lparen ->
        # Grouped/tuple type `(A, B)` or function type `(A, B) -> C`. Each element
        # may carry an optional binder name `(x: A) -> …` — a DEPENDENT arrow whose
        # codomain (and later domains) may mention `x`.
        open_token = token
        state = advance(state)
        {inner, state} = parse_paren_type_list(state)
        inner_types = Enum.map(inner, &elem(&1, 1))

        {state, close_token} =
          expect_container_close(state, :rparen, :grouped_type, open_token, inner_types, true)

        case peek(state) do
          %Token{type: :arrow} ->
            state = advance(state)
            {ret, state} = parse_type_arrow(state)
            binders = Enum.map(inner, &elem(&1, 0))
            doms = Enum.map(inner, &elem(&1, 1))

            ast =
              if Enum.all?(binders, &is_nil/1) do
                # No named domain — the existing non-dependent arrow, unchanged.
                {:function_call, [name: "Function", function_type: true], doms ++ [ret]}
              else
                # At least one named domain — a dependent Π; carry the binder names
                # (nil for anonymous domains) for the elaborator to scope.
                {:pi_type, [binders: binders], doms ++ [ret]}
              end

            {ast, state}

          _ ->
            # Grouped type or tuple type — binders (if any) are not meaningful here.
            case Enum.map(inner, &elem(&1, 1)) do
              [single] ->
                {single, state}

              many ->
                # Legacy spelling, canonical representation. Downstream
                # elaboration and emission must not recover which tuple spelling
                # was authored; all spellings enter the dependent pipeline as
                # the same unit-terminated tuple telescope.
                binders = List.duplicate("_", length(many))
                meta = [arity: length(many), binders: binders]
                meta = put_container_source_info(meta, open_token, state, close_token)
                {{:tuple_type, meta, many}, deprecate_paren_tuple(state, token, length(many))}
            end
        end

      _ ->
        # Simple type: Name or Name(A, B)
        state = advance(state)
        base_name = to_string(token.value)

        cond do
          base_name == "Sigma" and match?(%Token{type: :lparen}, peek(state)) ->
            parse_sigma_type(state, token)

          base_name == "Tuple" and match?(%Token{type: :lparen}, peek(state)) ->
            parse_tuple_type(state, token)

          match?(%Token{type: :lparen}, peek(state)) ->
            open_token = peek(state)
            state = advance(state)
            {params, state} = parse_type_param_list(state)

            {state, close_token} =
              expect_container_close(state, :rparen, :type_arguments, open_token, params, true, %{type: base_name})

            meta = [name: base_name, line: token.line, col: token.col]
            meta = put_type_application_source_info(meta, token, params, close_token)
            ast = {:function_call, meta, params}
            maybe_parse_function_type(state, ast)

          match?(%Token{type: :arrow}, peek(state)) ->
            # A -> B  (unary function type)
            state = advance(state)
            {ret, state} = parse_type_arrow(state)
            base = type_variable(token)
            ast = {:function_call, [name: "Function", function_type: true], [base, ret]}
            {ast, state}

          true ->
            base = type_variable(token)
            maybe_parse_type_projection(base, state)
        end
    end
  end

  # `{value: Base | Proposition}` is a proof-backed refinement type. The base is
  # parsed with the non-union arrow parser because this form owns the `|` token.
  # The proposition remains ordinary Cure syntax and may refer to `value`.
  defp parse_refinement_type(state) do
    open_token = peek(state)
    state = advance(state)
    binder_token = peek(state)

    {binder, state} =
      case binder_token do
        %Token{type: :identifier} ->
          {to_string(binder_token.value), advance(state)}

        %Token{} ->
          error =
            {:refinement_type_syntax,
             %{
               kind: :refinement_binder_invalid,
               expected: :identifier,
               observed: binder_token.value || binder_token.type,
               token_type: binder_token.type,
               span: binder_token.span,
               opener_span: open_token.span,
               line: binder_token.line,
               column: binder_token.col
             }}

          {"_invalid_refinement_binder", state |> add_error(error) |> advance()}
      end

    state =
      expect_refinement_separator(
        state,
        :refinement_colon_missing,
        :colon,
        open_token,
        binder_token.span,
        binder_token.span
      )

    {base_type, state} = parse_type_arrow(state)

    state =
      expect_refinement_separator(
        state,
        :refinement_bar_missing,
        :bar,
        open_token,
        binder_token.span,
        first_node_source_span(base_type)
      )
      |> skip_newlines()

    {proposition, state} = parse_expr(state, 0)

    {state, close_token} =
      case expect_token(state, :rbrace) do
        {:ok, close, next_state} ->
          {next_state, close}

        {:error, next_state} ->
          observed = peek(next_state)
          [_generic | rest] = next_state.errors

          error =
            {:refinement_type_syntax,
             %{
               kind: if(observed.type in [:eof, :dedent], do: :refinement_unclosed, else: :mismatched_closer),
               family: :refinement_type,
               expected: :rbrace,
               observed: observed.value || observed.type,
               token_type: observed.type,
               span: observed.span,
               observed_span: observed.span,
               opener_span: open_token.span,
               binder_span: binder_token.span,
               previous_span: first_node_source_span(proposition),
               line: observed.line,
               column: observed.col
             }}

          {%{next_state | errors: [error | rest]}, nil}
      end

    meta = [binder: binder]
    meta = put_refinement_source_info(meta, open_token, close_token, binder_token, base_type, proposition)

    {{:refinement_type, meta, [base_type, proposition]}, state}
  end

  defp expect_refinement_separator(state, kind, expected, open_token, binder_span, previous_span) do
    case expect_token(state, expected) do
      {:ok, _token, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:refinement_type_syntax,
           %{
             kind: kind,
             expected: expected,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: open_token.span,
             binder_span: binder_span,
             previous_span: previous_span,
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  defp put_refinement_source_info(meta, open_token, close_token, binder_token, base_type, proposition) do
    case {open_token.span, close_token} do
      {%Cure.Diagnostic.Span{} = opener, %Token{span: %Cure.Diagnostic.Span{} = closer}} ->
        with {:ok, whole} <- Range.through(opener, closer) do
          info = %SourceInfo{
            whole: whole,
            opener: opener,
            closer: closer,
            name: binder_token.span,
            annotation: first_node_source_span(base_type),
            body: first_node_source_span(proposition)
          }

          Keyword.put(meta, :source_info, info)
        else
          _ -> meta
        end

      _ ->
        meta
    end
  end

  # A type-position projection `p.1` / `p.2` (used in dependent index positions,
  # e.g. `SF(as, bs, p.1)`).
  defp maybe_parse_type_projection(inner, state) do
    case peek(state) do
      %Token{type: :dot} ->
        state = advance(state)
        attr_token = peek(state)
        attr = to_string(attr_token.value)
        state = advance(state)
        node = {:attribute_access, [attribute: attr], [inner]}
        maybe_parse_type_projection(node, state)

      # `Mod.Name(args)` — a qualified type constructor applied to type arguments.
      # The dotted projection above yields the qualified name; without this branch
      # the trailing `(args)` dangled unconsumed, a hard parse error in a signature
      # and a garbled `name: "unknown"` call in a `typealias` RHS. Only a chain of
      # NAME attributes (not a numeric index projection like `p.1`) can head a type
      # application; anything else leaves the `(` for the caller.
      %Token{type: :lparen} ->
        case qualified_type_name(inner) do
          {:ok, name} ->
            open_token = peek(state)
            state = advance(state)
            {params, state} = parse_type_param_list(state)

            {state, close_token} =
              expect_container_close(state, :rparen, :type_arguments, open_token, params, true, %{type: name})

            meta = [name: name, qualified: true]
            meta = put_type_application_source_info(meta, inner, params, close_token)
            ast = {:function_call, meta, params}
            maybe_parse_function_type(state, ast)

          :error ->
            {inner, state}
        end

      _ ->
        {inner, state}
    end
  end

  # A dotted chain of NAME attributes over a base variable is a qualified type
  # name: `A.B.C` → "A.B.C". A chain containing a numeric projection (`p.1`) is a
  # dependent index projection, not a type constructor, and returns `:error`.
  defp qualified_type_name({:variable, _, n}) when is_binary(n), do: {:ok, n}

  defp qualified_type_name({:attribute_access, meta, [inner]}) do
    attr = Keyword.get(meta, :attribute)

    if is_binary(attr) and attr =~ ~r/^[A-Za-z_]/ do
      case qualified_type_name(inner) do
        {:ok, prefix} -> {:ok, prefix <> "." <> attr}
        :error -> :error
      end
    else
      :error
    end
  end

  defp qualified_type_name(_), do: :error

  # Sigma(x: DomType, BodyType) — a dependent-pair type (design spec §4.7). The
  # body type may mention the binder `x`.
  defp parse_sigma_type(state, sigma_token) do
    open_token = peek(state)
    state = advance(state)
    binder_token = peek(state)

    {binder, state} =
      case binder_token do
        %Token{type: :identifier} ->
          {to_string(binder_token.value), advance(state)}

        %Token{} ->
          error =
            {:sigma_type_syntax,
             %{
               kind: :sigma_binder_invalid,
               expected: :identifier,
               observed: binder_token.value || binder_token.type,
               token_type: binder_token.type,
               span: binder_token.span,
               opener_span: open_token.span,
               line: binder_token.line,
               column: binder_token.col
             }}

          {"_invalid_sigma_binder", state |> add_error(error) |> advance()}
      end

    state = expect_sigma_separator(state, :sigma_colon_missing, :colon, open_token, binder_token.span)
    {dom_type, state} = parse_type_expr(state)

    state =
      expect_sigma_separator(
        state,
        :sigma_comma_missing,
        :comma,
        open_token,
        binder_token.span,
        first_node_source_span(dom_type)
      )

    {body_type, state} = parse_type_expr(state)

    {state, close_token} =
      case expect_token(state, :rparen) do
        {:ok, close, next_state} ->
          {next_state, close}

        {:error, next_state} ->
          observed = peek(next_state)
          [_generic | rest] = next_state.errors

          error =
            {:sigma_type_syntax,
             %{
               kind: if(observed.type in [:eof, :dedent], do: :sigma_unclosed, else: :mismatched_closer),
               family: :sigma_type,
               expected: :rparen,
               observed: observed.value || observed.type,
               token_type: observed.type,
               span: observed.span,
               observed_span: observed.span,
               opener_span: open_token.span,
               binder_span: binder_token.span,
               previous_span: first_node_source_span(body_type),
               line: observed.line,
               column: observed.col
             }}

          {%{next_state | errors: [error | rest]}, nil}
      end

    meta = [binder: binder]
    meta = put_sigma_source_info(meta, sigma_token, open_token, close_token, binder_token, dom_type, body_type)
    {{:sigma_type, meta, [dom_type, body_type]}, state}
  end

  defp expect_sigma_separator(state, kind, expected, open_token, binder_span, previous_span \\ nil) do
    case expect_token(state, expected) do
      {:ok, _token, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:sigma_type_syntax,
           %{
             kind: kind,
             expected: expected,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: open_token.span,
             binder_span: binder_span,
             previous_span: previous_span || binder_span,
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  defp put_sigma_source_info(meta, sigma_token, open_token, close_token, binder_token, dom_type, body_type) do
    case {sigma_token.span, open_token.span, close_token} do
      {%Cure.Diagnostic.Span{} = name, %Cure.Diagnostic.Span{} = opener,
       %Token{span: %Cure.Diagnostic.Span{} = closer} = close} ->
        with {:ok, whole} <- Range.through(name, close) do
          info = %SourceInfo{
            whole: whole,
            name: name,
            opener: opener,
            closer: closer,
            arguments: Enum.flat_map([dom_type, body_type], &node_source_span/1),
            annotation: first_node_source_span(dom_type),
            body: first_node_source_span(body_type),
            fields: %{"binder" => binder_token.span}
          }

          Keyword.put(meta, :source_info, info)
        else
          _ -> meta
        end

      _ ->
        meta
    end
  end

  # Tuple(T1, …, Tn) — the honest surface tuple (spec 2026-07-09-unified-tuple §3).
  # Parse a comma-separated list of `[binder?:] type` positions (≥ 2). EVERY arity
  # (including 2) becomes `{:tuple_type, [arity: n, binders: bs], [t1…tn]}` — the
  # elaborator unfolds it to a UNIT-TERMINATED nested Σ telescope
  # (`Sigma(T1, λb1. … Sigma(Tn, λbn. Unit))`) which emit flattens to a flat BEAM
  # tuple. This is DELIBERATELY distinct from bare `Sigma(x:T, U)` (`:sigma_type`,
  # NOT unit-terminated): the terminator is what lets emit tell "flatten the whole
  # spine" from "this element is itself a nested tuple". Per-position binders are
  # retained so a later position may depend on an earlier one (dependent telescope);
  # an anonymous position is binder `"_"`.
  defp parse_tuple_type(state, name_token) do
    open_token = peek(state)
    state = advance(state)
    {positions, state} = parse_tuple_positions(state, [])

    binders = Enum.map(positions, &elem(&1, 0))
    types = Enum.map(positions, &elem(&1, 1))

    {state, close_token} =
      expect_container_close(state, :rparen, :tuple_type, open_token, types, true)

    meta = [arity: length(positions), binders: binders]
    meta = put_tuple_type_source_info(meta, name_token, open_token, types, close_token)
    ast = {:tuple_type, meta, types}

    {ast, state}
  end

  # A `[binder?:] type` position list, comma-separated, terminated by `:rparen`.
  defp parse_tuple_positions(state, acc) do
    {binder, state} =
      case {peek(state), peek_at(state, 1)} do
        {%Token{} = t, %Token{type: :colon}} ->
          {to_string(t.value), advance(advance(state))}

        _ ->
          {"_", state}
      end

    {type, state} = parse_type_expr(state)
    acc = [{binder, type} | acc]

    case peek(state) do
      %Token{type: :comma} -> parse_tuple_positions(advance(state), acc)
      _ -> {Enum.reverse(acc), state}
    end
  end

  # Soft-deprecate the legacy parenthesised tuple type `(A, B)` in favour of the value/type-consistent `%[A, B]`
  # sigil. Emitted only as a pipeline event (never a hard error) and only when events are on and a real file is
  # known, so `(A, B)` keeps compiling to identical output — the only change is the hint.
  defp deprecate_paren_tuple(%__MODULE__{emit_events: true, file: file} = state, token, arity)
       when is_binary(file) do
    Events.emit(
      :parser,
      :deprecation,
      %{
        code: "E086",
        arity: arity,
        message:
          "parenthesised tuple type `(A, B)` is deprecated; write `%[A, B]` (E086 / E-TYPE-TUPLE-PAREN; the tuple-type sigil matching the value tuple `%[a, b]`)"
      },
      Events.meta(file, token.line)
    )

    state
  end

  defp deprecate_paren_tuple(state, _token, _arity), do: state

  defp maybe_parse_function_type(state, left) do
    case peek(state) do
      %Token{type: :arrow} ->
        state = advance(state)
        {ret, state} = parse_type_arrow(state)

        params =
          case left do
            {:function_call, _, p} -> p
            _ -> [left]
          end

        ast = {:function_call, [name: "Function", function_type: true], params ++ [ret]}
        {ast, state}

      _ ->
        {left, state}
    end
  end

  # -- Effect List  ! Io, Exception ------------------------------------------

  defp parse_effect_list(state) do
    state = skip_newlines(state)
    {first, first_token, state} = parse_single_effect(state)

    {rest, last_token, state} =
      case peek(state) do
        %Token{type: :comma} ->
          state = advance(state)
          state = skip_newlines(state)
          {more, last_token, state} = parse_effect_list_tail(state)
          {more, last_token, state}

        _ ->
          {[], first_token, state}
      end

    {[first | rest], last_token, state}
  end

  defp parse_effect_list_tail(state) do
    {eff, effect_token, state} = parse_single_effect(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, last_token, state} = parse_effect_list_tail(state)
        {[eff | rest], last_token, state}

      _ ->
        {[eff], effect_token, state}
    end
  end

  defp parse_single_effect(state) do
    token = peek(state)
    state = advance(state)
    name = to_string(token.value)

    effect =
      case String.downcase(name) do
        "io" -> :io
        "state" -> :state
        "exception" -> :exception
        "spawn" -> :spawn
        "extern" -> :extern
        _ -> String.to_atom(String.downcase(name))
      end

    {effect, token, state}
  end

  # -- Constraint List  Proto(T), Proto2(U) ----------------------------------

  defp parse_requirements_clause(state) do
    case peek(state) do
      %Token{type: :identifier, value: "requires"} ->
        state |> advance() |> parse_constraint_list()

      %Token{type: :keyword, value: :where} = token ->
        state
        |> emit_constraint_where_deprecation(token)
        |> advance()
        |> parse_constraint_list()

      _ ->
        {[], state}
    end
  end

  defp parse_constraint_list(state) do
    {first, state} = parse_single_constraint(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_constraint_list(state)
        {[first | rest], state}

      _ ->
        {[first], state}
    end
  end

  defp parse_single_constraint(state) do
    # Proto(T) form
    name_token = peek(state)
    state = advance(state)
    name = to_string(name_token.value)

    case peek(state) do
      %Token{type: :lparen} ->
        open_token = peek(state)
        state = advance(state)
        {params, state} = parse_type_param_list(state)

        {state, close_token} =
          expect_container_close(state, :rparen, :type_arguments, open_token, params, true, %{type: name})

        whole = through_spans(name_token.span, close_token && close_token.span) || name_token.span

        meta =
          Metadata.put_source_info([name: name, constraint: true], %SourceInfo{
            whole: whole,
            name: name_token.span,
            opener: open_token.span,
            closer: close_token && close_token.span,
            arguments: params |> Enum.map(&ast_source_span/1) |> Enum.reject(&is_nil/1)
          })

        {{:function_call, meta, params}, state}

      _ ->
        meta =
          Metadata.put_source_info([constraint: true], %SourceInfo{
            whole: name_token.span,
            name: name_token.span
          })

        {{:variable, meta, name}, state}
    end
  end

  # -- Helpers: dotted names, name lists, definition blocks ------------------

  defp parse_dotted_name(state) do
    first = peek(state)
    state = advance(state)
    parse_dotted_name(state, to_string(first.value))
  end

  defp parse_dotted_name_owned(state) do
    first = peek(state)
    state = advance(state)
    parse_dotted_name_owned(state, to_string(first.value), first)
  end

  defp parse_dotted_name_owned(state, acc, last_token) do
    case peek(state) do
      %Token{type: :dot} ->
        next = peek_at(state, 1)

        if next && next.type in [:lbrace, :lbracket] do
          {acc, last_token, state}
        else
          state = advance(state)
          next_token = peek(state)
          state = advance(state)
          parse_dotted_name_owned(state, acc <> "." <> to_string(next_token.value), next_token)
        end

      _ ->
        {acc, last_token, state}
    end
  end

  defp parse_dotted_name(state, acc) do
    case peek(state) do
      %Token{type: :dot} ->
        # Don't consume dot if next token is { (selective import syntax)
        next = peek_at(state, 1)

        if next && next.type in [:lbrace, :lbracket] do
          {acc, state}
        else
          state = advance(state)
          next_token = peek(state)
          state = advance(state)
          parse_dotted_name(state, acc <> "." <> to_string(next_token.value))
        end

      _ ->
        {acc, state}
    end
  end

  defp parse_name_list(state, closing) do
    {names, _spans, state} = parse_name_list_with_spans(state, closing)
    {names, state}
  end

  defp parse_name_list_with_spans(state, closing) do
    # Explicit delimiters suspend indentation. A multiline selective import or
    # type-parameter list therefore carries lexer `:indent`/`:dedent` tokens in
    # addition to newlines; treating either as a name produced the misleading
    # "imported names need a comma" diagnostic at the first real item.
    state = skip_name_list_layout(state)

    case peek(state) do
      %Token{type: ^closing} ->
        {[], [], state}

      _ ->
        token = peek(state)
        state = advance(state)
        state = skip_name_list_layout(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            {rest, spans, state} = parse_name_list_with_spans(state, closing)
            {[to_string(token.value) | rest], [token.span | spans], state}

          _ ->
            {[to_string(token.value)], [token.span], state}
        end
    end
  end

  defp skip_name_list_layout(state) do
    case peek(state) do
      %Token{type: type} when type in [:newline, :indent, :dedent] ->
        state |> advance() |> skip_name_list_layout()

      _ ->
        state
    end
  end

  # Parse an indented block of definitions (for mod, proto, impl bodies)
  #
  # Tolerates doc_comment tokens that precede the leading `:indent` --
  # the lexer emits fenced `###...###` docstrings *before* measuring the
  # indentation of the line that follows, so a module body like
  #
  #     mod M
  #       ###
  #       description
  #       ###
  #       fn f() -> Int = 0
  #
  # will have the token stream `[mod, M, newline, doc_comment, indent,
  # fn, ...]`. Prior to v0.17.0 we would bail out with an empty body.
  # Now we carry the doc forward to attach to the first definition
  # inside the block (if any).
  defp parse_definition_block(state) do
    {stmts, leading_doc, state} = parse_definition_block_with_lead_doc(state)
    {attach_leading_doc(stmts, leading_doc), state}
  end

  # Variant of `parse_definition_block/1` used by container parsers that
  # want to interpret the leading `##` block as the container's own doc
  # (e.g. `mod Name`). Returns the doc separately so the caller can
  # attach it to the container meta instead of the first body statement.
  #
  # The lexer doesn't emit `:indent` for doc-comment-only lines, so a
  # module whose first body definition is preceded by its own `##`
  # block has a token stream of the shape
  #
  #     [mod, Name, newline, doc_module..., doc_first..., indent, def...]
  #
  # `collect_leading_docs/1` honours blank-line gaps and only consumes
  # the contiguous module-doc run, leaving `doc_first` in the stream.
  # To let parsing continue into the indented body, we look past any
  # further doc comments when searching for `:indent`, and feed the
  # first-definition doc back in via `attach_leading_doc/2` so it
  # binds to the first body statement.
  defp parse_definition_block_with_lead_doc(state) do
    {leading_doc, state} = collect_leading_docs(state)
    {pending_first_doc, state} = collect_leading_docs(state)
    {leading_comments, state} = collect_leading_line_comments(state)

    case peek(state) do
      %Token{type: :indent} ->
        token = peek(state)
        state = advance(state)
        {stmts, state} = parse_block_body(state, token.value)
        state = expect_dedent(state)

        stmts = prepend_line_comments(stmts, leading_comments)
        stmts = attach_leading_doc(stmts, pending_first_doc)

        {stmts, leading_doc, state}

      _ ->
        {[], leading_doc, state}
    end
  end

  # Collect any doc_comment tokens (intermixed with newlines) and return
  # their concatenated text plus the advanced state. Returns `{"", state}`
  # when there are no doc comments to consume.
  defp collect_leading_docs(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :doc_comment} ->
        {text, state} = collect_doc_comments(state)
        state = skip_newlines(state)
        {text, state}

      _ ->
        {"", state}
    end
  end

  # Collect `:line_comment` tokens that appear on indented comment-only
  # lines before the block's `:indent` token. The lexer emits them at
  # their measured column but *ahead* of the indent push (to avoid
  # treating a comment-only line as starting the block), so we route
  # them back inside the block body here.
  defp collect_leading_line_comments(state) do
    state = skip_newlines(state)
    collect_leading_line_comments(state, [])
  end

  defp collect_leading_line_comments(state, acc) do
    case peek(state) do
      %Token{type: :line_comment} ->
        {node, state} = consume_line_comment(state)
        state = skip_newlines(state)
        collect_leading_line_comments(state, [node | acc])

      _ ->
        {Enum.reverse(acc), state}
    end
  end

  defp prepend_line_comments(stmts, []), do: stmts
  defp prepend_line_comments(stmts, comments), do: comments ++ stmts

  defp attach_leading_doc([first | rest], doc) when doc != "" do
    [attach_doc(first, doc) | rest]
  end

  defp attach_leading_doc(stmts, _doc), do: stmts

  # -- Decorator Attachment (@name before fn) --------------------------------

  defp parse_at(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    state = advance(state)
    dec_name = to_string(name_token.value)

    # Check if it's a call: @name(args) or @name value (bare boolean)
    {args, close_token, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {a, _labels, _label_spans, state, close_token} = parse_call_args(state, false)
          {a, close_token, state}

        %Token{type: :bool, value: bval} ->
          state = advance(state)
          arg = {:literal, [subtype: :boolean], bval}
          {[arg], nil, state}

        _ ->
          {[], nil, state}
      end

    decorator_info = decorator_source_info(token, name_token, args, close_token)

    state = skip_newlines(state)

    # Module-level decorators (e.g. `@group(:core)`) describe the MODULE. The
    # canonical form is `@group(:g)` directly above `mod`, where it attaches to
    # the module container (spec 2026-07-10-group-decorator-placement). The
    # in-body form is deprecated, not fatal: hard-failing would make a file using
    # the old placement unparseable — and therefore un-migratable — so we mirror
    # the `if`→`pickup` path (emit a deprecation event, keep the decorator node)
    # and let `cure migrate`'s @group-hoist rule relocate it to the canonical spot.
    # `@edition("YYYY")` is a standalone file-leading pragma, not a decorator
    # that attaches to a following declaration. It must appear before any
    # substantive statement; a misplaced one is a HARD parse error (stricter
    # than @group's soft-deprecation path, because the edition selects the
    # keyword set and cannot be honoured once parsing is underway). A
    # well-placed pragma carries its edition value on the {:decorator, …} node's
    # args (the "2026" string literal).
    if dec_name == "edition" do
      # Placement first (F1/F3: must be file-leading; a second pragma is no longer
      # leading), then argument validation (F7: must be a "YYYY" string literal, not
      # an unquoted int / non-year string / bare pragma). Mark the file as past its
      # leading position afterwards so a subsequent `@edition` is caught as misplaced.
      state =
        cond do
          not file_leading?(state) ->
            add_error(state, edition_pragma_error(:edition_pragma_placement, token, decorator_info, args))

          not valid_edition_pragma_arg?(args) ->
            add_error(state, edition_pragma_error(:edition_pragma_malformed, token, decorator_info, args))

          not single_line_edition_pragma?(token, args) ->
            # Canonical pragma is a single line. The pre-parse resolver
            # (Cure.Edition.pragma_edition) reads the pragma with a single-line
            # regex, so a multi-line pragma is invisible to it — honouring it here
            # would lex under the resolver's (default) edition while accepting a
            # different declared one (F1, audit iteration 4). Reject it as malformed.
            add_error(state, edition_pragma_error(:edition_pragma_malformed, token, decorator_info, args))

          not known_edition_pragma_arg?(args) ->
            # Well-formed "YYYY" but not a minted edition. The compile entrypoints
            # (compiler.ex compile_string/compile_and_load) resolve the edition via
            # Cure.Edition.resolve BEFORE lex/parse and already reject a typo there,
            # so on that path this branch never fires. It remains the allow-list
            # gate for DIRECT Parser.parse callers that skip resolve_edition
            # (detect_app, parse_source) — spec §3.1 ("a typo'd edition must fail
            # loudly") / §3.3 ("its argument is validated as an edition").
            add_error(state, edition_pragma_error(:edition_pragma_unknown, token, decorator_info, args))

          true ->
            state
        end

      state = %{state | seen_stmt?: true}
      meta = standalone_decorator_meta(dec_name, token, decorator_info)
      ast = {:decorator, meta, args}
      {ast, state}
    else
      if dec_name in @module_level_decorators do
        case peek(state) do
          %Token{type: :keyword, value: :mod} ->
            {mod_ast, state} = parse_module(state)
            {attach_decorator(mod_ast, dec_name, args, decorator_info), state}

          _ ->
            state = emit_group_placement_deprecation(state, token, dec_name)
            meta = standalone_decorator_meta(dec_name, token, decorator_info)
            ast = {:decorator, meta, args}
            {ast, state}
        end
      else
        parse_at_attach(state, token, dec_name, args, decorator_info)
      end
    end
  end

  # Attach `@name(args)` to a following fn/rec/type declaration, or emit a
  # standalone decorator/property node when nothing attachable follows.
  defp parse_at_attach(state, token, dec_name, args, decorator_info) do
    # Check if the next thing is a function definition -- if so, attach decorator
    case peek(state) do
      %Token{type: :keyword, value: kw} when kw in [:fn, :local] ->
        {fn_ast, state} = parse_expr(state, 0)
        fn_ast = attach_decorator(fn_ast, dec_name, args, decorator_info)
        {fn_ast, state}

      # v0.19.0: `@derive(Show, Eq, ...) rec Name` attaches the
      # derive list to the record container.
      %Token{type: :keyword, value: :rec} ->
        {rec_ast, state} = parse_expr(state, 0)
        rec_ast = attach_decorator(rec_ast, dec_name, args, decorator_info)
        {rec_ast, state}

      # `@builtin(:key) type Name = ...` attaches the decorator to the type
      # container (an enum ADT → {:container, container_type: :enum, ...}, which
      # attach_decorator/3's generic clause threads into :decorator meta).
      # `@builtin(:key) type Name indices (...)` attaches to the {:indexed_type}
      # meta (Bounded's GADT family). A @builtin on an alias ({:type_annotation})
      # form is still silently dropped — no attach_decorator clause today.
      %Token{type: :keyword, value: :type} ->
        {type_ast, state} = parse_type_def(state)
        type_ast = attach_decorator(type_ast, dec_name, args, decorator_info)
        {type_ast, state}

      # `@erases(:pid) opaque type Name` attaches the decorator to the opaque
      # container. Like the `type` branch, parse_type_def/2 builds a {:container, …}
      # node that attach_decorator/3's generic clause threads into :decorator meta —
      # but the `opaque` keyword must be consumed first (see the statement
      # dispatcher). Without this branch the decorator is silently dropped and the
      # carrier is left with no declared erasure.
      %Token{type: :keyword, value: :opaque} ->
        {type_ast, state} = parse_type_def(advance(state), opaque: true)
        type_ast = attach_decorator(type_ast, dec_name, args, decorator_info)
        {type_ast, state}

      # `@builtin(:tag) primitive Name` attaches the decorator to the primitive
      # container (the generic {:container, …} attach_decorator clause writes it
      # into :decorator meta, like `@builtin(:key) type Name`).
      %Token{type: :keyword, value: :primitive} ->
        {prim_ast, state} = parse_primitive_def(state)
        prim_ast = attach_decorator(prim_ast, dec_name, args, decorator_info)
        {prim_ast, state}

      # `@prelude typealias Name = RHS` attaches the decorator to the
      # `{:type_annotation}` synonym node (see attach_decorator's clause). Used so
      # a transparent alias like `String = List(Char)` can join the implicit
      # prelude at its definition site.
      %Token{type: :keyword, value: :typealias} ->
        {ta_ast, state} = parse_typealias(state)
        ta_ast = attach_decorator(ta_ast, dec_name, args, decorator_info)
        {ta_ast, state}

      _ ->
        # Standalone decorator or property
        if args != [] do
          meta = standalone_decorator_meta(dec_name, token, decorator_info)
          ast = {:decorator, meta, args}
          {ast, state}
        else
          ast = {:property, [name: dec_name, line: token.line, col: token.col], dec_name}
          {ast, state}
        end
    end
  end

  defp attach_decorator(fn_ast, dec_name, args, decorator_info) do
    case fn_ast do
      {:container, meta, body} ->
        meta = put_decorator_source_info(meta, dec_name, decorator_info)
        # Record container with @derive(Show, Eq, Ord).
        case Keyword.get(meta, :container_type) do
          :struct when dec_name == "derive" ->
            derive_names =
              Enum.map(args, fn
                {:variable, _, n} -> normalize_derived_interface(n)
                {:function_call, m, _} -> Keyword.get(m, :name, "") |> normalize_derived_interface()
                other -> other |> extract_literal_value() |> to_string() |> normalize_derived_interface()
              end)

            {:container, Keyword.put(meta, :deriving, derive_names), body}

          _ ->
            {:container, Keyword.put(meta, :decorator, {:decorator, [name: String.to_atom(dec_name)], args}), body}
        end

      # `@builtin(:key) type Name indices (...)` — a GADT / indexed family.
      # Thread the decorator into the indexed_type meta so
      # program.ex's maybe_register_builtin can see it (mirrors the
      # {:container} enum-ADT clause above).
      {:indexed_type, meta, ctors} ->
        meta = put_decorator_source_info(meta, dec_name, decorator_info)
        {:indexed_type, Keyword.put(meta, :decorator, {:decorator, [name: String.to_atom(dec_name)], args}), ctors}

      {:function_def, meta, body} ->
        meta = put_decorator_source_info(meta, dec_name, decorator_info)

        decoration =
          case dec_name do
            "extern" ->
              # @extern(:mod, :fun, arity) -> extern: {mod, fun, arity}
              extern_val =
                case args do
                  [m, f, a] -> {extract_literal_value(m), extract_literal_value(f), extract_literal_value(a)}
                  _ -> args
                end

              [extern: extern_val]

            _ ->
              [decorator: {:decorator, [name: String.to_atom(dec_name)], args}]
          end

        {:function_def, meta ++ decoration, body}

      # `@prelude typealias Name = RHS` — a transparent type synonym. Thread the
      # decorator into the `{:type_annotation}` meta so program.ex's prelude
      # discovery can see it (mirrors the `{:container}`/`{:indexed_type}` clauses).
      {:type_annotation, meta, rhs} ->
        meta = put_decorator_source_info(meta, dec_name, decorator_info)
        {:type_annotation, Keyword.put(meta, :decorator, {:decorator, [name: String.to_atom(dec_name)], args}), rhs}

      other ->
        other
    end
  end

  # Decorator spellings follow the current standard-library interface names.
  # `Ord` and `Eq` remain accepted migration aliases, but the declaration table
  # only ever sees canonical identities.
  defp normalize_derived_interface("Ord"), do: "Comparable"
  defp normalize_derived_interface("Eq"), do: "Equatable"
  defp normalize_derived_interface(name), do: name

  defp decorator_source_info(%Token{} = at, %Token{} = name, args, close_token) do
    last = if match?(%Token{}, close_token), do: close_token, else: name

    whole =
      case {at.span, last.span} do
        {%Cure.Diagnostic.Span{} = first, %Cure.Diagnostic.Span{} = final} ->
          case Range.through(first, final) do
            {:ok, span} -> span
            _ -> nil
          end

        _ ->
          nil
      end

    argument_spans =
      Enum.flat_map(args, fn
        {_tag, meta, _payload} when is_list(meta) ->
          case Metadata.source_info(meta) do
            %SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> [span]
            _ -> []
          end

        _ ->
          []
      end)

    %{whole: whole, name: name.span, arguments: argument_spans}
  end

  defp edition_pragma_error(kind, token, decorator_info, args) do
    argument_span = List.first(decorator_info.arguments)
    single_line? = match?(%Cure.Diagnostic.Span{start_line: line, end_line: line}, decorator_info.whole)

    span =
      cond do
        kind == :edition_pragma_placement -> decorator_info.whole
        not single_line? -> decorator_info.whole
        true -> argument_span || decorator_info.whole
      end

    details = %{
      span: span,
      pragma_span: decorator_info.whole,
      argument_span: argument_span,
      observed: edition_pragma_argument(args),
      known_editions: Cure.Edition.all(),
      single_line: single_line?,
      line: token.line,
      column: token.col
    }

    {kind, details}
  end

  defp edition_pragma_argument([{:literal, _meta, value}]), do: value
  defp edition_pragma_argument([]), do: :missing
  defp edition_pragma_argument(args), do: Enum.map(args, &edition_pragma_argument_value/1)

  defp edition_pragma_argument_value({:literal, _meta, value}), do: value
  defp edition_pragma_argument_value({:variable, _meta, value}), do: value
  defp edition_pragma_argument_value(_argument), do: :invalid

  defp put_decorator_source_info(meta, dec_name, decorator_info) do
    case Metadata.source_info(meta) do
      %SourceInfo{} = info ->
        Keyword.put(meta, :source_info, %{info | decorators: Map.put(info.decorators, dec_name, decorator_info)})

      _ ->
        meta
    end
  end

  defp standalone_decorator_meta(dec_name, token, decorator_info) do
    info = %SourceInfo{
      whole: decorator_info.whole,
      name: decorator_info.name,
      arguments: decorator_info.arguments
    }

    Metadata.put_source_info([name: dec_name, line: token.line, col: token.col], info)
  end

  defp extract_literal_value({:literal, _, val}), do: val

  # `@extern(Some.Foreign.Module, :f, 1)` parses the first argument
  # as a chain of attribute accesses rooted in a PascalCase variable.
  # Collapse that chain to an atom so codegen receives a literal atom.
  defp extract_literal_value({:attribute_access, _, _} = ast) do
    case attribute_access_to_dotted(ast) do
      nil -> ast
      name -> String.to_atom(name)
    end
  end

  defp extract_literal_value({:variable, _, name}) when is_binary(name) do
    case name do
      <<c, _::binary>> when c in ?A..?Z -> String.to_atom(name)
      _ -> name
    end
  end

  defp extract_literal_value(other), do: other

  defp attribute_access_to_dotted({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute)

    case attribute_access_to_dotted(parent) do
      nil -> nil
      path -> path <> "." <> to_string(attr)
    end
  end

  defp attribute_access_to_dotted({:variable, _, name}) when is_binary(name), do: name
  defp attribute_access_to_dotted(_), do: nil

  # -- Keyword unary (return, throw, yield, spawn) ---------------------------

  defp parse_keyword_unary(state, node_type) do
    token = peek(state)
    state = advance(state)
    {expr, state} = parse_expr(state, 0)
    meta = put_keyword_unary_source_info([line: token.line, col: token.col], token, expr)
    ast = {node_type, meta, [expr]}
    {ast, state}
  end

  defp put_keyword_unary_source_info(meta, %Token{span: %Cure.Diagnostic.Span{} = first}, expr) do
    body = ast_source_span(expr)

    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(first, body) || first,
      name: first,
      body: body
    })
  end

  defp put_keyword_unary_source_info(meta, _token, _expr), do: meta

  # -- Quasiquote (SP5.1) ----------------------------------------------------

  # `quote <form>` lifts the following Cure form to a `Std.Syntax.Syntax`
  # value. The inner form is parsed by the ordinary expression grammar, so
  # splice holes (`$(...)`) nest anywhere within it: `parse_prefix` emits a
  # `:splice` / `:splice_group` node wherever `$(` appears. The macro
  # frontend lowers `:quoted_syntax` to `Std.Syntax` builder calls (with each
  # hole spliced in) via the `to_syntax`/`to_core` bridge in `macro_syntax.ex`;
  # this stays pure surface sugar (TCB delta 0). Declaration-form quoting
  # rides the same node — a `type`/`fn` form parses through `parse_expr` here.
  defp parse_quote(state) do
    token = peek(state)
    state = advance(state)
    {inner, state} = parse_expr(state, 0)
    ast = {:quoted_syntax, [line: token.line, col: token.col], [inner]}
    {ast, state}
  end

  # `$(e)` single-node splice / `$(e ...)` repeated-group splice. The trailing
  # `...` (a `:ellipsis` token) marks splice-all: `e : List(Syntax)` flattened
  # into the enclosing node's child sequence (Scheme `,@` analog). Without it,
  # `e : Syntax` fills one child position. The `:splice_open` token already
  # consumed the `$(`; we close on `)`.
  defp parse_splice(state, open_token) do
    state = advance(state)
    {expr, state} = parse_expr(state, 0)
    meta = [line: open_token.line, col: open_token.col]

    case peek(state) do
      %Token{type: :ellipsis} ->
        state = advance(state)

        {state, close_token} =
          expect_container_close(state, :rparen, :splice_group, open_token, [expr], false)

        meta = put_splice_source_info(meta, open_token, close_token, expr)
        {{:splice_group, meta, [expr]}, state}

      _ ->
        {state, close_token} =
          expect_container_close(state, :rparen, :splice, open_token, [expr], false)

        meta = put_splice_source_info(meta, open_token, close_token, expr)
        {{:splice, meta, [expr]}, state}
    end
  end

  defp put_splice_source_info(
         meta,
         %Token{span: %Cure.Diagnostic.Span{} = opener},
         %Token{span: %Cure.Diagnostic.Span{} = closer},
         expression
       ) do
    Metadata.put_source_info(meta, %SourceInfo{
      whole: through_spans(opener, closer),
      opener: opener,
      closer: closer,
      body: ast_source_span(expression)
    })
  end

  defp put_splice_source_info(meta, _open_token, _close_token, _expression), do: meta

  # -- Send ------------------------------------------------------------------

  # The keyword statement form `send target, message` desugars to the
  # same `{:send, meta, [target, message]}` node emitted by the
  # Melquiades operator so downstream stages (type checker, codegen,
  # effects) have a single shape to reason about. `:melquiades_form` is
  # set to `:keyword` to let the printer round-trip the statement form.
  defp parse_send(state) do
    token = peek(state)
    state = advance(state)
    {target, state} = parse_expr(state, 0)
    state = expect_send_comma(state, token, target)
    {message, state} = parse_expr(state, 0)
    meta = [line: token.line, col: token.col, melquiades_form: :keyword]
    ast = {:send, meta, [target, message]}
    {ast, state}
  end

  defp expect_send_comma(state, send_token, target) do
    case expect_token(state, :comma) do
      {:ok, _comma, next_state} ->
        next_state

      {:error, next_state} ->
        [_generic | rest] = next_state.errors
        observed = peek(next_state)

        error =
          {:declaration_separator_missing,
           %{
             kind: :send_comma_missing,
             expected: :comma,
             observed: observed.value || observed.type,
             token_type: observed.type,
             span: zero_width_start(observed.span),
             observed_span: observed.span,
             opener_span: send_token.span,
             previous_span: first_node_source_span(target),
             line: observed.line,
             column: observed.col
           }}

        %{next_state | errors: [error | rest]}
    end
  end

  # -- Receive ---------------------------------------------------------------

  defp parse_receive(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    # Parse like match arms
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {arms, state} = parse_block_match_arms(state)
        state = expect_dedent(state)

        # Optional after timeout
        {timeout, state} =
          case peek(state) do
            %Token{type: :keyword, value: :after} ->
              state = advance(state)
              {timeout_expr, state} = parse_expr(state, 0)
              state = skip_newlines(state)
              {timeout_body, state} = parse_block(state)
              {{timeout_expr, timeout_body}, state}

            _ ->
              {nil, state}
          end

        meta = [line: token.line, col: token.col]
        meta = if timeout, do: Keyword.put(meta, :timeout, timeout), else: meta
        ast = {:async_operation, meta, arms}
        {ast, state}

      _ ->
        ast = {:async_operation, [line: token.line, col: token.col], []}
        {ast, state}
    end
  end

  # -- Try / Catch / Finally -------------------------------------------------

  defp parse_try(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    {try_body, state} = parse_block(state)
    state = skip_newlines(state)

    # catch clause
    {catch_arms, state} =
      case peek(state) do
        %Token{type: :keyword, value: :catch} ->
          state = advance(state)
          state = skip_newlines(state)

          case peek(state) do
            %Token{type: :indent} ->
              state = advance(state)
              {arms, state} = parse_block_match_arms(state)
              state = expect_dedent(state)
              {arms, state}

            _ ->
              {[], state}
          end

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # finally clause
    {finally_body, state} =
      case peek(state) do
        %Token{type: :keyword, value: :finally} ->
          state = advance(state)
          state = skip_newlines(state)
          {body, state} = parse_block(state)
          {body, state}

        _ ->
          {nil, state}
      end

    children = [try_body | catch_arms]
    children = if finally_body, do: children ++ [finally_body], else: children
    ast = {:exception_handling, [line: token.line, col: token.col], children}
    {ast, state}
  end

  # -- Block Parsing ---------------------------------------------------------

  defp parse_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        token = peek(state)
        state = advance(state)
        {exprs, state} = parse_block_body(state, token.value)
        state = expect_dedent(state)

        case exprs do
          [single] -> {single, state}
          many -> {{:block, [line: token.line, col: token.col], many}, state}
        end

      _ ->
        # Single expression as body (no indent)
        parse_expr(state, 0)
    end
  end

  defp parse_block_body(state, indent) do
    state = skip_newlines(state)
    parse_block_body(state, [], indent)
  end

  defp parse_block_body(state, acc, indent) do
    case peek(state) do
      %Token{type: :dedent, value: value}
      when is_integer(indent) and is_integer(value) and value > indent ->
        state
        |> advance()
        |> skip_newlines()
        |> parse_block_body(acc, indent)

      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :line_comment} ->
        {node, state} = consume_line_comment(state)
        state = skip_newlines(state)
        parse_block_body(state, [node | acc], indent)

      %Token{type: :doc_comment} ->
        # Collect consecutive doc comment blocks -- including ones
        # separated by blank-line gaps -- so that prose split across
        # paragraphs (or intermixed with plain `#` comments the lexer
        # drops) still attaches to the following definition as a
        # single docstring.
        {doc_text, state} = collect_all_doc_comments(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: type} when type in [:dedent, :eof] ->
            {Enum.reverse(acc), state}

          _ ->
            prev_errors = length(state.errors)
            {expr, state} = parse_expr(state, 0)
            expr = attach_doc(expr, doc_text)
            # If this expression introduced new parse errors, skip to the next
            # statement boundary (E063 recovery) so the broken statement cannot
            # consume tokens that belong to subsequent well-formed definitions.
            state =
              if length(state.errors) > prev_errors,
                do: synchronize_to_statement(state),
                else: state

            state = skip_newlines(state)
            parse_block_body(state, [expr | acc], indent)
        end

      _ ->
        prev_errors = length(state.errors)
        {expr, state} = parse_expr(state, 0)
        # Recovery: if this expression introduced parse errors, synchronize to
        # the next statement boundary before continuing so subsequent
        # well-formed definitions are not consumed as part of the failed parse.
        state =
          if length(state.errors) > prev_errors,
            do: synchronize_to_statement(state),
            else: state

        state = skip_newlines(state)
        parse_block_body(state, [expr | acc], indent)
    end
  end

  # Parse either a block (if indent follows) or a single expression
  defp parse_expr_or_block(state) do
    case peek(state) do
      %Token{type: :indent} -> parse_block(state)
      _ -> parse_expr(state, 0)
    end
  end

  defp parse_expression_let_chain_body({:assignment, meta, _} = assignment, state) do
    if Keyword.get(meta, :let) do
      parse_expression_let_chain_tail([assignment], state, meta)
    else
      {assignment, state}
    end
  end

  defp parse_expression_let_chain_body(body, state), do: {body, state}

  defp parse_expression_let_chain_tail(acc, state, meta) do
    state = skip_newlines(state)

    if expression_let_chain_tail?(state) do
      {expr, state} = parse_expr_or_block(state)
      acc = [expr | acc]

      case expr do
        {:assignment, expr_meta, _} ->
          if Keyword.get(expr_meta, :let) do
            parse_expression_let_chain_tail(acc, state, meta)
          else
            {{:block, [line: Keyword.get(meta, :line, 1), col: Keyword.get(meta, :col, 1)], Enum.reverse(acc)}, state}
          end

        _ ->
          {{:block, [line: Keyword.get(meta, :line, 1), col: Keyword.get(meta, :col, 1)], Enum.reverse(acc)}, state}
      end
    else
      case Enum.reverse(acc) do
        [single] -> {single, state}
        many -> {{:block, [line: Keyword.get(meta, :line, 1), col: Keyword.get(meta, :col, 1)], many}, state}
      end
    end
  end

  defp expression_let_chain_tail?(state) do
    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof, :bar, :comma, :rparen, :rbracket, :rbrace] ->
        false

      %Token{type: :keyword, value: value}
      when value in [:fn, :local, :type, :proto, :impl, :mod, :use] ->
        false

      _ ->
        true
    end
  end

  # -- Token Helpers ---------------------------------------------------------

  # Store `tokens` as a tuple + cached `count`. This is the single writer for
  # both fields; keeping them in lockstep is what makes O(1) lookup safe.
  defp put_tokens(state, tokens) when is_list(tokens) do
    %{state | tokens: List.to_tuple(tokens), count: length(tokens)}
  end

  # Token at an absolute index, or nil when out of range — mirroring the
  # `Enum.at/2` semantics the callers were written against.
  defp token_at(%{tokens: tokens, count: count}, idx) when idx >= 0 and idx < count do
    elem(tokens, idx)
  end

  defp token_at(_state, _idx), do: nil

  # The tokens from `pos` to the end, as a list. Callers that scan or split the
  # remaining stream want a list; this is O(n) like the `Enum.drop/2` it
  # replaces, and unlike `peek/1` it is not on the hot path.
  defp tokens_from(%{tokens: tokens, count: count}, pos) do
    start = max(pos, 0)

    # Clamp before building the range: `start..(count - 1)` would otherwise be a
    # descending range (and index a nonexistent element) once start > count - 1.
    if start >= count do
      []
    else
      for idx <- start..(count - 1), do: elem(tokens, idx)
    end
  end

  defp peek(%{count: count, pos: pos}) when pos >= count do
    Token.new(:eof, nil, 1, 1)
  end

  defp peek(%{tokens: tokens, pos: pos}), do: elem(tokens, pos)

  # Look n tokens past the current position (peek_ahead(state, 0) == peek(state)).
  defp peek_ahead(%{pos: pos} = state, n), do: token_at(state, pos + n)

  defp peek_at(%{pos: pos} = state, offset), do: token_at(state, pos + offset)

  defp advance(state), do: %{state | pos: state.pos + 1}

  # `:line_comment` tokens are emitted by the lexer only when
  # `preserve_comments: true` is set. In that mode `parse_program/2`
  # and `parse_block_body/2` peek for them explicitly *before* calling
  # `skip_newlines/1` and turn them into `{:comment, meta, text}` AST
  # nodes. Inside expressions they are absent from the stream because
  # the lexer places them at line boundaries.
  defp skip_newlines(state) do
    case peek(state) do
      %Token{type: :newline} -> skip_newlines(advance(state))
      _ -> state
    end
  end

  # Like `skip_newlines`, but also skips `##`/`#` comment tokens. Used where a comment may
  # document the first constructor of a `type … indices` block: such a comment lands before the
  # block's `:indent` token, so plain `skip_newlines` would leave `peek` on the comment and
  # defeat block-open detection (E5).
  defp skip_newlines_and_comments(state) do
    case peek(state) do
      %Token{type: :newline} -> skip_newlines_and_comments(advance(state))
      %Token{type: t} when t in [:doc_comment, :line_comment] -> skip_newlines_and_comments(advance(state))
      _ -> state
    end
  end

  defp expect_token(state, expected_type) do
    token = peek(state)

    if token.type == expected_type do
      {:ok, token, advance(state)}
    else
      error = {:expected_token, expected_type, token.type, token.value, token.line, token.col, token.span}
      {:error, add_error(state, error)}
    end
  end

  defp expect_implementation_for(state, opener, head_span, head_name, family) do
    observed = peek(state)

    case observed do
      %Token{type: :keyword, value: :for} = for_token ->
        {for_token, advance(state)}

      %Token{type: :keyword} ->
        error =
          {:declaration_separator_missing,
           %{
             kind: :implementation_for_keyword_missing,
             expected: :for,
             observed: macro_separator_observed(observed),
             token_type: observed.type,
             span: observed.span,
             opener_span: opener.span,
             previous_span: head_span,
             declaration: head_name,
             family: family,
             repair: :replace,
             line: observed.line,
             column: observed.col
           }}

        {nil, state |> add_error(error) |> advance()}

      _ ->
        error =
          {:declaration_separator_missing,
           %{
             kind: :implementation_for_keyword_missing,
             expected: :for,
             observed: macro_separator_observed(observed),
             token_type: observed.type,
             span: observed.span,
             opener_span: opener.span,
             previous_span: head_span,
             declaration: head_name,
             family: family,
             repair: :insert,
             line: observed.line,
             column: observed.col
           }}

        {nil, add_error(state, error)}
    end
  end

  defp expect_dedent(state) do
    case peek(state) do
      %Token{type: :dedent} -> advance(state)
      _ -> state
    end
  end

  # File-leading = no substantive (non-decorator, non-comment) top-level
  # statement has yet been consumed. `@edition` must be the first thing in a
  # file (comments/blanks aside); this flag is what the pragma-placement check
  # in parse_at/1 reads.
  defp file_leading?(state), do: not state.seen_stmt?

  # A well-formed `@edition` argument is exactly one string literal holding a
  # 4-digit year (matching Cure.Edition's pre-parse `pragma_capture` regex).
  # Anything else — unquoted int, non-year string, missing arg — is malformed.
  defp valid_edition_pragma_arg?([{:literal, meta, val}]) do
    # `\A..\z` (not `^..$`): `$` also matches just before a trailing newline, so
    # `^\d{4}$` would accept "2026\n". A pragma literal has no embedded newline
    # today, so this is belt-and-suspenders — but the intent is exactly-4-digits.
    Keyword.get(meta, :subtype) == :string and is_binary(val) and
      Regex.match?(~r/\A\d{4}\z/, val)
  end

  defp valid_edition_pragma_arg?(_), do: false

  # A well-formed pragma arg whose value is a KNOWN edition (allow-list membership
  # via Cure.Edition — the single source of truth). Presupposes the format check
  # (`valid_edition_pragma_arg?`) already passed; a non-known "YYYY" string is an
  # :edition_pragma_unknown error rather than a silent accept.
  defp known_edition_pragma_arg?([{:literal, _meta, val}]) when is_binary(val),
    do: Cure.Edition.valid?(val)

  defp known_edition_pragma_arg?(_), do: false

  # The canonical `@edition("YYYY")` pragma is a single line: the string literal
  # sits on the same line as the `@`. A pragma split across lines is invisible to
  # the single-line pre-parse resolver (Cure.Edition.pragma_edition), so it must
  # not be honoured here (F1). Presupposes valid_edition_pragma_arg? passed, so
  # args is a one-element literal list; a non-literal arg is treated as single-line
  # (it will already have failed the format check).
  defp single_line_edition_pragma?(token, [{:literal, meta, _}]),
    do: Keyword.get(meta, :line) == token.line

  defp single_line_edition_pragma?(_token, _args), do: true

  # Mark that a substantive top-level statement is about to be parsed. Comments
  # are NOT substantive. A decorator prefix (`:at`) is substantive UNLESS it is a
  # leading `@edition(...)` pragma — every other decorator (`@extern`, `@derive`,
  # `@builtin`, `@group`, ...) leads a real definition and must flip the flag, so
  # an `@edition` that follows a decorated definition is correctly seen as
  # misplaced (audit F1). Called just before a top-level `parse_expr`, so the
  # flag is set BEFORE descending into a module body, letting an in-body
  # `@edition` be detected as misplaced.
  defp mark_seen_if_stmt(state) do
    case peek(state) do
      %Token{type: type} when type in [:line_comment, :doc_comment] ->
        state

      %Token{type: :at} ->
        if edition_pragma_next?(state), do: state, else: %{state | seen_stmt?: true}

      _ ->
        %{state | seen_stmt?: true}
    end
  end

  # True when the upcoming `@name` decorator is specifically `@edition` — the one
  # non-substantive decorator (a file-leading pragma, not a definition prefix).
  defp edition_pragma_next?(state) do
    case peek_ahead(state, 1) do
      %Token{value: v} -> to_string(v) == "edition"
      _ -> false
    end
  end

  defp add_error(state, error) do
    if state.emit_events do
      Events.emit(:parser, :error, error, Events.meta(state.file, 1))
    end

    %{state | errors: [error | state.errors]}
  end

  # PICKUP §17 / MATCH §10: emit a deprecation event whenever the
  # legacy `if` keyword is parsed. The event payload identifies the
  # spec-reserved diagnostic code `E-IF-REMOVED` so subscribers (the
  # LSP, the `mix cure.rewrite` task) can surface the migration hint.
  # Subsequent `elif` branches reuse the same `parse_if/1` recursive
  # call site -- and therefore the same emission point -- so a chained
  # `if/elif/elif/else` produces one event per branch, which is the
  # right granularity for editor diagnostics.
  defp emit_if_deprecation(state, token) do
    if state.emit_events do
      payload =
        {:if_deprecated, "`if`/`elif` are deprecated; rewrite as `pickup` (E-IF-REMOVED, see docs/PICKUP.md §17)",
         line: token.line, col: token.col}

      Events.emit(:parser, :deprecation, payload, Events.meta(state.file, token.line))
    end

    state
  end

  defp emit_constraint_where_deprecation(state, token) do
    if state.emit_events do
      payload =
        {:constraint_where_deprecated,
         "constraint-position `where` is deprecated; write `requires` (`where` now introduces function-local definitions)",
         line: token.line, col: token.col}

      Events.emit(:parser, :deprecation, payload, Events.meta(state.file, token.line))
    end

    state
  end

  # A module-level decorator (`@group`) placed somewhere other than directly above
  # `mod` is the deprecated in-body form. Mirroring `emit_if_deprecation/2`, emit a
  # deprecation event (spec-reserved code `E-GROUP-PLACEMENT`) rather than a hard
  # error, so the file still parses and the @group-hoist migration can relocate it.
  defp emit_group_placement_deprecation(state, token, dec_name) do
    if state.emit_events do
      payload =
        {:group_not_above_module,
         "@#{dec_name}(...) belongs directly above `mod`; rewrite via `cure migrate` " <>
           "(E-GROUP-PLACEMENT, see docs/superpowers/specs/2026-07-10-group-decorator-placement)",
         line: token.line, col: token.col}

      Events.emit(:parser, :deprecation, payload, Events.meta(state.file, token.line))
    end

    state
  end

  # After a parse error, skip forward until a safe statement boundary:
  # a newline, dedent, or eof ends the current statement, and a
  # definition-opening keyword (fn, mod, rec, ...) starts the next one.
  # This prevents a broken statement from silently consuming tokens that
  # belong to subsequent well-formed definitions (E063 recovery).
  defp synchronize_to_statement(state) do
    case peek(state) do
      %Token{type: type} when type in [:eof, :dedent, :newline] ->
        state

      %Token{type: :keyword, value: kw} when kw in @definition_keywords ->
        state

      _ ->
        synchronize_to_statement(advance(state))
    end
  end

  # -- Doc Comment Helpers -----------------------------------------------------

  defp collect_doc_comments(state) do
    collect_doc_comments(state, [], nil)
  end

  # Collect a contiguous run of `:doc_comment` tokens, using the source
  # line numbers already on the tokens to break on a blank-line gap.
  # Blank lines don't produce tokens (the lexer eats them silently), so
  # consecutive doc comments appear adjacent in the stream; compare
  # their source lines to tell `## foo\n## bar` (adjacent, line delta 1
  # for single-line `##` tokens) from `## foo\n\n## bar` (separated,
  # line delta 2+). A gap terminates the run so the next `##` block
  # binds to the following definition rather than to the leading doc.
  #
  # Split into two clauses so the integer arithmetic on `prev_line` is
  # never evaluated against `nil`; dialyzer (rightly) rejects
  # `line - prev_line` in the combined-guard form because it narrows
  # `prev_line` to `nil` across the first entry call.
  defp collect_doc_comments(state, acc, nil) do
    case peek(state) do
      %Token{type: :doc_comment, value: text, line: line} ->
        state = advance(state)
        state = skip_newlines(state)
        collect_doc_comments(state, [text | acc], line)

      _ ->
        doc = acc |> Enum.reverse() |> Enum.join("\n")
        {doc, state}
    end
  end

  defp collect_doc_comments(state, acc, prev_line) when is_integer(prev_line) do
    case peek(state) do
      %Token{type: :doc_comment, value: text, line: line}
      when line - prev_line <= 1 ->
        state = advance(state)
        state = skip_newlines(state)
        collect_doc_comments(state, [text | acc], line)

      _ ->
        doc = acc |> Enum.reverse() |> Enum.join("\n")
        {doc, state}
    end
  end

  # Collect every consecutive `:doc_comment` block, merging blocks
  # separated by blank-line gaps (or by plain `#` comments, which the
  # lexer drops when `preserve_comments: false`) with a paragraph
  # break. Used by `parse_program/2` and `parse_block_body/2` where any
  # leftover doc-comment tokens ahead of the next statement must bind
  # to that statement -- otherwise the parser would try to recurse
  # into `parse_expr/2` on a `:doc_comment` prefix and raise an
  # "unexpected doc_comment" error.
  defp collect_all_doc_comments(state) do
    {first, state} = collect_doc_comments(state)
    collect_all_doc_comments(state, first)
  end

  defp collect_all_doc_comments(state, acc) do
    state_after_ws = skip_newlines(state)

    case peek(state_after_ws) do
      %Token{type: :doc_comment} ->
        {next, state_after_ws} = collect_doc_comments(state_after_ws)

        merged =
          case {acc, next} do
            {"", n} -> n
            {a, ""} -> a
            {a, n} -> a <> "\n\n" <> n
          end

        collect_all_doc_comments(state_after_ws, merged)

      _ ->
        {acc, state}
    end
  end

  defp attach_doc({type, meta, children}, doc) when is_list(meta) do
    {type, Keyword.put(meta, :doc, doc), children}
  end

  defp attach_doc(ast, _doc), do: ast

  # -- Line Comment Helper ----------------------------------------------------

  # Consume a `:line_comment` token and return an AST node.
  # Emits `{:comment, [line: n, col: c], text}` so downstream consumers
  # (the algebra formatter, documentation tools) can reproduce the
  # comment in source order. Plain `#` comments preserved this way are
  # never attached as `:doc` metadata; they remain free-standing nodes.
  defp consume_line_comment(state) do
    token = peek(state)
    meta = [line: token.line, col: token.col]
    node = {:comment, meta, token.value}
    {node, advance(state)}
  end
end
