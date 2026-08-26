defmodule Cure.Compiler.MacroFuzz do
  @moduledoc """
  Antigen-backed typed filler generation for macro proof inputs.

  This first slice deliberately uses Antigen's certified v1 signature menu. A
  grammar category outside that menu is a reported coverage gap, not a guessed
  inhabitant of a different type.
  """

  alias Antigen.{Challenge, Gen, Shrink}
  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.{SigMenu, Term}
  alias Cure.Compiler.{Lexer, LiftModule, Parser, Token}
  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Normalise}
  alias Cure.Elab.{Elaborator, MacroExpand, Program}
  alias Cure.MetaAST.Metadata

  @default_draws 32
  @cache_key :cure_macro_fuzz_cache_state

  @type generator_info :: %{
          category: String.t(),
          env: Cure.Core.Env.t(),
          ctx: Context.t(),
          goal: Cure.Core.Term.t() | nil,
          domain: atom(),
          generator: Antigen.Gen.t()
        }

  @category_goals %{
    "Nat" => {:data, :Nat, [], []},
    "Bd" => {:data, :Bd, [], []},
    "Vec" => {:data, :Vec, [], [{:ctor, :Z, []}]}
  }

  @spec hole_generator(String.t()) ::
          {:ok, generator_info()} | {:error, {:unsupported_hole_type, String.t()}}
  def hole_generator(category) when is_binary(category), do: hole_generator(category, SigMenu.env_of(:v1))

  @doc "Resolve a grammar category against a real module environment."
  @spec hole_generator(String.t(), Cure.Core.Env.t()) ::
          {:ok, generator_info()} | {:error, {:unsupported_hole_type, String.t()}}
  def hole_generator(category, env) when is_binary(category) do
    case Map.fetch(@category_goals, category) do
      {:ok, goal} ->
        generation_env = SigMenu.env_of(:v1)
        ctx = Context.empty(generation_env)
        {:ok, %{category: category, domain: :core, env: env, ctx: ctx, goal: goal, generator: Term.gen_term(ctx, goal)}}

      :error ->
        case native_hole_generator(category, env) do
          {:error, _} -> module_hole_generator(category, env)
          result -> result
        end
    end
  end

  defp native_hole_generator(category, _env) do
    generation_env = SigMenu.env_of(:v1)
    ctx = Context.empty(generation_env)

    case category do
      "Number" ->
        {:ok,
         %{
           category: category,
           domain: :number,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:int_lit, 0}, {:int_lit, 42}, {:float_lit, 0.5}])
         }}

      "Duration" ->
        {:ok,
         %{
           category: category,
           domain: :duration,
           env: generation_env,
           ctx: ctx,
           goal: {:int_type},
           generator: Gen.member_of([{:int_lit, 1}, {:int_lit, 500}, {:int_lit, 1_000_000}])
         }}

      "Code" ->
        {:ok,
         %{
           category: category,
           domain: :code,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator:
             Gen.frequency([
               {2, Gen.member_of([{:int_lit, 0}, {:int_lit, 9}])},
               {2, Term.gen_term(ctx, SigMenu.nat())}
             ])
         }}

      "Expression" ->
        {:ok,
         %{
           category: category,
           domain: :expression,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator:
             Gen.member_of([
               {:raw_text, "0"},
               {:raw_text, "1 + 2 * 3"},
               {:raw_text, "Some(7)"},
               {:raw_text, "%[:identity, 9]"}
             ])
         }}

      "Identifier" ->
        {:ok,
         %{
           category: category,
           domain: :identifier,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:ctor, :Example, []}, {:ctor, :Worker, []}])
         }}

      "Atom" ->
        {:ok,
         %{
           category: category,
           domain: :atom,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:raw_text, ":example"}, {:raw_text, ":worker"}])
         }}

      "ModuleName" ->
        {:ok,
         %{
           category: category,
           domain: :module_name,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator:
             Gen.member_of([
               {:raw_text, "Cure.Example"},
               {:raw_text, "Cure.Worker"}
             ])
         }}

      "Kind" ->
        {:ok,
         %{
           category: category,
           domain: :core,
           env: generation_env,
           ctx: ctx,
           goal: {:type, 0},
           generator: Term.gen_term(ctx, {:type, 0})
         }}

      "Type" ->
        {:ok,
         %{
           category: category,
           domain: :type,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:raw_text, "Int"}, {:raw_text, "Bool"}, {:raw_text, "Atom"}])
         }}

      "raw until " <> _delimiter ->
        {:ok,
         %{
           category: category,
           domain: :raw,
           env: generation_env,
           ctx: ctx,
           goal: nil,
           generator: Gen.member_of([{:raw_text, "0"}, {:raw_text, "item"}, {:raw_text, "item 1"}])
         }}

      _ ->
        {:error, {:unsupported_hole_type, category}}
    end
  end

  defp module_hole_generator(category, env) do
    family_name = String.to_atom(category)

    with true <- Inductive.family?(env, family_name),
         family = Inductive.get_family(env, family_name),
         ctors = Inductive.ctors_of(env, family_name),
         nullary = Enum.filter(ctors, &(Map.get(&1, :args, []) == [])),
         true <- nullary != [] do
      ctx = Context.empty(env)

      case canonical_parameters(ctx, family.params) do
        {:ok, params} ->
          # A single indexed constructor gives the generator one stable goal.
          # Families with several incompatible indexed result spines are kept
          # as explicit coverage gaps until a dependent sum generator can carry
          # each constructor's goal alongside its term.
          case nullary do
            [ctor | _] ->
              result_params = instantiate_result_terms(ctor.result_params, params, 0)
              result_indices = instantiate_result_terms(ctor.result_indices, params, 0)
              goal = {:data, family.name, result_params, result_indices}

              {:ok,
               %{
                 category: category,
                 domain: :core,
                 env: env,
                 ctx: ctx,
                 goal: goal,
                 generator: Gen.return({:ctor, ctor.name, []})
               }}

            _ ->
              {:error, {:unsupported_hole_type, category}}
          end

        :error ->
          {:error, {:unsupported_hole_type, category}}
      end
    else
      _ -> {:error, {:unsupported_hole_type, category}}
    end
  end

  defp canonical_parameters(_ctx, []), do: {:ok, []}

  defp canonical_parameters(ctx, params) do
    params
    |> Enum.reduce_while({:ok, []}, fn {_name, type}, {:ok, values} ->
      case canonical_parameter(ctx, type) do
        {:ok, value} -> {:cont, {:ok, values ++ [value]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp canonical_parameter(%Context{} = ctx, {:type, _level}) do
    env = Context.signature(ctx)
    {:ok, {:data, Env.resolve_key(env, env.families, :Nat), [], []}}
  end

  defp canonical_parameter(ctx, type) do
    try do
      {:ok, SigMenu.canon(ctx, type)}
    rescue
      _ -> :error
    end
  end

  defp instantiate_result_terms(terms, params, field_count) do
    Enum.map(terms, &instantiate_result_term(&1, params, field_count))
  end

  defp instantiate_result_term(term, params, field_count) do
    params
    |> Enum.with_index()
    |> Enum.reverse()
    |> Enum.reduce(term, fn {param, index}, acc ->
      target = field_count + length(params) - index - 1
      Cure.Core.Term.subst(acc, target, param)
    end)
  end

  @spec sample_holes(String.t(), non_neg_integer(), integer()) ::
          {:ok, generator_info(), [Cure.Core.Term.t()]}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, {:generated_hole_not_well_typed, term()}}
  def sample_holes(category, count, seed)
      when is_binary(category) and is_integer(count) and count >= 0 and is_integer(seed) do
    sample_holes(category, count, seed, SigMenu.env_of(:v1))
  end

  @spec sample_holes(String.t(), non_neg_integer(), integer(), Cure.Core.Env.t()) ::
          {:ok, generator_info(), [Cure.Core.Term.t()]}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, {:generated_hole_not_well_typed, term()}}
  def sample_holes(category, count, seed, env)
      when is_binary(category) and is_integer(count) and count >= 0 and is_integer(seed) do
    with {:ok, info} <- hole_generator(category, env),
         terms = Backend.sample_seeded(info.generator, count, seed),
         :ok <- check_samples(info, terms) do
      {:ok, info, terms}
    end
  end

  @doc "Proof-check supported syntax rules against generated use-sites."
  @spec check_expansion_proof(tuple(), Cure.Core.Env.t(), keyword()) ::
          :ok
          | {:error, {:expansion_ill_typed, map()}}
          | {:error, {:unsupported_hole_type, String.t()}}
          | {:error, term()}
  def check_expansion_proof(macro_def, env, opts \\ []) do
    {result, _manifest, _cached?} = cached_proof(macro_def, env, opts)
    result
  end

  @doc "Return the proof manifest and whether this lookup reused cached work."
  @spec proof_manifest(tuple(), Cure.Core.Env.t(), keyword()) ::
          {:ok, %{cached?: boolean(), rules: [map()]}}
          | {:error, term(), %{cached?: boolean(), rules: [map()]}}
  def proof_manifest(macro_def, env, opts \\ []) do
    {result, manifest, cached?} = cached_proof(macro_def, env, opts)
    report = %{cached?: cached?, rules: manifest}

    case result do
      :ok -> {:ok, report}
      {:error, _} = error -> {:error, error, report}
    end
  end

  @doc "Report every typed hole domain and open category used by a macro."
  @spec category_coverage(tuple(), Cure.Core.Env.t()) :: {:ok, map()}
  def category_coverage({:macro_def, _meta, rules}, env) do
    open_categories =
      rules
      |> Enum.filter(&(&1[:kind] == :open_category))
      |> Enum.map(& &1.name)
      |> Enum.uniq()

    categories =
      rules
      |> Enum.filter(&(&1[:kind] in [:syntax, :computed]))
      |> Enum.flat_map(fn rule ->
        Enum.map(segment_holes(rule.segments), &{&1.kind, rule.keyword})
      end)
      |> Enum.uniq()
      |> Enum.map(fn {category, keyword} ->
        status =
          case hole_generator(category, env) do
            {:ok, info} -> %{status: :supported, domain: info.domain}
            {:error, {:unsupported_hole_type, ^category}} -> %{status: :unsupported, domain: nil}
          end

        Map.merge(%{category: category, keyword: keyword, open: category in open_categories}, status)
      end)

    unsupported = Enum.filter(categories, &(&1.status == :unsupported))

    {:ok,
     %{
       categories: categories,
       open_categories: open_categories,
       unsupported: unsupported,
       complete?: unsupported == []
     }}
  end

  defp cached_proof({:macro_def, _meta, rules} = macro_def, env, opts) do
    key = proof_cache_key(macro_def, env, opts)
    cache = :persistent_term.get(@cache_key, %{})

    case Map.fetch(cache, key) do
      {:ok, {result, manifest}} ->
        {result, manifest, true}

      :error ->
        result = run_expansion_proof(rules, env, opts)
        status = if result == :ok, do: :passed, else: :failed

        manifest =
          for rule <- Enum.filter(rules, &(&1[:kind] in [:syntax, :computed])) do
            %{
              keyword: rule.keyword,
              hole_kinds: rule.segments |> segment_holes() |> Enum.map(& &1.kind),
              draws: Keyword.get(opts, :draws, @default_draws),
              status: if(contextual_proof?(rule), do: :deferred, else: status)
            }
          end

        :persistent_term.put(@cache_key, Map.put(cache, key, {result, manifest}))
        {result, manifest, false}
    end
  end

  @doc false
  def proof_cache_key(macro_def, env, opts \\ []) do
    :erlang.phash2(
      {Metadata.semantic_key(macro_def), env, Keyword.get(opts, :draws, @default_draws), Keyword.get(opts, :seed, 1)}
    )
  end

  defp run_expansion_proof(rules, env, opts) do
    draws = Keyword.get(opts, :draws, @default_draws)
    seed = Keyword.get(opts, :seed, 1)

    rules
    |> Enum.filter(&(&1[:kind] in [:syntax, :computed] and not contextual_proof?(&1)))
    |> Enum.reduce_while(:ok, fn rule, :ok ->
      case prove_rule(rule, rules, env, draws, seed) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  # A capture obligation is resolved from the caller's inferred expression
  # type, so a definition-site generator cannot prove it in isolation.
  defp contextual_proof?(rule),
    do: rule[:contextual] or Map.get(rule, :obligations, []) != []

  defp prove_rule(rule, rules, env, draws, seed) do
    holes = segment_holes(rule.segments)

    case holes do
      [] ->
        with {:ok, input} <- assemble_use_site(rule, %{}),
             {:ok, expansion} <- expand_generated(rule, rules, input, env) do
          check_expansion(rule.keyword, input, expansion, env)
        end

      _ ->
        with {:ok, bindings} <- sample_bindings(holes, draws, seed, env) do
          Enum.reduce_while(bindings, :ok, fn binding, :ok ->
            case assemble_use_site(rule, binding) do
              {:ok, input} ->
                case expand_generated(rule, rules, input, env) do
                  {:ok, expansion} ->
                    case check_expansion(rule.keyword, input, expansion, env) do
                      :ok ->
                        {:cont, :ok}

                      {:error, {:expansion_ill_typed, details}} ->
                        shrunk = shrink_counterexample(rule, rules, env, binding, details)
                        {:halt, {:error, {:expansion_ill_typed, shrunk}}}
                    end

                  {:error, reason} ->
                    {:halt,
                     {:error, {:expansion_ill_typed, %{keyword: rule.keyword, input: input, kernel_error: reason}}}}
                end

              {:error, _} = error ->
                {:halt, error}
            end
          end)
        end
    end
  end

  defp sample_bindings(holes, draws, seed, env) do
    initial = List.duplicate(%{}, draws)

    Enum.reduce_while(holes, {:ok, initial}, fn %{name: name, kind: kind, repeat: repeat}, {:ok, bindings} ->
      case sample_holes(kind, draws, seed, env) do
        {:ok, _info, terms} ->
          next =
            bindings
            |> Enum.with_index()
            |> Enum.map(fn {binding, index} ->
              value = if repeat, do: [Enum.at(terms, index)], else: Enum.at(terms, index)
              Map.put(binding, name, value)
            end)

          {:cont, {:ok, next}}

        {:error, {:generated_hole_not_well_typed, term}} ->
          {:halt,
           {:error,
            {:generated_hole_not_well_typed, %{term: term, category: kind, hole: name, generator_invariant: true}}}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
  end

  defp expand_generated(%{kind: :syntax}, rules, input, _env),
    do: {:ok, Parser.expand_example(rules, input)}

  defp expand_generated(%{kind: :computed}, rules, input, env) do
    rules
    |> Parser.expand_example(input)
    |> MacroExpand.expand(env)
  end

  defp check_expansion(keyword, input, expansion, env) do
    case expansion do
      {:block, _meta, items} when is_list(items) ->
        check_block_expansion(keyword, input, expansion, env)

      {:lift_module, _meta, []} ->
        case LiftModule.request_ast(expansion) do
          {:ok, _quoted_module} ->
            :ok

          {:error, reason} ->
            {:error,
             {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
        end

      # A `becomes` template is ONE expression form, so a rule that generates a
      # definition expands to a bare declaration node rather than to a block of
      # them. Routing that to the expression checker rejected it as
      # `{:unsupported_expression, {:function_def, …}}` at the DEFINITION site,
      # before any use-site existed — every single-declaration macro was
      # unwritable. The declaration itself is still proved, through the same
      # proof-module path a multi-declaration block takes.
      _ ->
        if Program.declaration?(expansion),
          do: check_block_expansion(keyword, input, expansion, env),
          else: check_expression_expansion(keyword, input, expansion, env)
    end
  end

  # A declaration macro may return a type declaration alongside a lifted
  # module. Check the enclosing declarations and the lifted unit through their
  # ordinary generic paths so the proof exercises the same two scopes as the
  # real declaration pass.
  defp check_block_expansion(keyword, input, expansion, _env) do
    declarations = expansion |> LiftModule.strip() |> block_items()

    proof_module =
      {:container, [container_type: :module, name: "MacroExpansionProof", language: :cure], declarations}

    with {:ok, _env} <- Program.check_ast(proof_module),
         {:ok, requests} <- LiftModule.collect(expansion),
         :ok <- emit_proof_lifted_requests(requests) do
      :ok
    else
      {:error, reason} ->
        if use_site_resolved_reference?(reason) do
          :ok
        else
          {:error,
           {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
        end
    end
  end

  # Is the sole obstruction a QUALIFIED name the definition site cannot be
  # expected to resolve?
  #
  # A template may name another module — that is much of the point of a macro.
  # The defining module need not import it: the reference does not exist until
  # the rule expands, and it lands in the EXPANDING module, where the canonical
  # pipeline discovers it as a `:macro_generated_reference` edge and extends the
  # dependency graph until it closes. Failing the definition-site proof on it
  # made any template that names another module unwritable, and the error named
  # a module the author had no reason to import.
  #
  # The deferral is deliberately narrow — it is keyed on the name being
  # qualified. A BARE unresolved name is still a definition-site failure, and
  # must stay one: an unbound bare name is exactly how a hygiene defect in a
  # generated binder shows up, which is the class of bug this gate exists to
  # catch. Deferring does not skip the check either; the expansion is checked
  # again in the expanding module, where an unimportable module or a misspelt
  # remote call is reported against the code that actually caused it.
  defp use_site_resolved_reference?({:source_context, reason, _context}),
    do: use_site_resolved_reference?(reason)

  defp use_site_resolved_reference?({:unknown_global, name, _details}) when is_atom(name),
    do: qualified_name?(name)

  defp use_site_resolved_reference?({:unknown_global, name}) when is_atom(name),
    do: qualified_name?(name)

  defp use_site_resolved_reference?(_reason), do: false

  defp qualified_name?(name), do: name |> Atom.to_string() |> String.contains?(".")

  defp emit_proof_lifted_requests(requests) do
    Enum.reduce_while(requests, :ok, fn request, :ok ->
      case LiftModule.emit(request) do
        {:ok, _unit} -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
  end

  defp block_items({:block, _meta, items}) when is_list(items), do: items
  defp block_items(item), do: [item]

  defp check_expression_expansion(keyword, input, expansion, env) do
    case Elaborator.elaborate_expr_typed(expansion, [], Context.empty(env), env) do
      {:ok, _term, _type} ->
        :ok

      {:error, {:unsolved_metavariables, name} = reason} ->
        if parametric_erased_call?(expansion, env, name) do
          :ok
        else
          {:error,
           {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
        end

      {:error, reason} ->
        {:error, {:expansion_ill_typed, %{keyword: keyword, input: input, expansion: expansion, kernel_error: reason}}}
    end
  end

  # A contextual expression rule may expand to a nullary application of a global
  # whose every parameter is an erased implicit — e.g. `Std.Otp.self()` where
  # `self : {m: Type} -> Effect(Pid(m))`. The erased index `m` cannot be solved
  # use-site-free, so standalone elaboration reports it as an unsolved
  # metavariable. But an erased binder is computationally irrelevant: the
  # expansion is well-typed at a schematic type for every instantiation of the
  # erased parameters, exactly as an ungeneralized polymorphic term is. When the
  # sole obstruction is unsolved metavariables of such an all-erased,
  # no-explicit-argument global call, the expansion is proven well-typed by
  # parametricity — so the generative proof accepts it without a `contextual`
  # exemption. Guards: the expansion must be a bare nullary call (no argument
  # subterms can hide a relevant unsolved metavariable), and the errored callee's
  # every parameter must be erased (no relevant parameter left unsolved).
  @doc false
  @spec parametric_erased_call?(term(), Cure.Core.Env.t(), atom()) :: boolean()
  def parametric_erased_call?({:function_call, _meta, []}, env, name) do
    case Env.get_def(env, name) do
      %{type: type, quantities: quantities} when is_list(quantities) ->
        quantities != [] and Enum.all?(quantities, &(&1 == :erased)) and
          all_erased_pi_spine?(type, length(quantities))

      _ ->
        false
    end
  end

  def parametric_erased_call?(_expansion, _env, _name), do: false

  # The def's type must be a telescope of exactly `count` erased Pi binders whose
  # final codomain is not itself a Pi — i.e. every parameter is erased and no
  # relevant (present-grade) parameter hides in or beyond the spine.
  defp all_erased_pi_spine?(type, 0), do: not match?({:pi, _grade, _dom, _cod}, type)

  defp all_erased_pi_spine?({:pi, :erased, _dom, cod}, count) when count > 0,
    do: all_erased_pi_spine?(cod, count - 1)

  defp all_erased_pi_spine?(_type, _count), do: false

  defp shrink_counterexample(rule, rules, env, bindings, details) do
    {name, term, info} = first_shrinkable_binding(bindings, env)

    if is_nil(info) do
      Map.put(details, :generated_bindings, bindings)
    else
      shrink_counterexample(rule, rules, env, bindings, details, name, term, info)
    end
  end

  defp shrink_counterexample(rule, rules, env, bindings, details, name, term, info) do
    challenge =
      Challenge.new(
        kind: :typed_term,
        assay: "macro/expansion",
        label: :well_typed,
        seed: 0,
        payload: %{sig: :v1, ctx: [], type: info.goal, term: term}
      )

    pred = fn candidate ->
      candidate_term = candidate.payload.term

      with {:ok, input} <- assemble_use_site(rule, Map.put(bindings, name, candidate_term)),
           {:ok, expansion} <- expand_generated(rule, rules, input, env),
           {:error, {:expansion_ill_typed, _}} <- check_expansion(rule.keyword, input, expansion, env) do
        true
      else
        _ -> false
      end
    end

    shrunk = Shrink.minimize(challenge, pred, 128)

    result =
      Map.merge(details, %{
        generated_bindings: bindings,
        generated_term: term,
        shrunk_term: shrunk.payload.term
      })

    if map_size(bindings) == 1, do: result, else: Map.put(result, :shrunk_hole, name)
  end

  defp first_shrinkable_binding(bindings, env) do
    Enum.find_value(bindings, fn {name, term} ->
      case term do
        {:ctor, _, _} ->
          {:ok, info} = hole_generator_for_term(term, env)

          case info do
            %{goal: goal} when not is_nil(goal) -> {name, term, info}
            _ -> nil
          end

        _ ->
          nil
      end
    end) || {nil, nil, nil}
  end

  defp hole_generator_for_term({:ctor, :Z, []}, env), do: hole_generator("Nat", env)
  defp hole_generator_for_term({:ctor, :S, _}, env), do: hole_generator("Nat", env)
  defp hole_generator_for_term({:ctor, name, []}, env) when name in [:T, :F], do: hole_generator("Bd", env)
  defp hole_generator_for_term(_term, _env), do: {:ok, %{goal: nil}}

  @doc "Assemble a rule's keyword, literals, and named hole fillers into tokens."
  @spec assemble_use_site(map(), %{String.t() => Cure.Core.Term.t()}) ::
          {:ok, [Token.t()]} | {:error, {:unsupported_surface_filler, term()}} | {:error, term()}
  def assemble_use_site(%{keyword: keyword, segments: segments}, bindings)
      when is_binary(keyword) and is_list(segments) and is_map(bindings) do
    with {:ok, words} <- assemble_words(segments, bindings) do
      line = Enum.join([keyword | words], " ")

      if declarations_hole?(segments) do
        # A `Declarations until dedent` body must occupy its own indented
        # line so `parse_definition_block` sees an `:indent`. Synthesise a
        # minimal well-typed body block and let the lexer emit the structural
        # indent/dedent tokens rather than hand-building them.
        case Lexer.tokenize(line <> "\n  fn __proof_body() -> Int = 1\n", emit_events: false) do
          {:ok, tokens} -> {:ok, Enum.reject(tokens, &(&1.type == :eof))}
          {:error, _} = error -> error
        end
      else
        case Lexer.tokenize(line, emit_events: false) do
          {:ok, tokens} ->
            tokens = Enum.reject(tokens, &(&1.type == :eof))
            {:ok, append_raw_delimiters(tokens, segments)}

          {:error, _} = error ->
            error
        end
      end
    end
  end

  def assemble_use_site(%{keyword: keyword, segments: segments}, _bindings)
      when is_binary(keyword) and is_list(segments),
      do: {:error, :invalid_macro_fuzz_bindings}

  def assemble_use_site(_rule, _bindings), do: {:error, :invalid_macro_fuzz_rule}

  defp declarations_hole?(segments) when is_list(segments) do
    Enum.any?(segments, fn
      {:declarations_hole, _meta} -> true
      {:optional, group} -> declarations_hole?(group)
      _ -> false
    end)
  end

  defp append_raw_delimiters(tokens, segments) do
    if Enum.any?(segments, &match?({:raw_hole, %{delimiter: "dedent"}}, &1)),
      do: tokens ++ [Token.new(:dedent, nil, 1, 1)],
      else: tokens
  end

  defp assemble_words(segments, bindings) when is_list(segments) and is_map(bindings) do
    Enum.reduce_while(segments, {:ok, []}, fn
      {:lit, word}, {:ok, acc} ->
        {:cont, {:ok, acc ++ [word]}}

      {:hole, %{name: name}}, {:ok, acc} ->
        case Map.fetch(bindings, name) do
          {:ok, term} ->
            case surface_filler(term) do
              {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
              {:error, _} = error -> {:halt, error}
            end

          :error ->
            {:halt, {:error, {:missing_hole_filler, name}}}
        end

      {:raw_hole, %{name: name}}, {:ok, acc} ->
        case Map.fetch(bindings, name) do
          {:ok, term} ->
            case surface_filler(term) do
              {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
              {:error, _} = error -> {:halt, error}
            end

          :error ->
            {:halt, {:error, {:missing_hole_filler, name}}}
        end

      {:repeat, {:hole, %{name: name}}}, {:ok, acc} ->
        case Map.fetch(bindings, name) do
          {:ok, values} when is_list(values) ->
            case Enum.reduce_while(values, {:ok, []}, fn value, {:ok, words} ->
                   case surface_filler(value) do
                     {:ok, text} -> {:cont, {:ok, words ++ [text]}}
                     {:error, _} = error -> {:halt, error}
                   end
                 end) do
              {:ok, words} -> {:cont, {:ok, acc ++ words}}
              {:error, _} = error -> {:halt, error}
            end

          :error ->
            {:halt, {:error, {:missing_hole_filler, name}}}

          {:ok, _other} ->
            {:halt, {:error, {:invalid_repeated_hole_filler, name}}}
        end

      {:optional, group}, {:ok, acc} ->
        case assemble_words(group, bindings) do
          {:ok, words} -> {:cont, {:ok, acc ++ words}}
          {:error, _} = error -> {:halt, error}
        end

      {:declarations_hole, _meta}, {:ok, acc} ->
        # The body block is appended to the assembled source as its own
        # indented line by `assemble_use_site`; it contributes no inline word.
        {:cont, {:ok, acc}}

      other, {:ok, _acc} ->
        {:halt, {:error, {:invalid_macro_segment, other}}}
    end)
  end

  defp assemble_words(segments, _bindings), do: {:error, {:invalid_macro_segment, segments}}

  defp surface_filler(term) do
    case surface_filler_normal(term) do
      {:error, _} = error ->
        normalized = Normalise.nf(Context.empty(SigMenu.env_of(:v1)), term)

        if normalized == term or normalized == :fuel_exhausted do
          error
        else
          surface_filler_normal(normalized)
        end

      result ->
        result
    end
  end

  defp surface_filler_normal({:ctor, :Z, []}), do: {:ok, "0"}

  defp surface_filler_normal({:ctor, :S, [inner]}) do
    with {:ok, n} <- surface_nat(inner), do: {:ok, Integer.to_string(n + 1)}
  end

  defp surface_filler_normal({:ctor, :T, []}), do: {:ok, "true"}
  defp surface_filler_normal({:ctor, :F, []}), do: {:ok, "false"}
  defp surface_filler_normal({:data, :Nat, [], []}), do: {:ok, "Nat"}
  defp surface_filler_normal({:data, :Bd, [], []}), do: {:ok, "Bd"}
  defp surface_filler_normal({:raw_text, text}) when is_binary(text), do: {:ok, text}
  defp surface_filler_normal({:int_lit, n}) when is_integer(n), do: {:ok, Integer.to_string(n)}
  defp surface_filler_normal({:float_lit, n}) when is_float(n), do: {:ok, Float.to_string(n)}

  defp surface_filler_normal({:ctor, name, []}) when is_atom(name), do: {:ok, Atom.to_string(name)}
  defp surface_filler_normal(other), do: {:error, {:unsupported_surface_filler, other}}

  defp surface_nat({:ctor, :Z, []}), do: {:ok, 0}

  defp surface_nat({:ctor, :S, [inner]}) do
    with {:ok, n} <- surface_nat(inner), do: {:ok, n + 1}
  end

  defp surface_nat(_other), do: {:error, :not_a_nat}

  defp check_samples(%{ctx: ctx, goal: goal, domain: :core}, terms) do
    goal_value = Eval.eval(goal, Context.env(ctx))

    case Enum.find(terms, &(Kernel.check(ctx, &1, goal_value) != :ok)) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: domain}, terms) when domain in [:number, :duration] do
    case Enum.find(terms, fn
           {:int_lit, _} -> false
           {:float_lit, _} -> domain != :number
           _ -> true
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{ctx: ctx, domain: :code}, terms) do
    case Enum.find(terms, fn term ->
           not (match?({:ok, _}, Kernel.infer(ctx, term)) and match?({:ok, _}, surface_filler(term)))
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :raw}, terms) do
    case Enum.find(terms, &(not match?({:raw_text, text} when is_binary(text), &1))) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :expression}, terms) do
    case Enum.find(terms, fn
           {:raw_text, text} ->
             case Lexer.tokenize(text, emit_events: false) do
               {:ok, tokens} -> match?({:ok, _}, Parser.parse(tokens, emit_events: false)) == false
               {:error, _} -> true
             end

           _ ->
             true
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :identifier}, terms) do
    case Enum.find(terms, &(not match?({:ctor, name, []} when is_atom(name), &1))) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :atom}, terms) do
    case Enum.find(terms, fn
           {:raw_text, text} -> not Regex.match?(~r/^:[a-z][A-Za-z0-9_@!?]*$/, text)
           _ -> true
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :module_name}, terms) do
    case Enum.find(terms, fn
           {:raw_text, name} -> not Regex.match?(~r/^Cure\.[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*$/, name)
           _ -> true
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp check_samples(%{domain: :type}, terms) do
    case Enum.find(terms, fn
           {:raw_text, text} -> not Regex.match?(~r/^[A-Z][A-Za-z0-9_.]*(?:\([^\n]*\))?$/, text)
           _ -> true
         end) do
      nil -> :ok
      bad -> {:error, {:generated_hole_not_well_typed, bad}}
    end
  end

  defp segment_holes(segments) when is_list(segments), do: Enum.flat_map(segments, &segment_holes/1)

  defp segment_holes({:hole, %{name: name, kind: kind}}),
    do: [%{name: name, kind: kind, repeat: false}]

  defp segment_holes({:raw_hole, %{name: name, delimiter: delimiter}}),
    do: [%{name: name, kind: "raw until " <> delimiter, repeat: false}]

  defp segment_holes({:repeat, {:hole, %{name: name, kind: kind}}}),
    do: [%{name: name, kind: kind, repeat: true}]

  defp segment_holes({:optional, segments}), do: segment_holes(segments)
  defp segment_holes(_segment), do: []
end
