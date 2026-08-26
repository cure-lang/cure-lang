defmodule Cure.Migrate do
  @moduledoc """
  The migration facility's rule engine (spec §4). Holds the ordered registry of
  migration rules and runs them over a whole-file AST as a fold, threading each
  rule's rewrite into the next and collecting one warning per rewrite.

  Two consumers share this one engine:

    * `cure build` reports the warnings but keeps the original source.
    * `cure migrate` applies the rewrites and reprints the file.

  See `Cure.Migrate.Rule` for the shape of a single rule.
  """

  alias Cure.Compiler.MacroFamily
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityScan}
  alias Cure.Migrate.Rule

  defmodule Warning do
    @moduledoc """
    A migration warning emitted when a rule rewrites (or, in `cure build`,
    *would* rewrite) a file. `:rule` is the rule's stable id atom; `:file` and
    `:span` locates it precisely for the user (`:line` remains for compatibility
    with callers that consume migration warnings as data).
    """
    @enforce_keys [:rule, :message, :file]
    defstruct [:rule, :message, :file, :line, :span, :tier, :preview]

    @type t :: %__MODULE__{
            rule: atom(),
            message: String.t(),
            file: String.t(),
            line: pos_integer() | nil,
            span: Cure.Diagnostic.Span.t() | nil,
            tier: Rule.tier(),
            preview: String.t() | nil
          }
  end

  @doc """
  The built-in rule registry, in declaration (application) order. Seeded by the
  day-one rules (Tasks 8/9/9b); empty until then. `run/2` uses this unless the
  caller passes an explicit `:rules` list (tests do).
  """
  @spec rules() :: [Rule.t()]
  def rules,
    do: [
      Cure.Migrate.Rules.IfElifToPickup.rule(),
      Cure.Migrate.Rules.UppercaseTypeVar.rule(),
      Cure.Migrate.Rules.GroupHoist.rule(),
      Cure.Migrate.Rules.ModuleRename.rule(),
      Cure.Migrate.Rules.RemovedModule.rule(),
      Cure.Migrate.Rules.ProtoToInterface.rule()
    ]

  @doc "Rules to apply when crossing to `target` (spec §7.2)."
  @spec rules_for_crossing(Cure.Edition.t(), [Rule.t()]) :: [Rule.t()]
  def rules_for_crossing(target, rules \\ rules()) do
    Enum.filter(rules, fn r ->
      mandatory = r.enforced_in != nil and Cure.Edition.compare(r.enforced_in, target) in [:lt, :eq]
      proactive = r.tier in [:machine, :review] and Cure.Edition.compare(r.since, target) in [:lt, :eq]
      mandatory or proactive
    end)
  end

  @doc "The :manual rules whose old form is illegal at `target` (block the bump)."
  @spec blocking_manual(Cure.Edition.t(), [Rule.t()]) :: [Rule.t()]
  def blocking_manual(target, rules \\ rules()) do
    Enum.filter(rules, fn r ->
      r.tier == :manual and r.enforced_in != nil and
        Cure.Edition.compare(r.enforced_in, target) in [:lt, :eq]
    end)
  end

  @doc """
  Run `rules` over `ast` as an ordered fold. Each rule sees the AST as left by
  the previous rule; a `{:rewrite, new_ast}` result is threaded forward and
  records one `Warning`, a `:no_change` result is transparent. Returns
  `{final_ast, warnings}` with warnings in rule-application order.

  Options:

    * `:file` — the source path, recorded on each warning (default `"nofile"`).
    * `:rules` — override the registry (default `rules/0`).
    * `:apply` — which rewrites to fold into the returned AST:
        * `:all` (default) — every rule's rewrite; used by `cure migrate`.
        * `:safe_only` — only the rewrites of `:machine`-tier rules; used by
          `cure build`, so a `:review`/`:manual` rule *warns* but leaves the
          legacy form as-is in the compiled AST (spec's "normalize in-memory
          where safe"). Warnings are emitted for every fired rule in both modes.
  """
  @spec run(Rule.ast(), keyword()) :: {Rule.ast(), [Warning.t()]}
  def run(ast, opts \\ []) do
    {new_ast, warns, _rewriters} = fold_rules(ast, opts)
    {new_ast, warns}
  end

  # Shared fold behind `run/2` and `run_to_fixpoint/2`. Threads the AST through
  # the rule set as `run/2` documents, and additionally reports `rewriters` — the
  # ordered ids of rules whose committed rewrite actually changed the AST this
  # pass. `run_to_fixpoint/2` needs that: a pass whose rewrites net to identity
  # (e.g. a non-monotone `x->y`/`y->x` pair) leaves the AST equal yet is still
  # actively rewriting, so AST-equality alone cannot tell "done" from "thrashing"
  # — while a pure `:warn` rule must NOT count as a rewrite (it never converges
  # away, so counting it would loop forever). The list (not just a boolean) also
  # lets a verify failure be attributed to a *rewriter* rather than a warner.
  @spec fold_rules(Rule.ast(), keyword()) :: {Rule.ast(), [Warning.t()], [atom()]}
  defp fold_rules(ast, opts) do
    file = Keyword.get(opts, :file, "nofile")
    rule_set = Keyword.get(opts, :rules, rules())
    apply_mode = Keyword.get(opts, :apply, :all)
    ctx = build_ctx(ast, file)

    {ast, warns, rev_rewriters} =
      Enum.reduce(rule_set, {ast, [], []}, fn %Rule{} = rule, {acc_ast, warns, rewriters} ->
        case rule.detect_and_rewrite.(acc_ast, ctx) do
          {:rewrite, new_ast} ->
            committed = commit(rule, apply_mode, acc_ast, new_ast)

            {committed, warns ++ warnings_for(rule, file, [nil], new_ast),
             maybe_rewriter(rewriters, rule, committed, acc_ast)}

          {:rewrite, new_ast, locations} ->
            committed = commit(rule, apply_mode, acc_ast, new_ast)

            {committed, warns ++ warnings_for(rule, file, locations, new_ast),
             maybe_rewriter(rewriters, rule, committed, acc_ast)}

          {:warn, locations} ->
            {acc_ast, warns ++ warnings_for(rule, file, locations, nil), rewriters}

          :no_change ->
            {acc_ast, warns, rewriters}
        end
      end)

    {ast, warns, Enum.reverse(rev_rewriters)}
  end

  # Prepend the rule's id to the (reversed) rewriter list iff its commit actually
  # changed the AST — a `:safe_only`-suppressed rewrite is not a rewriter.
  defp maybe_rewriter(rewriters, %Rule{id: id}, committed, old_ast) do
    if committed != old_ast, do: [id | rewriters], else: rewriters
  end

  # Fold the rewrite (`:all` mode, or a `:machine`-tier rule) or keep the legacy
  # AST while still having warned (`:safe_only` mode, `:review`/`:manual` rule).
  defp commit(_rule, :all, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{tier: :machine}, :safe_only, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{}, :safe_only, old_ast, _new_ast), do: old_ast

  defp warnings_for(%Rule{} = rule, file, locations, preview_ast) do
    preview = if preview_ast, do: preview_source(preview_ast)
    message = tier_message(rule)

    Enum.map(locations, fn
      %Cure.Diagnostic.Span{} = span ->
        %Warning{
          rule: rule.id,
          message: message,
          file: file,
          line: span.start_line,
          span: span,
          tier: rule.tier,
          preview: preview
        }

      line ->
        %Warning{
          rule: rule.id,
          message: message,
          file: file,
          line: line,
          tier: rule.tier,
          preview: preview
        }
    end)
  end

  defp preview_source(ast) do
    case safe_print(ast) do
      {:ok, source} -> source
      {:error, _} -> nil
    end
  end

  defp tier_message(%Rule{tier: :machine, warning_template: message}),
    do: message <> ". This migration is semantics-preserving and can be applied automatically."

  defp tier_message(%Rule{tier: :review, warning_template: message}) do
    proposal = message |> String.replace(" will be ", " can be ") |> String.replace(" will ", " can ")
    proposal <> ". Review the proposed result before applying it."
  end

  defp tier_message(%Rule{tier: :manual, warning_template: message}),
    do: message <> ". This migration must be completed by hand."

  @max_passes 8

  @doc """
  Run the registry to a fixpoint (spec §6.1): repeatedly apply `run/2` until a
  full pass changes nothing. After each changing pass, verify the reprinted
  output reparses and preserves every comment; a verify failure aborts. If the
  AST is still changing at `:max_passes`, return `{:error, {:no_convergence,
  culprit_rule_ids}}` (a rule-set bug, not a user error).
  """
  @spec run_to_fixpoint(Rule.ast(), keyword()) ::
          {:ok, Rule.ast(), [Warning.t()]}
          | {:error, {:no_convergence, [atom()]}}
          | {:error, {:verify_failed, atom() | nil}}
  def run_to_fixpoint(ast, opts \\ []) do
    max = Keyword.get(opts, :max_passes, @max_passes)
    # The target edition governs the verify reparse (F12): output valid only under
    # the crossing target must parse under it, not the compiler default.
    edition = Keyword.get(opts, :edition) || Cure.Edition.current()

    case safe_print(ast) do
      {:ok, src} -> do_fixpoint(ast, opts, max, [], comment_texts(src), edition)
      # An input the Printer can't render can't be migrated cleanly — report it as
      # a verify failure (no culprit rule) rather than crashing the caller.
      {:error, _} -> {:error, {:verify_failed, nil}}
    end
  end

  defp do_fixpoint(ast, opts, passes_left, warns, baseline, edition) do
    {new_ast, pass_warns, rewriters} = fold_rules(ast, opts)

    cond do
      # Fixpoint reached: nothing rewrote the AST this pass. Pure `:warn` rules
      # may still have fired (they warn every pass and never converge away) —
      # that is expected and does NOT block convergence. Deduplicate the
      # accumulated warnings (F2): a rule that fires on N passes must surface its
      # warning once, not once per pass.
      new_ast == ast and rewriters == [] ->
        {:ok, ast, Enum.uniq(warns ++ pass_warns)}

      # Still rewriting at the pass budget → the rule set does not converge
      # (a rule-set bug, not a user error). Report the rules that fired last.
      passes_left <= 1 ->
        {:error, {:no_convergence, pass_warns |> Enum.map(& &1.rule) |> Enum.uniq()}}

      true ->
        case verify(new_ast, baseline, edition) do
          :ok ->
            do_fixpoint(new_ast, opts, passes_left - 1, warns ++ pass_warns, baseline, edition)

          {:error, _reason} ->
            # Attribute to a rule that actually REWROTE this pass (F-culprit): a
            # verify break is caused by a rewrite, never by a pure-warn rule.
            {:error, {:verify_failed, List.last(rewriters)}}
        end
    end
  end

  # Reprint → reparse (fail if the output no longer parses) AND diff comments
  # against `baseline` — the ORIGINAL input's comment texts, captured once by
  # `run_to_fixpoint/2` before the first pass, not the previous pass's output.
  # Checking against the true original (not pass-to-pass) is what makes this
  # catch a comment a rule drops on pass 3 even though passes 1-2 preserved
  # everything — re-basing to each intermediate pass would let that slip
  # through as "no *new* loss this pass". Reparse uses the target `edition` so
  # output valid only under it is not spuriously rejected (F12). The whole body
  # is guarded (F3b): a rule that yields unrenderable/unparseable output must
  # surface a clean {:error, …}, never crash the migration.
  defp verify(ast, baseline_comments, edition) do
    with {:ok, src} <- safe_print(ast),
         {:ok, toks} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false, edition: edition),
         {:ok, _} <- Cure.Compiler.Parser.parse(toks, emit_events: false, edition: edition) do
      if baseline_comments -- comment_texts(src) == [] do
        :ok
      else
        {:error, :comment_dropped}
      end
    else
      _ -> {:error, :reparse}
    end
  rescue
    _ -> {:error, :verify_crashed}
  end

  # Render an AST to source, converting a Printer exception (e.g. an unrenderable
  # node a buggy rule produced) into a value rather than a propagating crash.
  defp safe_print(ast) do
    {:ok, Cure.Compiler.Printer.quoted_to_string(ast)}
  rescue
    _ -> {:error, :unprintable}
  end

  # The lossless-comment check for `verify/3`: every `#`-led comment body, trimmed,
  # sorted. Coarse-but-adequate — KNOWN latent limitation: the scan is not
  # quote-aware, so a `#` inside a string literal is misread as a comment. Harmless
  # today (no migrate rule rewrites string-literal contents, so the bogus entry is
  # stable across baseline/output and never trips `:comment_dropped`); make this
  # quote-aware before adding any rule that edits inside string literals.
  defp comment_texts(src) do
    src
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/#+\s?(.*)$/, line) do
        [_, txt] -> [String.trim(txt)]
        _ -> []
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.sort()
  end

  @typedoc "Why a path failed the git preflight."
  @type git_reason :: :dirty | :untracked | :not_a_repo

  @doc """
  Preflight git-safety guard for `cure migrate` (spec §5.7): every path must be
  tracked and porcelain-clean before any file is rewritten, so a migration can
  always be reviewed and reverted as a diff. Classifies **each** path
  independently (no short-circuit) and returns one reason per failing path — a
  batch can legitimately mix untracked scratch files with merely-dirty tracked
  ones, and a single reason-for-the-whole-batch could not represent that without
  misreporting some paths.

  Returns `:ok` when every path is clean, else `{:error, [{path, reason}]}` in
  the order `paths` was given, where `reason` is `:untracked`, `:dirty`, or
  `:not_a_repo`.

  Each `git` invocation pins `cd: Path.dirname(path)` (git discovers the repo
  root upward from there): `git status`/`git ls-files` resolve relative to the
  caller's cwd, not the repo containing `path`, so without this a path in a
  different repo than the caller's cwd fails with "outside repository".
  """
  @spec git_guard([Path.t()]) :: :ok | {:error, [{Path.t(), git_reason()}]}
  def git_guard(paths) do
    failures =
      paths
      |> Enum.map(fn path -> {path, classify_path(path)} end)
      |> Enum.reject(fn {_path, reason} -> reason == :clean end)

    if failures == [], do: :ok, else: {:error, failures}
  end

  defp classify_path(path) do
    dir = Path.dirname(path)
    # Pin the git call to the file's own directory and address the file by its
    # basename there: this resolves correctly whether `path` was given absolute
    # or relative to a different cwd (a relative `lib/a.cure` addressed from
    # `cd lib` would otherwise become `lib/lib/a.cure` and misclassify).
    name = Path.basename(path)

    case System.cmd("git", ["ls-files", "--error-unmatch", name], cd: dir, stderr_to_stdout: true) do
      {_out, 0} -> porcelain_status(name, dir)
      {out, _nonzero} -> if not_a_repo?(out), do: :not_a_repo, else: :untracked
    end
  end

  defp porcelain_status(name, dir) do
    case System.cmd("git", ["status", "--porcelain", "--", name], cd: dir) do
      {"", 0} -> :clean
      {_nonempty, 0} -> :dirty
      {_out, _nonzero} -> :dirty
    end
  end

  defp not_a_repo?(output), do: output =~ "not a git repository"

  @doc """
  Build the per-file context consulted by `:needs_resolution` rules: the set of
  type names (as strings) in scope for `ast`. Seeded with Cure's built-in
  primitive type names (`@builtin_type_names`, owned by the lint) — and
  unioned with the type names this file declares (structs, enums, type aliases,
  and indexed families) and those it imports.

  `file` is the consuming source's path; it is needed to resolve USER-module
  imports (a `use MyApp.Foo` has no path convention — see `imported_names/2` —
  so the only handle is a sibling `.cure` file next to `file`). Callers with no
  path may use the arity-1 form, which resolves only `Std.*` + auto-prelude
  imports (a user import then contributes nothing rather than crashing).
  """
  @spec build_ctx(Rule.ast(), Path.t()) :: MapSet.t()
  def build_ctx(ast, file \\ "nofile") do
    builtin_type_names()
    |> MapSet.union(declared_type_names(ast))
    |> MapSet.union(declared_ctor_names(ast))
    |> MapSet.union(imported_names(ast, file))
  end

  # The built-in type names in scope for every module — real Cure types (never
  # free type variables) that must NOT be lowercased. The lint owns this surface
  # vocabulary directly (the classic type-checker Env, which formerly supplied
  # the first group, was deleted in the #18 rip-out). Group 1 = the surface
  # primitive types (`Int`/`Float`/`String`/`Bool`/`Atom`/`Unit`/`Any`/`Never`/
  # `Char`). Group 2: `Type` is the universe kind (`fn F(a: Type) -> Type`);
  # `Binary`/`Bitstring` are BEAM primitive types; `Map`/`Tuple` are
  # built-in containers; `Nat` is the Int-tier foundational numeric (dedicated
  # kernel literal forms). Without these, container/kind signatures warn
  # spuriously and `cure migrate --all` would corrupt them (`Tuple` -> `tuple`).
  # Data *constructors* of imported inductives (e.g. `Std.Nat`'s `Z`/`S`) are a
  # different category — resolved per-import (`imported_names/2`), not here.
  #
  # Unindexed `Pid` and `Ref` belonged to the retired unrestricted process
  # surface. The formal OTP API provides `Std.Otp.Pid(m)`, `MonitorRef`, and
  # `TimerRef`; treating the old spellings as builtins hid stale declarations
  # until a later Core read-back happened to expose `unknown_global`. They are
  # withdrawn names, not builtins and not type variables, and are recognized as
  # such by `Cure.Elab.Resolution.retired_type_name?/1` — which
  # `Rules.UppercaseTypeVar` consults so it does not lowercase them into fresh
  # variables. Do not re-add them here: that would restore the hiding.
  @builtin_type_names ~w(Int Float String Bool Atom Unit Any Never Char
                         Type Binary Bitstring Map Tuple Nat)

  defp builtin_type_names, do: MapSet.new(@builtin_type_names)

  # Every type name this file introduces, gathered by a full pre-order walk:
  #   * `{:container, [container_type: :struct | :enum | :opaque | :primitive, name: n], _}` —
  #     records, enums, and bodyless opaque handles (`opaque type GCounter`)
  #   * `{:type_annotation, [name: n], _}` — `typealias N = …`
  #   * `{:indexed_type, [name: n], _}` — indexed families (defensive; carries :name)
  #   * `{:import, [items: [...], alias: a], _}` — `use Mod.{A, B}` / `use Mod as A`
  defp declared_type_names(ast) do
    ast |> collect_type_names([]) |> MapSet.new()
  end

  defp collect_type_names({:container, meta, ch}, acc) when is_list(ch) do
    acc =
      case Keyword.get(meta, :container_type) do
        t when t in [:struct, :enum, :opaque, :primitive] -> maybe_name(meta, acc)
        _ -> acc
      end

    Enum.reduce(ch, acc, &collect_type_names/2)
  end

  # `use Mod.{A, B}` / `use Mod as Alias` bring type constructors into scope; their
  # names must be treated as declared, not as free type variables. The import node's
  # body is empty, so this is the only place the selectively-imported items and the
  # alias enter `ctx`.
  defp collect_type_names({:import, meta, _}, acc) do
    items = Keyword.get(meta, :items, [])

    names =
      case Keyword.get(meta, :alias) do
        a when is_binary(a) -> [a | items]
        _ -> items
      end

    Enum.reduce(names, acc, fn
      n, a when is_binary(n) -> [n | a]
      _, a -> a
    end)
  end

  defp collect_type_names({:type_annotation, meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, maybe_name(meta, acc), &collect_type_names/2)
  end

  defp collect_type_names({:indexed_type, meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, maybe_name(meta, acc), &collect_type_names/2)
  end

  # A `macro` declaration synthesizes typed record types for its rules — a legacy
  # `computed by` rule gets `syntax_type(keyword)` (`fsm` -> `FsmSyntax`), a
  # structured `syntax family`/`expands with` gets `syntax_type(family)`
  # (`FsmDefinition` -> `FsmDefinitionSyntax`) plus its `…InputSyntax`. Those
  # records are generated during lowering (`MacroFamily.generated_record_declarations`,
  # the same pipeline `Program.declarations`/`LiftModule.unit_declarations` run),
  # so they are absent from the raw source AST this walk sees. Reproduce the exact
  # lowering to learn their names; otherwise a sibling expander's signature
  # (`fn derive_fsm(input: FsmSyntax)`) is misread as carrying a free type
  # variable and spuriously warned/lowercased.
  defp collect_type_names({:macro_def, meta, rules}, acc)
       when is_list(meta) and is_list(rules) do
    MacroFamily.lowered_rules(meta, rules)
    |> Enum.filter(&(&1[:kind] == :computed))
    |> Enum.uniq_by(&Map.get(&1, :syntax_type))
    |> Enum.flat_map(&MacroFamily.generated_record_declarations(meta, &1))
    |> Enum.reduce(acc, fn
      {:container, cmeta, _fields}, a -> maybe_name(cmeta, a)
      _other, a -> a
    end)
  end

  # A `:computed_use` is a use-site macro invocation (`actor … on_call …`). The
  # invoked family's expander emits an *ambient* enum type into the CALLER's
  # module during `expand_declaration_uses` — a step that runs after this lint
  # (`compiler.ex`: `migrate_warn` precedes `expand_declaration_uses`). A
  # handwritten sibling then annotates against that derived type
  # (`fn make_message() -> ActorMessage = Inc`), but it is absent from the
  # surface AST this walk sees, so it was misread as a free type variable and
  # lowercased (`ActorMessage` -> `actormessage`). The generated names are string
  # literals inside the expander bodies (`enum_type("ActorMessage"/"ActorRequest",
  # …)` in `lib/std/actor.cure`), so — unlike a `:macro_def`'s records — they are
  # not recoverable from lowering rules; the family keyword names them here.
  # Over-listing a name only makes the lint MORE conservative (these
  # family-reserved names never double as free type variables), and the addition
  # is scoped to modules that actually invoke the family, so a real free `T` in
  # an actor module still warns.
  #
  # `fsm` is deliberately absent: its derived event type is declared as `Event`
  # INSIDE the generated module, not ambiently beside the caller, so there is no
  # invisible name to protect.
  defp collect_type_names({:computed_use, meta, ch}, acc) when is_list(ch) do
    acc = Enum.reduce(computed_use_ambient_types(meta), acc, fn n, a -> [n | a] end)
    Enum.reduce(ch, acc, &collect_type_names/2)
  end

  defp collect_type_names({_k, _meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, acc, &collect_type_names/2)
  end

  defp collect_type_names({_k, _meta, _name, inner}, acc), do: collect_type_names(inner, acc)
  defp collect_type_names(l, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_type_names/2)
  defp collect_type_names(_other, acc), do: acc

  # The ambient enum type names a stdlib concurrency family emits into its
  # caller. Keyed on the surface keyword carried by the `:computed_use` node,
  # matching the `enum_type(…)` emit sites in the family sources. `ActorRequest`
  # only materializes when an `on_call` channel is present, but listing it
  # unconditionally is harmless — it is a reserved family type name, never a free
  # type variable.
  defp computed_use_ambient_types(meta) do
    case Keyword.get(meta, :keyword) do
      "actor" -> ["ActorMessage", "ActorRequest"]
      _ -> []
    end
  end

  defp maybe_name(meta, acc) do
    case Keyword.get(meta, :name) do
      n when is_binary(n) -> [n | acc]
      _ -> acc
    end
  end

  # Every data-constructor name this file introduces. A constructor spelled in an
  # index/argument position (`Optic(s, a, LensKind)`) parses as a bare
  # `{:variable}` node indistinguishable from a free type var, so its name must
  # be in `ctx` too — otherwise the rule lowercases it (`LensKind` -> `lenskind`),
  # corrupting the family index. Three surface spellings carry constructors:
  #   * `{:variable, [variant: true], name}` — nullary enum variant (`LensKind`)
  #   * `{:function_def, [variant: true, name: n], _}` — field-carrying variant
  #     (`MkLensRep(a, (a) -> s)`), a constructor decl reusing the fn-def node
  #   * `{:gadt_ctor, [name: n], [_arrow_chain]}` — an `indices`-form GADT constructor
  defp declared_ctor_names(ast) do
    ast |> collect_ctor_names([]) |> MapSet.new()
  end

  defp collect_ctor_names({:variable, meta, name}, acc) when is_binary(name) do
    if Keyword.get(meta, :variant) == true, do: [name | acc], else: acc
  end

  defp collect_ctor_names({:function_def, meta, ch}, acc) when is_list(ch) do
    acc = if Keyword.get(meta, :variant) == true, do: maybe_name(meta, acc), else: acc
    Enum.reduce(ch, acc, &collect_ctor_names/2)
  end

  defp collect_ctor_names({:gadt_ctor, meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, maybe_name(meta, acc), &collect_ctor_names/2)
  end

  defp collect_ctor_names({_k, _meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, acc, &collect_ctor_names/2)
  end

  defp collect_ctor_names({_k, _meta, _name, inner}, acc), do: collect_ctor_names(inner, acc)
  defp collect_ctor_names(l, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_ctor_names/2)
  defp collect_ctor_names(_other, acc), do: acc

  # The type + constructor names each `use`d module exports, resolved by reading
  # the imported module's source and collecting its declarations (the same walk
  # used for this file). An imported type or constructor spelled in a signature
  # (`Vector(a, Z)` — `Z` from `Std.Nat`) is a real name, not a free type
  # variable, but only the imported module knows it. DIRECT imports only (no
  # transitive walk): a name used in this file's signatures is either declared
  # here, a builtin, or directly imported. Best-effort and FAIL-OPEN — an
  # unresolvable import (non-stdlib module, missing source dir, read/parse
  # failure) contributes nothing rather than crashing the warn-only lint.
  defp imported_names(ast, file) do
    sources = Enum.uniq(collect_import_sources(ast, []) ++ prelude_sources())
    # User (non-`Std.*`) imports have no path convention — Cure resolves them by
    # co-compilation, not by name→path — so they cannot be read the way a stdlib
    # source is. The only handle a single-file lint has is the sibling `.cure`
    # files next to `file`; build a mod-name→exports map from them once, up front.
    sibling_exports = sibling_module_exports(file, sources)

    Enum.reduce(sources, MapSet.new(), fn source, acc ->
      names =
        case stdlib_source_path(source) do
          {:ok, path} -> exported_names_of_file(path)
          :error -> {:ok, Map.get(sibling_exports, source, MapSet.new())}
        end

      case names do
        {:ok, ns} -> MapSet.union(acc, ns)
        :error -> acc
      end
    end)
  end

  # Prelude membership lives at the definition site. The migration linter reads
  # the same `@prelude` markers as the loader instead of maintaining a second
  # compiler-owned module list.
  defp prelude_sources do
    dirs = Cure.Stdlib.Paths.source_dirs()
    key = {:migrate_prelude_sources, dirs}

    case Process.get(key) do
      nil ->
        sources = compute_prelude_sources(dirs)
        Process.put(key, sources)
        sources

      sources ->
        sources
    end
  end

  defp compute_prelude_sources(dirs) do
    dirs
    |> Enum.flat_map(&Path.wildcard(Path.join(&1, "*.cure")))
    |> Enum.uniq()
    |> Enum.flat_map(fn path ->
      with {:ok, src} <- File.read(path),
           true <- Regex.match?(~r/^\s*@prelude\s*$/m, src),
           {:ok, name} <- module_name_of_file(path) do
        [name]
      else
        _ -> []
      end
    end)
  end

  defp collect_import_sources({:import, meta, _}, acc) do
    case Keyword.get(meta, :source) do
      s when is_binary(s) -> [s | acc]
      _ -> acc
    end
  end

  defp collect_import_sources({_k, _meta, ch}, acc) when is_list(ch),
    do: Enum.reduce(ch, acc, &collect_import_sources/2)

  defp collect_import_sources({_k, _meta, _name, inner}, acc),
    do: collect_import_sources(inner, acc)

  defp collect_import_sources(l, acc) when is_list(l),
    do: Enum.reduce(l, acc, &collect_import_sources/2)

  defp collect_import_sources(_other, acc), do: acc

  # The type + constructor names a `.cure` source at `path` exports. Fail-open:
  # any read/lex/parse failure yields `:error` and contributes nothing.
  #
  # Memoized per process, keyed by (path, mtime): a fixpoint re-resolves every import
  # on each pass, and each file's lint re-reads its siblings, so without this the same
  # sibling sources are read+lexed+parsed O(files × passes) times — quadratic in the
  # stdlib size, which times out the whole-stdlib monotone test as the tree grows. The
  # mtime in the key keeps it correct if a source is rewritten mid-process (temp files).
  defp exported_names_of_file(path) do
    mtime =
      case File.stat(path, time: :posix) do
        {:ok, %File.Stat{mtime: t}} -> t
        _ -> :nostat
      end

    key = {:mig_exports, path, mtime}

    case Process.get(key) do
      nil ->
        result = compute_exported_names_of_file(path)
        Process.put(key, result)
        result

      cached ->
        cached
    end
  end

  defp compute_exported_names_of_file(path) do
    with {:ok, src} <- File.read(path),
         {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false),
         ast <- Cure.Compiler.Parser.harvest(tokens, path, BuiltinFixity.table(), Cure.Edition.current()) do
      {:ok, MapSet.union(declared_type_names(ast), declared_ctor_names(ast))}
    else
      _ -> :error
    end
  end

  # Resolve USER-module imports (`use MyApp.Foo`, i.e. any non-`Std.*` source)
  # by scanning the consuming file's directory. Cure has no name→path convention
  # for user modules — the real compiler resolves them by co-compiling all input
  # files together, a registry this per-file lint does not have — so the only
  # sound handle is the sibling `.cure` sources next to `file`. Each sibling is
  # matched to an import by its declared `mod` NAME (robust to arbitrary
  # filenames), and only the requested sources are kept. Returns a
  # `mod-name-string => exported-names` map. Scans nothing (returns `%{}`) when
  # there is no file path or no user import — so the pure-`Std` case pays zero
  # directory I/O. Fail-open throughout.
  defp sibling_module_exports(file, sources) do
    user_sources =
      sources
      |> Enum.reject(&match?({:ok, _}, stdlib_source_path(&1)))
      |> MapSet.new()

    if file in [nil, "", "nofile"] or MapSet.size(user_sources) == 0 do
      %{}
    else
      Path.dirname(file)
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.reduce(%{}, fn path, acc ->
        with {:ok, name} <- module_name_of_file(path),
             true <- MapSet.member?(user_sources, name),
             {:ok, names} <- exported_names_of_file(path) do
          Map.put(acc, name, names)
        else
          _ -> acc
        end
      end)
    end
  end

  # The declared `mod`/`proof`-container name of the source at `path`, as a
  # string, mirroring `Cure.Elab.Program.find_module_name/1`. Fail-open.
  defp module_name_of_file(path) do
    with {:ok, src} <- File.read(path),
         name when is_binary(name) <- FixityScan.harvest_source(src, path, BuiltinFixity.table()).module do
      {:ok, name}
    else
      _ -> :error
    end
  end

  # Resolve a `Std.<Name>` import source to its `.cure` file, searching the same
  # stdlib source directories the elaborator uses (`import_source_path/1`). Only
  # `Std.*` is handled — a bare/user module resolves to `:error` and is skipped.
  defp stdlib_source_path(source) do
    case source do
      "Std." <> _ ->
        case Cure.Compiler.SourceResolver.module_path(source) do
          {:ok, path} -> {:ok, path}
          :not_found -> :error
        end

      _ ->
        :error
    end
  end
end
