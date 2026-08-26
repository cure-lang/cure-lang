# cure bless

> **Removed.** `cure bless` depended on `Cure.Types.Checker`, the classic
> type checker retired when the compiler moved to the dependent-only
> pipeline (see the Unreleased section of `CHANGELOG.md`). `Cure.Bless`,
> `Cure.Bless.Advisor`, the `mix cure.bless` task, and the REPL `:bless`
> command no longer exist in the tree. This page is kept to record the
> pre-removal design in case a dependent-pipeline equivalent is built later.

`cure bless` was a Socratic type-error assistant that landed in
**v0.28.0**. For each type or refinement error in a `.cure` file it
displayed the diagnostic, explained what went wrong in one sentence,
proposed the best available fix, and prompted the user for permission
before touching anything on disk.

## CLI

```bash
cure bless lib/my_module.cure
cure bless lib/my_module.cure --batch   # suggestions only, no prompts
mix cure.bless lib/my_module.cure       # Mix task equivalent
```

## REPL

```text
cure(1)> :bless lib/my_module.cure
```

## Interaction model

For each error the assistant follows a four-step loop:

1. Print the Cure-formatted diagnostic (identical to what
   `cure check` would emit).
2. Display the top suggestion from `Cure.Bless.Advisor`.
3. Prompt `Apply? [y]es / [n]o / [s]kip`.
4. On `y`: apply the patch, write the modified source back to disk,
   and re-run the checker. On `n` or `s`: move to the next error.

After all errors are processed the session reports `:all_fixed`,
`:some_skipped`, or `:nothing_to_fix`.

## Example session

```text
error: type mismatch
 --> lib/moneta.cure:45
  | function 'deposit' declared return type Money but body has type
  | Result(Money, String)

  Suggestion (remove return type): Remove the return type annotation
  on line 45 and let the checker infer it.

  Apply? [y]es / [n]o / [s]kip: y
  Applied. Re-checking...
  No more errors.
```

## Batch mode

Pass `--batch` (or `-b`) to print every suggestion without
interactive prompting. Useful for CI inspection or scripted
workflows:

```bash
cure bless lib/ --batch 2>&1 | tee bless_report.txt
```

## Supported error patterns

`Cure.Bless.Advisor` recognises and produces machine-applicable
patches for five patterns:

| Error tag | Suggestion |
|-----------|-----------|
| `:type_mismatch` (declared return type) | Remove or widen the return-type annotation |
| `:type_mismatch` (argument) | Inspect the call site |
| `:constraint_violation` | Add a `when` guard at the call site |
| `:unbound_variable` | Insert a `let` binding or choose a name from the diagnostic's in-scope candidates |
| `:arity_mismatch` | Explain the expected argument count |
| `:non_exhaustive_match` | Insert a wildcard `_ -> throw "unhandled case"` arm |

Patches that modify source text work on a line-level basis: they
locate the relevant line in the source string, apply a targeted
regex substitution or a line insertion, and validate the result by
running the type checker again. When no patch function is available
for a given error shape, the suggestion is printed for human review
but the `[y]` option is disabled.

## Programmatic API

```elixir
# Non-interactive: returns a list of {error, [suggestion]} pairs
pairs = Cure.Bless.advise(source, "my_module.cure")

Enum.each(pairs, fn {err, [top | _rest]} ->
  IO.puts("#{top.kind}: #{top.description}")
  case top.patch.(source) do
    {:ok, fixed} -> File.write!("my_module.cure", fixed)
    {:error, _}  -> :skip
  end
end)
```

`Cure.Bless.bless_file/2` runs the interactive session for a path.
`Cure.Bless.advise/2` returns the pairs without side-effects.

## Related

- [`docs/REPL.md`](REPL.md) -- `:bless` meta-command.
- [`docs/OBSERVABILITY.md`](OBSERVABILITY.md) -- `cure top` and
  `cure trace`.
- [`docs/REPLAY.md`](REPLAY.md) -- `@record` annotation and
  `cure replay`.
