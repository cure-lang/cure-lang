# cure_calc

A four-function calculator, written in Cure, with no dependencies beyond the
standard library. This is the worked example behind
[`docs/GETTING_STARTED.md`](../../docs/GETTING_STARTED.md), which walks through
creating, compiling, running, and testing a project like this one from an empty
directory.

It is a pure Cure project: `Cure.toml`, `lib/`, `test/`, and nothing else. No
`mix.exs`, no Elixir wrapper.

## Layout

    Cure.toml            project manifest: name, version, edition, [doc]
    lib/calc.cure        mod Calc      -- the calculator itself
    lib/main.cure        mod Calc.Demo -- main/0, the entry point
    test/calc_test.cure  mod Calc.Test -- eight Std.Test assertions

## Commands

Run from this directory, with the `cure` escript on `PATH`:

```bash
cure check lib/calc.cure    # type-check one file
cure compile lib/           # compile the project to BEAM bytecode
cure run lib/main.cure      # compile the project and call main/0
cure test                   # run every test_* function under test/
cure fmt --check lib/ test/ # report unformatted files
cure doc lib/               # generate HTML docs into _build/cure/doc/
```

`cure run lib/main.cure` prints:

```text
cure_calc -- a four-function calculator in Cure

(2.0000 + (3.0000 * 4.0000)) = 14.0000
((7.0000 + 8.0000) / 2.0000) = 7.5000
-(10.0000 - 4.0000) = -6.0000
(1.0000 / 0.0000) ! division by zero
```

## What it demonstrates

- **Algebraic data types** -- `Op` is a four-variant enumeration, `Expr` is a
  recursive tree (`Lit`, `Neg`, `Bin`). Both use the multi-line `|` form.
- **Total evaluation** -- `eval/1` returns `Result(Float, String)`. Division by
  zero is an `Error` value, never an exception, so no arithmetic can crash the
  evaluator.
- **Exhaustive `match`** -- every `match` covers every constructor; the checker
  rejects a missing arm rather than deferring it to a runtime badmatch.
- **`pickup`** -- guard-style branching in `safe_div/2`.
- **Structural recursion** -- `eval/1` and `render/1` recurse into strictly
  smaller sub-trees, which is what lets the totality checker certify them.
- **Multiple modules in one project** -- `Calc.Demo` and `Calc.Test` reach
  `Calc` with `use Calc`; the compiler resolves it from source through the
  project's source roots.
- **A little FFI** -- `show/1` calls `:erlang.float_to_list/2` through
  `@extern` to print fixed-point numbers, because the shortest round-trip form
  (`1.4000000000000000e+01`) is unreadable in a transcript.
- **`Std.Test`** -- `assert`, `assert_eq`, and `Std.Result` helpers, run by
  `cure test`.

## Where to go next

- Add a parser: turn `"2 + 3 * 4"` into an `Expr` with `Std.String` and a
  recursive-descent function, and return `Result(Expr, String)`.
- Track precedence explicitly instead of parenthesising everything in
  `render/1`.
- Replace `Float` with a length-indexed or refined numeric domain and let the
  dependent checker carry the invariants; see
  [`docs/DEPENDENT_TYPES.md`](../../docs/DEPENDENT_TYPES.md).
