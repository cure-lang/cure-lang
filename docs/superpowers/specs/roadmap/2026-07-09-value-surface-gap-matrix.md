# Value-Surface Gap Matrix (scout artifact, 2026-07-09)

Read-only inventory backing the value-surface parity roadmap (`2026-07-09-value-surface-roadmap-design.md`). Anchors verified against the tree on 2026-07-09; classic files are the coverage/semantics REFERENCE only (firewall test 8d7a5eb forbids the dependent pipeline referencing them).

## 0. Core target inventory

`lib/cure/core/term.ex:11-26` — entire Core grammar: `{:type,l} {:var,k} {:pi} {:lam} {:app} {:data,name,params,indices} {:ctor,name,args} {:case,scrut,motive,branches} {:global} {:int_type} {:int_lit,n} {:float_type} {:float_lit,f}`.

Seeded builtins (`core/builtins.ex:14-19,28-67`): families `Bool(False|True)`, `Nat(Z|S)`, `Equivalent`, `Sigma(mk_pair/2)`; op globals `int_*`/`float_*` + `struct_eq`/`struct_ne`.

**NO Core target exists for:** string literals, char, atom/symbol, binary/bitstring, maps, native lists, tuples of arity ≠ 2, regex. Emit (`elab/emit.ex:162-189`): ctor → Bool atom / Nat integer / Sigma bare 2-tuple / general tagged tuple `{:Name,…}`; NO string/map/native-cons lowering, NO `@extern` lowering. `declarations.ex:1095-1097` maps only Int/Float type names; `String`/`Map`/`List` annotations become `{:data, Name, [], indices}` family references (`elaborator.ex:4876-4893`) — dangling unless the family exists.

## 1. Elaborator reject inventory

Dispatchers: `elaborate_expr_typed` (infer, elaborator.ex:49-554), `elaborate_expr_checked` (check, 808-1033), `elaborate_expr` (type-level, 4735-4793). `unsupported_expression` catch-alls: 38, 431, 459, 489, 511, 554, 4789, 4793; type catch-all 4893; block 3641, 3671; pattern rejects 2189, 2242, 2393, 2425, 2704, 2748, 2933, 3036, 3266, 3750, 3754, 1821; guard rejects 2527, 2531, 2579-2600, 2827-2895, 3101; with-abs 1556, 1781, 1790, 3864.

## 2. Gaps, ordered by unlock impact

| # | Gap | Modules unlocked | Elaborator status | Classic reference | Core target |
|---|---|---|---|---|---|
| G1 | `@extern` FFI | ~14 (crdt 22/22 fns, string 17/17, regex 7/7, http 4/4 are 100%-extern; map 11/14, math 10/18, time 9/13, system 6/10, gen 5/10, io 4/8, json, test, list, pair) | ZERO handling in elab/core/emit (parser meta `extern: {m,f,a}` at parser.ex:4760-4768 unread; declarations.ex:26/45 + emit.ex:118-138 assume a body) | codegen.ex:625,643-645 wrapper → remote call; E056/E057 (errors.ex:56-63,1325-1371) | new: extern-marked global, emit → remote `{:call,{:remote,…}}` |
| G2 | `pickup` | 10 (iter 9, list 9, core 7, math 5, test 5, set 2, gen 2, map, option, result) | REJECTED (no clause → :38/:554) | codegen.ex:780,1454-1500 nested Bool case; checker.ex:1349-1366 (E079 Bool guards, E080 join, terminator) | EXISTS — desugar to nested `{:case}` on Bool like `if` (elaborator.ex:471,1024-1028) |
| G3 | List + `[…]`/`[h\|t]` + list patterns | ~9 (list 82 sites, match 26, pair 12, iter 11, non_empty 5, set 4, gen 4, map 8, option) | REJECTED (no :list clause; patterns → nested_constructor_arg 3736-3754) | codegen.ex:788,1611-1646 native cons; pattern_compiler.ex:98-99; checker {:list,elem}, empty={:list,:never} 1410-1431 | Std.List family exists; REPRESENTATION DECISION: emit tagged tuple `{:Cons,h,t}` today vs classic native cons (FFI/`:lists` interop) |
| G4 | String + literals + `<>` | ~9 (string, http, json, regex, io, time, gen, map, crdt) | REJECTED 3 ways: :string subtype → :458; `<>` no binop (prim_op :630 → :unsupported_op → :511); `String` = dangling data | codegen.ex:920-921,946-948 UTF-8 `{:bin}`; checker.ex:1050; pattern_compiler.ex:168,180-182 | NONE — new `{:string_type}`/`{:string_lit}` + str_* builtin ops, or List Char |
| G5 | Atom/symbol literals | large counts but INFLATED by `@extern(:m,:f)` decorator atoms (AMBIGUOUS); real use = tags/status | REJECTED (:symbol → :458) | codegen.ex:929-930; pattern_compiler.ex:171 | mostly subsumed by ADT ctors + G1; dynamic atoms deferred |
| G6 | Lambda in inference position | core, iter, list, set + every HOF caller (option/result map/filter) | PARTIAL: checked-mode HANDLED (1012-1052); inference REJECTED | codegen.ex:798,1678-1698; checker.ex:1466,1929-1933 | `{:lam}` exists; needs expected-type propagation to HOF args |
| G7 | Tuples arity ≥3 | pair, match, misc | PARTIAL: 2-tuple → Sigma (980-1003, 4765); ≥3 reject; nested pattern → nested_tuple_element 2748 | codegen.ex:791,1650-1658; checker {:tuple,types} 1437-1439 | nested Sigma sugar or new builtin |
| G8 | Maps `{k=>v}` | map, json, http, crdt | REJECTED | codegen.ex:794,1663-1674; checker {:map,k,v} 1444-1460; pattern_compiler.ex:106 | NONE — new builtin or extern-backed opaque |
| G9 | String interpolation | low | REJECTED | codegen.ex:802,1702-1720 iolist + iolist_to_binary | rides G4 |
| G10 | Comprehensions + ranges | list, iter, math | REJECTED | codegen.ex:828,1848; :810,1786; checker 942-945 | desugar to List + recursion (rides G3) |
| G11 | Binary/bitstring | low | REJECTED (:bytes → :458) | codegen.ex:938-939,1006-1027; pattern_compiler.ex:146-149,186-199 | new builtin or extern BIFs |
| G12 | send/throw/early_return/try/async | gen, system | REJECTED | codegen.ex:820,824,814,832,762 | deferred to Effect/typed-OTP tracks (see effects-in-core + typed-beam-process-algebra memories) |

**Already at parity (do NOT re-port):** record_update; `if`; arithmetic/cmp/and/or/==/!= binops (NOT `<>`, NOT Float `rem`); unary `not`; 2-tuple→Sigma; checked-mode lambda; match/with_abs; int/float/bool literal chains (2610-2718); linear non-nested ctor patterns; Σ attribute_access (427-441).

## 3. Std-module → gap mapping (the ratchet)

| module | dominant blocker | first-wave gap |
|---|---|---|
| string / crdt / regex / http | G1 extern (+G4 String) | extern + String |
| map | G8 Map + G1 | Map + extern |
| json | G4/G8 + record | String/Map |
| io / time / system | G1 + G4/atoms | extern |
| gen | G1 + G3 + pickup | extern + List |
| math / test / core | G2 pickup (+G1 math) | pickup |
| list / match / non_empty | G3 List (+pickup) | List |
| iter / set | G3 + G2 + G6 HOF | List + pickup + lambda |
| pair | G7 tuples + G3 | tuples/List |
| option / result | G6 HOF + G2 | lambda |

## 4. Behavioral oracles (classic test pins, survive until rip-out)

codegen_test.exs (literals/lists/tuples/maps/records/lambda/conditional), pattern_compiler_test.exs, pickup_test.exs (W081/W082/E076-E080), match_spec_test.exs, parser_destructuring_test.exs, multi_head_cons_test.exs, bin_segment_test.exs, binary_comprehension_test.exs, lambda_block_test.exs, with_abs_codegen_test.exs, record_defaults_test.exs, checker_test.exs (typing rules).

## 5. Flagged ambiguities

1. `@extern` dependent failure mode not run-confirmed (zero handling is certain; reject vs raise unknown).
2. Atom value-position counts inflated by decorator atoms.
3. List representation fork (resolved in the roadmap: native cons via the Bool/Nat/Sigma special-emit precedent).
4. `String` struct_eq behavior undefined until G4 lands.
