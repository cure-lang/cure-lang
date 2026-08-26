" Vim syntax file
" Language:    Cure
" Maintainer:  Cure project
" Last Change: 2026 Apr 23
" Target:      Cure 0.28.2 (Talk Back)
"
" Grammar buckets mirror `Makeup.Lexers.CureLexer` and `highlightjs-cure`
" so every Cure highlighter agrees on what is syntactic vs. user code.
" Identifiers may end in `?` or `!`, so `is_empty?` and `stop!` must
" lex as a single word and never collapse onto the bare keyword.

if exists("b:current_syntax")
  finish
endif

syn case match

" --- Comments ---------------------------------------------------------------
" Cure has three comment flavours (all lexed as comments by the compiler):
"
"   ### ... ###  fenced multi-line doc comment (v0.17.0+)
"   ## ...       single-line doc comment
"   # ...        plain line comment
"
" The fenced region MUST be declared before the single-line matches so its
" start pattern wins over `##.*$`. The single-line matches use a negative
" lookahead so `###` never matches them by accident.
syn region cureFencedDoc
      \ start="###"
      \ end="###"
      \ contains=cureTodo,cureDocTag,@Spell
      \ keepend

syn match  cureDocComment "\v##(#)@!.*$" contains=cureTodo,cureDocTag,@Spell
syn match  cureComment    "\v#(#)@!.*$"  contains=cureTodo,@Spell
syn keyword cureTodo      contained TODO FIXME NOTE XXX HACK BUG
syn match   cureDocTag    contained "\v\@\w+"

" Fenced doc comments can span arbitrarily many lines. Sync from the start
" of the buffer so the region state is always correct, regardless of where
" the viewport lands. Cure source files are small enough that this is cheap.
syntax sync fromstart

" --- Strings, regexes, char literals ----------------------------------------
" Strings support #{...} interpolation and \n \r \t \\ \" \uXXXX escapes.
syn region cureString
      \ matchgroup=cureStringDelim
      \ start=+"+ skip=+\\.+ end=+"+
      \ contains=cureEscape,cureInterpolation,@Spell
syn match  cureEscape         contained "\v\\(u\x{4}|[ntr\\\"'])"
syn region cureInterpolation  contained
      \ matchgroup=cureInterpolationDelim
      \ start="#{" end="}"
      \ contains=TOP

" Regex literal: ~r/.../flags. Keep the end bound anchored so a stray
" slash in code can't drag the region forward.
syn region cureRegex
      \ matchgroup=cureRegexDelim
      \ start=+\~r/+ skip=+\\.+ end=+/[a-zA-Z]*+
      \ contains=cureEscape,@NoSpell
      \ keepend

" Char literals come in two forms:
"   'c' or '\n'    -- a single character or escape in single quotes
"   ?c  or ?\n     -- Erlang-style character literal
" Both are bounded matches (never regions) to avoid a stray apostrophe in
" prose (e.g. "Cure's") dragging the highlighter forward.
syn match  cureQuotedChar "\v'([^'\\]|\\.)'"                contains=cureEscape
syn match  cureErlangChar "\v\?(\\[\\'\"ntrabfv0]|[[:print:]])"

" --- Numbers ----------------------------------------------------------------
" `_` is a legal digit separator in every base.
syn match cureFloat  "\v<\d[\d_]*\.\d[\d_]*([eE][+-]?\d[\d_]*)?>"
syn match cureNumber "\v<0x[0-9a-fA-F][0-9a-fA-F_]*>"
syn match cureNumber "\v<0b[01][01_]*>"
syn match cureNumber "\v<\d[\d_]*>"

" --- Atoms, holes, decorators -----------------------------------------------
" Atoms keep the trailing `?`/`!` the same as identifiers.
syn match  cureAtom "\v\:[a-z_][a-zA-Z0-9_]*[!?]?"

" Typed holes -- `?_` anonymous, `?name` named.
syn match  cureHole "\v\?[A-Za-z_][A-Za-z0-9_]*"

" Attributes / decorators -- `@record`, `@derive`, `@deprecated`, etc.
syn match  cureAttribute "\v\@[A-Za-z_][A-Za-z0-9_]*"

" --- Keywords ---------------------------------------------------------------
" Control flow
syn keyword cureKeyword if then else elif match return throw try catch finally
syn keyword cureKeyword when where in for do of end with yield
syn keyword cureKeyword assert_type rewrite

" Declarations (top-level and nested containers)
syn keyword cureDeclaration fn mod rec fsm proto impl type let
syn keyword cureDeclaration actor sup app proof
syn keyword cureDeclaration local use as extern

" Concurrency / message passing
syn keyword cureConcurrency spawn send receive after

" FSM / container lifecycle hooks
syn keyword cureFsmCallback on_start on_stop on_transition on_enter on_exit
syn keyword cureFsmCallback on_failure on_timer on_message on_phase

" Literal constants
syn keyword cureBoolean true false
syn keyword cureConstant nil

" Built-in BEAM / Cure types
syn keyword cureBuiltinType Int Float Bool String Atom Bitstring Binary
syn keyword cureBuiltinType Char Any Unit Void Nat
syn keyword cureBuiltinType List Tuple Map Set Pair Vector
syn keyword cureBuiltinType Option Result Pid Ref
syn keyword cureBuiltinType Sigma Pi Eq DPair

" Well-known constructors / canonical proofs
syn keyword cureConstructor Ok Error Some None
syn keyword cureConstructor Zero Succ Pred Self refl

" --- Operators --------------------------------------------------------------
syn keyword cureOperator and or not

" FSM transition literal: `--event-->` (event name may end in ?/!).
" Matched before the generic operator table so the arrow doesn't split.
syn match cureFsmTransition "\v--[A-Za-z_][A-Za-z0-9_]*[!?]?--\>"

" Melquiades send operator: ASCII `<-|` and the envelope glyph U+2709 (✉).
syn match cureOperator "\v\<-\|"
syn match cureOperator "\%u2709"

" Arrows and pipes (multi-char first so they win)
syn match cureOperator "\v--\>"
syn match cureOperator "\v-\>"
syn match cureOperator "\v\<-"
syn match cureOperator "\v\=\>"
syn match cureOperator "\v\|\>"

" Comparison
syn match cureOperator "\v\=\="
syn match cureOperator "\v!\="
syn match cureOperator "\v\<\="
syn match cureOperator "\v\>\="
syn match cureOperator "\v\<\>"

" Monad / applicative / functor sugar
syn match cureOperator "\v\>\>\="
syn match cureOperator "\v\>\>"
syn match cureOperator "\v\<\*\>"
syn match cureOperator "\v\<\*"
syn match cureOperator "\v\*\>"
syn match cureOperator "\v\<\$"
syn match cureOperator "\v\$\>"

" Compound assignment
syn match cureOperator "\v\+\="
syn match cureOperator "\v-\="
syn match cureOperator "\v\*\="
syn match cureOperator "\v/\="

" Range
syn match cureOperator "\v\.\.\="
syn match cureOperator "\v\.\."

" Cons / list / misc
syn match cureOperator "\v::"
syn match cureOperator "\v\+\+"
syn match cureOperator "\v--"
syn match cureOperator "\v\|\|"
syn match cureOperator "\v\&\&"
syn match cureOperator "\v\*\*"

" Single-char math / assignment / guard heads
syn match cureOperator "\v[+\-*/%]"
syn match cureOperator "\v\="
syn match cureOperator "\v[<>]"
syn match cureOperator "\v\|"

" --- Delimiters -------------------------------------------------------------
syn match cureDelimiter "\v[(),;]"
" Tuple / map prefix `%[...]` / `%{...}` -- highlight the `%` distinctly
syn match cureTuplePrefix "\v\%\ze[\[{]"

" --- Identifiers, function / module / type heads ----------------------------
" Dotted module path (e.g. Std.Vector, Cure.Types.Pi)
syn match cureModulePath "\v<[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)+>"

" Type / constructor identifiers (CamelCase)
syn match cureType "\v<[A-Z][A-Za-z0-9_]*>"

" Lowercase identifiers (functions, variables). Allow trailing ? or !.
syn match cureIdentifier "\v<[a-z_][A-Za-z0-9_]*[!?]?>"

" Function definition heads: `fn name(...)`
syn match cureFunctionDef "\vfn\s+\zs[a-z_][A-Za-z0-9_]*[!?]?"

" Container heads: `mod Name`, `actor Name`, `sup Name`, `app Name`,
" `proof Name`. Allow dotted module paths for `mod` and `sup`.
syn match cureModuleHead "\vmod\s+\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"
syn match cureActorHead  "\vactor\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureSupHead    "\vsup\s+\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"
syn match cureAppHead    "\vapp\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureProofHead  "\vproof\s+\zs[A-Z][A-Za-z0-9_]*"

" Record, fsm, proto heads
syn match cureRecordHead "\vrec\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureFsmHead    "\vfsm\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureProtoHead  "\vproto\s+\zs[A-Z][A-Za-z0-9_]*"

" `impl Trait`, `impl Trait for Type`, `use Foo.Bar`
syn match cureImplHead "\vimpl\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureImplFor  "\vimpl\s+[A-Z][A-Za-z0-9_]*\s+for\s+\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"
syn match cureUseHead  "\vuse\s+\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"

" `type Name` heads (ADT / alias / refinement)
syn match cureTypeHead "\vtype\s+\zs[A-Z][A-Za-z0-9_]*"

" Type annotation after `:` -- a leading type name in `name: Type`
syn match cureTypeAnnotation "\v:\s*\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"

" --- Highlight links --------------------------------------------------------
hi def link cureComment            Comment
hi def link cureDocComment         SpecialComment
hi def link cureFencedDoc          SpecialComment
hi def link cureDocTag             Tag
hi def link cureTodo               Todo

hi def link cureString             String
hi def link cureStringDelim        String
hi def link cureEscape             SpecialChar
hi def link cureInterpolation      Special
hi def link cureInterpolationDelim SpecialChar
hi def link cureRegex              String
hi def link cureRegexDelim         Delimiter

hi def link cureNumber             Number
hi def link cureFloat              Float

hi def link cureAtom               Constant
hi def link cureQuotedChar         Character
hi def link cureErlangChar         Character
hi def link cureHole               Special
hi def link cureAttribute          PreProc

hi def link cureKeyword            Statement
hi def link cureDeclaration        Keyword
hi def link cureConcurrency        Keyword
hi def link cureFsmCallback        Keyword
hi def link cureBoolean            Boolean
hi def link cureConstant           Constant

hi def link cureBuiltinType        Type
hi def link cureConstructor        StorageClass

hi def link cureFsmTransition      Special
hi def link cureOperator           Operator
hi def link cureDelimiter          Delimiter
hi def link cureTuplePrefix        Special

hi def link cureModulePath         Structure
hi def link cureType               Type
hi def link cureIdentifier         Identifier

hi def link cureFunctionDef        Function
hi def link cureModuleHead         PreProc
hi def link cureActorHead          PreProc
hi def link cureSupHead            PreProc
hi def link cureAppHead            PreProc
hi def link cureProofHead          PreProc
hi def link cureRecordHead         PreProc
hi def link cureFsmHead            PreProc
hi def link cureProtoHead          PreProc
hi def link cureImplHead           Special
hi def link cureImplFor            Type
hi def link cureUseHead            Include
hi def link cureTypeHead           PreProc
hi def link cureTypeAnnotation     TypeDef

let b:current_syntax = "cure"
