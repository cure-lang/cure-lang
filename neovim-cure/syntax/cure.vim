" Vim syntax file for Cure programming language
" Language: Cure
" Maintainer: Cure Core Team

if exists("b:current_syntax")
  finish
endif

" Comments
syn match cureComment "#.*$" contains=@Spell
syn region cureBlockComment start="#|" end="|#" contains=cureBlockComment,@Spell

" Keywords - Modules & Structuring
syn keyword cureModule mod use as type typealias opaque primitive indexed indices rec proto impl local interface implementation deriving
syn keyword cureOtpKeyword actor sup app fsm state event transition on_transition on_enter on_exit on_failure on_timer

" Keywords - Functions & Declarations
syn keyword cureKeyword fn let extern proof unsafe quote
syn keyword cureQuantity erased linear affine

" Keywords - Control Flow & Logic
syn keyword cureConditional match pickup if elif else then for do end in try catch finally throw return yield spawn send receive after when where
syn keyword cureOperatorWords and or not band bor bxor bsl bsr bnot

" Boolean & Nil
syn keyword cureBoolean true false nil

" Builtin Types & Standard Library
syn keyword cureType Int Float String Atom Bool List Map Tuple Result Option Effect Unit Pid Reference Port

" Builtin Constructors
syn keyword cureConstructor Ok Error Some None True False

" Strings & Interpolation
syn region cureString start='"' skip='\\"' end='"' contains=cureInterpolation,@Spell
syn region cureInterpolation matchgroup=cureInterpolationDelimiter start="#{" end="}" contained contains=TOP

" Atoms
syn match cureAtom ":[a-zA-Z_][a-zA-Z0-9_]*"
syn match cureAtom ':"[^"]*"'

" Numbers
syn match cureNumber "\<0x[0-9a-fA-F_]\+\>"
syn match cureNumber "\<0b[01_]\+\>"
syn match cureNumber "\<[0-9][0-9_]*\(\.[0-9][0-9_]*\)\?\>"

" Operators & Special Punctuation
syn match cureArrow "->"
syn match cureFatArrow "=>"
syn match cureMelquiades "<-|"
syn match cureMelquiades "✉"
syn match cureOperator "[:=|&\-+*/%<>!^~]\+"

" Highlight Links
hi def link cureComment Comment
hi def link cureBlockComment Comment
hi def link cureModule Structure
hi def link cureOtpKeyword Macro
hi def link cureKeyword Keyword
hi def link cureQuantity StorageClass
hi def link cureConditional Conditional
hi def link cureOperatorWords Operator
hi def link cureBoolean Boolean
hi def link cureType Type
hi def link cureConstructor Constant
hi def link cureString String
hi def link cureInterpolationDelimiter PreProc
hi def link cureAtom Identifier
hi def link cureNumber Number
hi def link cureArrow Operator
hi def link cureFatArrow Operator
hi def link cureMelquiades Special
hi def link cureOperator Operator

let b:current_syntax = "cure"
