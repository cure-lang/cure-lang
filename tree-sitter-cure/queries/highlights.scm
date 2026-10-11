; Highlights for Cure. Generic captures come first; later, more specific
; patterns override them.

(identifier) @variable
(quoted_identifier) @variable
(type_identifier) @type
(keyword) @keyword

; Calls: `name(...)`
((identifier) @function.call
  .
  (paren_group))

; Well-known constructors
((type_identifier) @constructor
  (#any-of? @constructor "Ok" "Error" "Some" "None" "True" "False" "Z" "S"))

; Declarations
(module_declaration "mod" @keyword)
(module_declaration name: (module_name (type_identifier) @title))
(function_declaration name: (_) @function)
(function_declaration "fn" @keyword.function)
(type_declaration name: (type_identifier) @type)
(container_declaration name: (module_name (type_identifier) @title))
(container_declaration kind: (keyword) @keyword.special)
(macro_declaration kind: (keyword) @keyword.special)
(macro_declaration name: (module_name (type_identifier) @title))
(macro_declaration name: (identifier) @title)

; -- Macro vocabulary --------------------------------------------------------
; These words are identifiers to the Cure lexer; they only mean something at
; the start of a macro entry, so most patterns anchor on a preceding newline.

; Required family field / container use site: `root ModuleName`, `table Books`
((newline)
  .
  (identifier) @property
  .
  (type_identifier)
  .
  (newline))

; Field after a cardinality: `optional label Expression`
((identifier) @_cardinality
  .
  (identifier) @property
  (#any-of? @_cardinality "optional" "repeated" "one_or_more"))

; Rule dispatch keyword: `syntax twice <n: Code> ...`, `example twice 21 ...`
((newline)
  .
  (identifier) @_head
  .
  (identifier) @function.macro
  (#any-of? @_head "syntax" "example" "literal"))

; Lifecycle callbacks in container bodies: `on_start`, `on_transition`, ...
((newline)
  .
  (identifier) @keyword.special
  (#match? @keyword.special "^on_[a-z_]+$"))

; Entry heads
((newline)
  .
  (identifier) @keyword
  (#any-of? @keyword
    "syntax" "accepts" "expands" "literal" "example" "explain" "fail" "open"
    "includes" "optional" "repeated" "one_or_more" "keyword"))

; Two-word heads: `syntax family`, `expands with`, `computed by`
((identifier) @_first
  .
  (identifier) @keyword
  (#eq? @_first "syntax")
  (#eq? @keyword "family"))
((identifier) @_first
  .
  (identifier) @keyword
  (#eq? @_first "expands")
  (#eq? @keyword "with"))
((identifier) @keyword
  .
  (identifier) @_by
  (#eq? @keyword "computed")
  (#eq? @_by "by"))
((identifier) @_first
  .
  (identifier) @keyword
  (#eq? @_first "computed")
  (#eq? @keyword "by"))
; `computed directly by`
((identifier) @keyword
  .
  (identifier) @_directly
  (#eq? @keyword "computed")
  (#eq? @_directly "directly"))
((identifier) @_first
  .
  (identifier) @keyword
  (#any-of? @_first "computed" "directly")
  (#any-of? @keyword "directly" "by"))

; Expander functions: `expands with derive_table`, `computed by expand_quad`
((identifier) @_link
  .
  (identifier) @function
  (#any-of? @_link "with" "by"))

; Mid-line rule keywords: `... becomes n + n`, `... contextual`,
; `example twice 21 expands 21 + 21`
((identifier) @keyword
  (#any-of? @keyword "becomes" "contextual" "expands"))

; Contextual keywords are identifiers lexically (`let prefix = ...` is an
; ordinary binder), so each one is matched only in the position that makes it
; a keyword.

; `have step = lemma(...)`
((newline)
  .
  (identifier) @keyword
  .
  (identifier)
  (#eq? @keyword "have"))

; `fn f(...) -> Bool requires Equatable(t) = ...`
((identifier) @keyword
  .
  (type_identifier)
  (#eq? @keyword "requires"))

; `precedencegroup Pipe`
((newline)
  .
  (identifier) @keyword
  .
  (type_identifier)
  (#eq? @keyword "precedencegroup"))

; `infix `|>` ...`, `prefix ...`, `postfix ...`
((newline)
  .
  (identifier) @keyword
  .
  (quoted_identifier)
  (#any-of? @keyword "infix" "prefix" "postfix"))

; `proof chain` blocks and their `because ...` justifications
((newline)
  .
  (identifier) @keyword
  .
  (identifier) @_chain
  (#eq? @keyword "proof")
  (#eq? @_chain "chain"))
((identifier) @_proof
  .
  (identifier) @keyword
  (#eq? @_proof "proof")
  (#eq? @keyword "chain"))
((newline)
  .
  (identifier) @keyword
  (#eq? @keyword "because"))

; Category after a hole: `<x: Code> is Statement`
((operator) @_close
  .
  (identifier) @keyword
  (#eq? @_close ">")
  (#eq? @keyword "is"))

; Holes in rules and macro names: `<name: ModuleName>`
((operator) @_open
  .
  (identifier) @variable.parameter
  .
  (operator) @_colon
  (#eq? @_open "<")
  (#eq? @_colon ":"))

(decorator "@" @attribute)
(decorator name: (identifier) @attribute)

; FSM transitions: `Locked --coin--> Unlocked`
(transition "--" @operator)
(transition event: (_) @label)
(transition_arrow) @operator

(boolean) @boolean
(nil) @constant.builtin
(hole) @variable.special

(atom) @string.special.symbol
(number) @number
(char) @string.special
(regex) @string.regex
(string) @string
(escape_sequence) @string.escape
(interpolation
  "#{" @punctuation.special
  "}" @punctuation.special) @embedded

(comment) @comment
(doc_comment) @comment.doc

(operator) @operator
((operator) @operator.special
  (#any-of? @operator.special "<-|" "✉" "|>"))

(punctuation) @punctuation.delimiter
(paren_group ["(" "$(" ")"] @punctuation.bracket)
(bracket_group ["[" "%[" "]"] @punctuation.bracket)
(brace_group ["{" "%{" "}"] @punctuation.bracket)
