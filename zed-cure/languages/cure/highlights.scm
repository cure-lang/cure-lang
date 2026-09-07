; Highlights for Cure in Zed

(comment) @comment
(line_comment) @comment
(block_comment) @comment

"mod" @keyword
"use" @keyword
"as" @keyword
"type" @keyword
"typealias" @keyword
"opaque" @keyword
"primitive" @keyword
"indexed" @keyword
"indices" @keyword
"rec" @keyword
"proto" @keyword
"impl" @keyword
"local" @keyword
"interface" @keyword
"implementation" @keyword
"deriving" @keyword

"fn" @keyword
"let" @keyword
"extern" @keyword
"proof" @keyword
"unsafe" @keyword
"quote" @keyword

"erased" @storageclass
"linear" @storageclass
"affine" @storageclass

"match" @keyword.control
"pickup" @keyword.control
"if" @keyword.control
"elif" @keyword.control
"else" @keyword.control
"then" @keyword.control
"for" @keyword.control
"do" @keyword.control
"end" @keyword.control
"in" @keyword.control
"try" @keyword.control
"catch" @keyword.control
"finally" @keyword.control
"throw" @keyword.control
"return" @keyword.control
"yield" @keyword.control
"spawn" @keyword.control
"send" @keyword.control
"receive" @keyword.control
"after" @keyword.control
"when" @keyword.control
"where" @keyword.control

"actor" @keyword.special
"sup" @keyword.special
"app" @keyword.special
"fsm" @keyword.special
"state" @keyword.special
"event" @keyword.special
"transition" @keyword.special
"on_transition" @keyword.special
"on_enter" @keyword.special
"on_exit" @keyword.special
"on_failure" @keyword.special
"on_timer" @keyword.special

"true" @boolean
"false" @boolean
"nil" @constant.builtin

[
  "Int"
  "Float"
  "String"
  "Atom"
  "Bool"
  "List"
  "Map"
  "Tuple"
  "Result"
  "Option"
  "Effect"
  "Unit"
  "Pid"
  "Reference"
  "Port"
] @type.builtin

[
  "Ok"
  "Error"
  "Some"
  "None"
  "True"
  "False"
] @constructor

(string_literal) @string
(atom_literal) @string.special.symbol
(number_literal) @number

[
  "->"
  "=>"
  "<-|"
  "✉"
  "="
  "=="
  "!="
  "+"
  "-"
  "*"
  "/"
  "|"
  ":"
  "::"
] @operator
