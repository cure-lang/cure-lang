/*
Language: Cure
Author: Aleksei Matiushkin <matiouchkine@gmail.com>
Description: A dependently-typed functional language for the BEAM VM with
             first-class finite state machines, typed supervision trees,
             OTP applications, SMT-backed verification, and propositional
             equality. Indentation-significant, ML-influenced syntax with
             Erlang-style bitstring segments and FSM transition literals.
Website: https://cure-lang.org
Category: functional
*/

/** @type LanguageFn */
export default function(hljs) {
  // --------------------------------------------------------------------------
  // Keywords
  //
  // Mirrors the buckets used by `Makeup.Lexers.CureLexer` so the two
  // highlighters agree on what is syntactic vs. user code. The trailing
  // `?` / `!` are part of an identifier in Cure, so the `$pattern` below
  // needs to accept them -- `is_empty?` and `stop!` tokenise as whole
  // words, and we must not accidentally match `if?` as `if`.
  // --------------------------------------------------------------------------

  const DECLARATION_KEYWORDS = [
    'mod', 'fn', 'type', 'proto', 'impl', 'fsm', 'let', 'rec',
    'local', 'use', 'as', 'extern',
    'actor', 'sup', 'app', 'proof'
  ];

  const CONTROL_KEYWORDS = [
    'if', 'elif', 'else', 'then',
    'match', 'when', 'where',
    'for', 'do', 'in', 'end',
    'try', 'catch', 'finally', 'throw',
    'return', 'yield',
    'assert_type', 'rewrite', 'with'
  ];

  const CONCURRENCY_KEYWORDS = [
    'spawn', 'send', 'receive', 'after'
  ];

  const FSM_CALLBACK_KEYWORDS = [
    'on_start', 'on_stop', 'on_transition',
    'on_enter', 'on_exit', 'on_failure',
    'on_timer', 'on_message', 'on_phase'
  ];

  const WORD_OPERATORS = ['and', 'or', 'not'];

  const LITERALS = ['true', 'false', 'nil'];

  // Identifiers are `\w+` optionally followed by a single `?` or `!`.
  // Using `$pattern` with the suffix means `if?` and `mod!` lex as a
  // single word and never match the bare keywords.
  const IDENT_PATTERN = /[A-Za-z_][A-Za-z0-9_]*[?!]?/;

  const KEYWORDS = {
    $pattern: IDENT_PATTERN,
    keyword: [].concat(
      DECLARATION_KEYWORDS,
      CONTROL_KEYWORDS,
      CONCURRENCY_KEYWORDS,
      FSM_CALLBACK_KEYWORDS,
      WORD_OPERATORS
    ),
    literal: LITERALS,
    // Common BEAM/Cure primitive types. Bumped relevance -- seeing
    // `Bitstring` or `Atom` is a strong hint that we're looking at Cure.
    built_in: [
      'Int', 'Float', 'Bool', 'String', 'Atom', 'Bitstring',
      'Binary', 'Char', 'Any', 'Unit', 'Void',
      'List', 'Map', 'Tuple', 'Option', 'Result', 'Pid', 'Ref'
    ]
  };

  // --------------------------------------------------------------------------
  // Comments
  //
  // Order matters at the caller: fenced `### ... ###` must be tried before
  // `##` line doc-comments, which must be tried before plain `#`.
  // --------------------------------------------------------------------------

  // No `self` in contains: `### ... ###` does NOT nest. Without this,
  // the first inner `###` would re-open the mode rather than close the
  // outer one, swallowing the rest of the file.
  const FENCED_DOC_COMMENT = {
    scope: 'comment',
    begin: /###/,
    end: /###/,
    contains: [
      {
        scope: 'doctag',
        match: /@\w+/
      },
      hljs.PHRASAL_WORDS_MODE
    ],
    relevance: 10
  };

  const LINE_DOC_COMMENT = hljs.COMMENT(
    /##(?!#)/,
    /$/,
    {
      scope: 'comment',
      contains: [
        {
          scope: 'doctag',
          match: /@\w+/
        },
        hljs.PHRASAL_WORDS_MODE
      ],
      relevance: 0
    }
  );

  const LINE_COMMENT = hljs.COMMENT(
    /#(?!#)/,
    /$/,
    { relevance: 0 }
  );

  const COMMENTS = [FENCED_DOC_COMMENT, LINE_DOC_COMMENT, LINE_COMMENT];

  // --------------------------------------------------------------------------
  // Numbers
  //
  // Cure allows `_` as a digit separator in every base.
  // --------------------------------------------------------------------------

  const NUMBER = {
    scope: 'number',
    variants: [
      { match: /\b0b[01][01_]*\b/ },                                // binary
      { match: /\b0x[0-9a-fA-F][0-9a-fA-F_]*\b/ },                  // hex
      { match: /\b\d[\d_]*\.\d[\d_]*(?:[eE][+-]?\d[\d_]*)?\b/ },    // float
      { match: /\b\d[\d_]*\b/ }                                     // int
    ],
    relevance: 0
  };

  // --------------------------------------------------------------------------
  // Strings, char literals, regexes
  // --------------------------------------------------------------------------

  const ESCAPE = {
    scope: 'char.escape',
    variants: [
      { match: /\\u[0-9a-fA-F]{4}/ },
      { match: /\\./ }
    ]
  };

  // `#{ ... }` interpolation. The inner content is parsed in the same
  // root language context (so you get keywords, numbers, nested strings,
  // etc. inside an interpolation, just like the makeup lexer does).
  const SUBST = {
    scope: 'subst',
    begin: /#\{/,
    end: /\}/,
    keywords: KEYWORDS
  };

  const STRING = {
    scope: 'string',
    begin: /"/,
    end: /"/,
    illegal: /\n/,
    contains: [ESCAPE, SUBST]
  };

  // Char literals: both the `'c'` form and the `?\n` form that mirrors
  // Erlang's character syntax.
  const CHAR_LITERAL = {
    scope: 'string',
    variants: [
      { match: /\?\\[a-zA-Z0-9]/ },
      { match: /'(?:\\.|[^'\\])'/ }
    ],
    relevance: 0
  };

  const REGEX = {
    scope: 'regexp',
    begin: /~r\//,
    end: /\/[a-z]*/,
    contains: [ESCAPE],
    relevance: 10
  };

  // --------------------------------------------------------------------------
  // Atoms, typed holes, attributes
  // --------------------------------------------------------------------------

  const ATOM = {
    scope: 'symbol',
    match: /:[A-Za-z_][A-Za-z0-9_]*[?!]?/,
    relevance: 0
  };

  // Typed holes -- `?_` anonymous, `?name` named. Distinct scope so
  // editors can colour them differently from ordinary identifiers.
  const HOLE = {
    scope: 'variable.constant',
    match: /\?[A-Za-z_][A-Za-z0-9_]*/,
    relevance: 10
  };

  const ATTRIBUTE = {
    scope: 'meta',
    match: /@[A-Za-z_][A-Za-z0-9_]*/
  };

  // --------------------------------------------------------------------------
  // Module / type names
  //
  // `Foo`, `Foo.Bar`, `Std.String` -- uppercase-led dotted identifiers.
  // Also catches unary sum-type constructors (`Some`, `None`, `Red`).
  // --------------------------------------------------------------------------

  const MODULE_OR_TYPE = {
    scope: 'title.class',
    match: /\b[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*\b/,
    relevance: 0
  };

  // --------------------------------------------------------------------------
  // Function declarations
  //
  // `fn name(...)` or `fn name` -- the head name highlights as a function.
  // Placed as a mode (rather than a flat match) so the `fn` token itself
  // keeps its keyword scope from the root `keywords` bucket.
  // --------------------------------------------------------------------------

  const FUNCTION_DECL = {
    scope: 'function',
    beginKeywords: 'fn',
    end: /[(=\n]/,
    excludeEnd: true,
    contains: [
      {
        scope: 'title.function',
        match: /[a-z_][A-Za-z0-9_]*[?!]?/
      }
    ]
  };

  // --------------------------------------------------------------------------
  // FSM transition literal: `--event-->`
  //
  // Event names follow the identifier rules (including a trailing `?`/`!`
  // for soft / hard events). We match the full literal as a single token
  // so the arrow and the event name get highlighted consistently.
  // --------------------------------------------------------------------------

  const FSM_TRANSITION = {
    scope: 'operator',
    match: /--[A-Za-z_][A-Za-z0-9_]*[?!]?-->/,
    relevance: 10
  };

  // --------------------------------------------------------------------------
  // Predicate / effect identifiers
  //
  // `is_empty?`, `stop!`, `mod!` are single tokens in Cure. Without this
  // rule the operator mode below would peel the trailing `?` or `!` off
  // into an operator, leaving the leading identifier free to match the
  // keyword list (so `mod!()` would show `mod` highlighted as a keyword
  // and `!` as an operator, which is wrong). We consume the whole
  // identifier as a single plain-text match with no scope so keyword
  // lookup never fires on it.
  // --------------------------------------------------------------------------

  const PREDICATE_OR_EFFECT_IDENT = {
    match: /[a-z_][A-Za-z0-9_]*[?!]/
  };

  // --------------------------------------------------------------------------
  // Operators
  //
  // Multi-char operators listed longest-first. The Melquiades send
  // operator has two surface forms: ASCII `<-|` and the envelope glyph
  // U+2709 (`✉`). Both are given a small relevance bump so a code
  // fragment using either is a strong signal of Cure.
  // --------------------------------------------------------------------------

  const OPERATOR = {
    scope: 'operator',
    variants: [
      { match: /<-\|/, relevance: 10 },
      { match: /\u2709/, relevance: 10 },                           // ✉
      { match: /-->|<-|<>|\|>|->|=>|\.\.=|\.\.|==|!=|<=|>=|\+\+|--|\*\*|::|\+=|-=|\*=|\/=/ },
      { match: /[+\-*/%=<>|^!&]/ }
    ],
    relevance: 0
  };

  // --------------------------------------------------------------------------
  // Root
  // --------------------------------------------------------------------------

  return {
    name: 'Cure',
    aliases: ['cure'],
    keywords: KEYWORDS,
    contains: [
      // Comments first so `#{` inside strings isn't mistaken for a comment.
      ...COMMENTS,
      STRING,
      CHAR_LITERAL,
      REGEX,
      ATOM,
      HOLE,
      ATTRIBUTE,
      FSM_TRANSITION,
      FUNCTION_DECL,
      // Must come before MODULE_OR_TYPE (harmless, since predicates are
      // lowercase-led) and before OPERATOR (so `!`/`?` don't split off).
      PREDICATE_OR_EFFECT_IDENT,
      MODULE_OR_TYPE,
      NUMBER,
      OPERATOR,
      // Tuple / map opener punctuation -- purely cosmetic so the `%`
      // doesn't get picked up as a lone modulo operator.
      { match: /%\[|%\{/, scope: 'punctuation' }
    ]
  };
}
