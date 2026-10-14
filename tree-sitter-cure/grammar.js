/**
 * Tree-sitter grammar for Cure (https://github.com/cure-lang/cure-lang).
 *
 * This is a deliberately *lexical* grammar: it recognises Cure's tokens
 * (keywords, identifiers, literals, comments, operators, FSM transitions)
 * plus a handful of declaration heads, but it does not model Cure's
 * indentation-structured block grammar. That keeps it robust against the
 * evolving surface syntax while giving editors accurate highlighting and a
 * declaration outline.
 *
 * Token rules mirror `Cure.Compiler.Lexer` (lib/cure/compiler/lexer.ex).
 */

const { KEYWORDS, CONTAINERS } = require('./keywords');

module.exports = grammar({
  name: 'cure',

  word: $ => $.identifier,

  // Newlines are tokens, not extras: macro vocabulary (`syntax`, `accepts`,
  // `expands with`, family fields) is only meaningful at the start of a line,
  // and the highlight queries need to see line boundaries to tell it apart
  // from ordinary identifiers.
  extras: $ => [/[ \t\r\f]/],

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice($._token, $.brace_group, $.paren_group, $.bracket_group),

    // Everything except bare brackets. Brackets are grouped so editors can
    // pair them, and so an interpolation's closing `}` is never mistaken for
    // one inside it.
    _token: $ => choice(
      $.module_declaration,
      $.function_declaration,
      $.type_declaration,
      $.container_declaration,
      $.macro_declaration,
      $.decorator,
      alias('@', $.operator),
      $.transition,
      $.transition_arrow,
      $._regex_start,
      $.boolean,
      $.nil,
      $.identifier,
      $.type_identifier,
      $.quoted_identifier,
      $.hole,
      $.atom,
      $.number,
      $.string,
      $.char,
      $.comment,
      $.doc_comment,
      $.operator,
      $.newline,
      ...CONTAINERS.map(word => alias(word, $.identifier)),
      alias('macro', $.identifier),
    ),

    brace_group: $ => seq(choice('{', '%{'), optional($.regex), repeat($._item), '}'),

    // `(...)` and quasiquote splices `$(...)`.
    paren_group: $ => seq(choice('(', '$('), optional($.regex), repeat($._item), ')'),

    // `[...]` and tuples `%[...]`.
    bracket_group: $ => seq(choice('[', '%['), optional($.regex), repeat($._item), ']'),

    // The lexer reads `/` as a regex delimiter only where an expression can
    // begin (`regex_literal_start?`), and as division everywhere else. Here
    // a regex is only valid right after those tokens (or an opening
    // bracket, above), so `a / b / c` stays two divisions. A keyword is
    // never followed by division, so any keyword may precede one.
    _regex_start: $ => prec.right(seq(
      choice(
        $.keyword,
        alias(choice('=', '->', '=>', ':', '|', '|>'), $.operator),
        $.punctuation,
      ),
      optional($.regex),
    )),

    // -- Declaration heads --------------------------------------------------

    module_declaration: $ => prec(1, seq('mod', field('name', $.module_name))),

    module_name: $ => seq($.type_identifier, repeat(seq(token.immediate('.'), alias(token.immediate(/[A-Z][a-zA-Z0-9_]*/), $.type_identifier)))),

    function_declaration: $ => prec(1, seq(
      'fn',
      field('name', choice($.identifier, $.quoted_identifier)),
    )),

    type_declaration: $ => prec(1, seq(
      field('kind', alias(choice('type', 'typealias', 'rec', 'interface', 'implementation', 'proto', 'impl'), $.keyword)),
      field('name', $.type_identifier),
    )),

    container_declaration: $ => prec(1, seq(
      field('kind', alias(choice(...CONTAINERS), $.keyword)),
      field('name', $.module_name),
    )),

    // `macro Twice`, `macro app <name: ModuleName>`; the name may be a
    // container word, since containers are themselves stdlib macros.
    macro_declaration: $ => prec(1, seq(
      field('kind', alias('macro', $.keyword)),
      field('name', choice(
        $.module_name,
        $.identifier,
        ...CONTAINERS.map(word => alias(word, $.identifier)),
      )),
    )),

    // `@extern(...)`, `@derive ...`. A bare `@` (as-pattern `w@S(m)`) falls
    // back to an operator.
    decorator: $ => prec(1, seq('@', field('name', choice($.identifier, alias('extern', $.identifier))))),

    // `Locked --coin--> Unlocked`, `Red --Timer--> Green`,
    // `Created --LockFunds(amount: Int)--> Reserved`. A payload signature sits
    // between the event and `-->`. Event suffixes: `coin?` lexes as one
    // identifier, while `!` is never part of an identifier, so `coin!-->`
    // ends in a `!-->` arrow.
    transition: $ => seq('--', field('event', choice($.identifier, $.type_identifier))),

    transition_arrow: _ => choice('-->', '!-->'),

    newline: _ => /\n/,

    keyword: _ => choice(...KEYWORDS),

    boolean: _ => choice('true', 'false'),

    nil: _ => 'nil',

    // -- Identifiers -------------------------------------------------------

    // A trailing `?` is a predicate suffix (`even?`); `!` is never part of an
    // identifier, so `a!=b` is `a`, `!=`, `b`.
    identifier: _ => /[a-z_][a-zA-Z0-9_$]*\??/,

    type_identifier: _ => /[A-Z][a-zA-Z0-9_]*/,

    quoted_identifier: _ => /`[^`\n]*`/,

    hole: _ => /\?[a-zA-Z_][a-zA-Z0-9_]*/,

    // -- Literals ------------------------------------------------------------

    atom: _ => token(seq(':', /[a-zA-Z_][a-zA-Z0-9_]*[?!]?/)),

    number: _ => token(choice(
      /0[xX][0-9a-fA-F_]+/,
      /0[bB][01_]+/,
      /0[oO][0-7_]+/,
      /[0-9][0-9_]*(\.[0-9][0-9_]*)?([eE][+-]?[0-9]+)?/,
    )),

    string: $ => seq(
      '"',
      repeat(choice(
        $.string_content,
        $.escape_sequence,
        $.interpolation,
      )),
      token.immediate('"'),
    ),

    string_content: _ => token.immediate(/[^"\\#]+|#/),

    escape_sequence: _ => token.immediate(/\\./),

    interpolation: $ => seq(
      token.immediate('#{'),
      repeat($._item),
      '}',
    ),

    char: _ => token(choice(
      "'''",
      /'[^'\\\n]'/,
      /'\\.[^'\n]*'/,
    )),

    // `/^[A-Z]\w+$/i`; the modifiers are the lexer's `regex_flag?/1`.
    regex: _ => token(seq('/', repeat(choice(/[^\/\\\n]/, /\\./)), '/', /[imsxufrUE]*/)),

    // -- Comments ------------------------------------------------------------

    comment: _ => token(prec(-1, /#[^\n]*/)),

    // `## line`, and the fenced form: `###` plus the rest of its line opens
    // the fence, which closes at the next line whose first non-space
    // characters are `###` (or at end of file). A `###` elsewhere in a line
    // does not close it.
    doc_comment: _ => token(choice(
      prec(1, /##[^\n]*/),
      prec(2, /###[^\n]*(\n *([^ #\n][^\n]*|#([^#\n][^\n]*)?|##([^#\n][^\n]*)?)?)*(\n *###[^\n]*)?/),
    )),

    // -- Operators and punctuation ------------------------------------------

    operator: _ => token(choice(
      /[+\-*\/=<>!|&^~\\]+/,
      '..', '..=', '::', '.', '%', '$', '?', '✉',
    )),

    punctuation: _ => choice(',', ';'),
  },
});
