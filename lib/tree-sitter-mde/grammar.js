/**
 * Tree-sitter Grammar for MDE/Celf-style syntax (Extended)
 *
 * This grammar parses:
 * - Type declarations: name: type.
 * - Constructors: name: T1 -> T2 -> ... -> Tn.
 * - Clauses: name/case: head <- premise1 <- premise2.
 * - Forward rules: antecedent -o { consequent }.
 * - @annotations for extended Celf (.calc files)
 *
 * Annotation syntax:
 *   @key value
 *   @key "string value"
 *   @key 60 left        (precedence with associativity)
 */

module.exports = grammar({
  name: 'mde',

  // Whitespace and comments
  extras: $ => [
    /\s/,
    $.comment,
  ],

  // Word boundaries for keywords
  word: $ => $.identifier,

  rules: {
    // Program is a list of declarations, directives, and query directives
    source_file: $ => repeat(choice($.declaration, $.directive, $.query_directive)),

    // Query directive: #kind body.
    // Used for: #symex, #trace
    query_directive: $ => seq(
      '#',
      field('kind', $.identifier),
      field('body', $.expr),
      '.'
    ),

    // Unified declaration: name: body @annotations? .
    // Both type declarations and clauses share this structure
    declaration: $ => seq(
      field('name', $.decl_name),
      ':',
      field('body', $.decl_body),
      field('annotations', optional($.annotation_block)),
      '.'
    ),

    // Standalone directive: @name args... .
    // Used for: @family, @extends, @metavar, @schema
    directive: $ => seq(
      '@',
      field('name', $.identifier),
      field('args', repeat($.directive_arg)),
      '.'
    ),

    // Directive argument: identifier, string, or key="value"
    directive_arg: $ => choice(
      $.key_value_pair,
      $.string_literal,
      $.identifier,
      $.variable,
      $.number
    ),

    // Key-value pair: key="value" or key=identifier
    key_value_pair: $ => seq(
      field('key', $.identifier),
      '=',
      field('value', choice($.string_literal, $.identifier, $.number))
    ),

    // Declaration name: (ident|var) (/ (ident | var | number))*
    // Note: Celf allows uppercase identifiers for type/constant names
    decl_name: $ => seq(
      choice($.identifier, $.variable),
      repeat(seq('/', choice($.identifier, $.variable, /\d+/)))
    ),

    // Declaration body: expr with optional premises
    decl_body: $ => seq(
      field('expr', $.expr),
      field('premises', optional($.back_chain))
    ),

    // Annotation block: one or more @key value annotations
    annotation_block: $ => repeat1($.annotation),

    // Single annotation: @key value?
    annotation: $ => seq(
      '@',
      field('key', $.identifier),
      field('value', optional($.annotation_value))
    ),

    // Annotation value variants
    annotation_value: $ => choice(
      $.string_literal,
      $.prec_value,      // number with optional associativity
      $.identifier,
      $.bool_literal,
    ),

    // Precedence: number with optional associativity (left/right/none)
    prec_value: $ => seq(
      $.number,
      optional($.associativity)
    ),

    associativity: $ => choice('left', 'right', 'none'),

    // String literal: "..."
    string_literal: $ => seq(
      '"',
      /[^"]*/,
      '"'
    ),

    // Boolean literal
    bool_literal: $ => choice('true', 'false'),

    // Number (integer: decimal or 0x hex)
    number: $ => /\d+|0x[0-9a-fA-F]+/,

    // Backward chaining: <- expr <- expr ...
    back_chain: $ => repeat1(seq('<-', $.expr)),

    // Unified expression (covers both types and terms)
    expr: $ => choice(
      // Arrow (type signature) - right associative
      prec.right(1, seq($.expr_plus, '->', $.expr)),
      // Forward rule: A -o { B }
      prec.right(1, seq($.expr_plus, '-o', '{', $.expr, '}')),
      // Linear implication: A -o B
      prec.right(1, seq($.expr_plus, '-o', $.expr)),
      // Quantifiers: exists X. body / forall X. body
      prec.right(1, seq('exists', $.variable, '.', $.expr)),
      prec.right(1, seq('forall', $.variable, '.', $.expr)),
      $.expr_plus,
    ),

    // Plus (additive disjunction, left-associative): A + B
    expr_plus: $ => choice(
      prec.left(2, seq($.expr_plus, '+', $.expr_with)),
      $.expr_with,
    ),

    // With (additive conjunction, left-associative): A & B
    expr_with: $ => choice(
      prec.left(3, seq($.expr_with, '&', $.expr_tensor)),
      $.expr_tensor,
    ),

    // Tensor (left-associative): A * B * C
    // Note: Trailing * (affine marker) is handled in convert.js
    expr_tensor: $ => choice(
      prec.left(4, seq($.expr_tensor, '*', $.expr_bang)),
      $.expr_bang,
    ),

    // Bang (prefix): !A
    expr_bang: $ => choice(
      seq('!', $.expr_bang),
      $.expr_app,
    ),

    // Application (left-associative): f x y z
    expr_app: $ => choice(
      prec.left(5, seq($.expr_app, $.expr_atom)),
      $.expr_atom,
    ),

    // Atoms
    expr_atom: $ => choice(
      'type',
      $.identifier,
      $.variable,
      $.number,
      seq('(', $.expr, ')'),
    ),

    // Lexical rules
    identifier: $ => /[a-z_][a-zA-Z0-9_']*/,
    variable: $ => /[A-Z][a-zA-Z0-9_']*/,
    comment: $ => token(seq('%', /.*/)),
  }
});
