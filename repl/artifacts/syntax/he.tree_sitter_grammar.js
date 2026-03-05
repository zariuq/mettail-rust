module.exports = grammar({
  name: 'metta_he',
  extras: $ => [/\s/, $.comment],
  rules: {
    source_file: $ => repeat($._top),
    _top: $ => choice($.eval_form, $.atom),
    eval_form: $ => seq('!', $.atom),
    atom: $ => choice($.list, $.variable, $.string, $.symbol),
    list: $ => seq('(', repeat($.atom), ')'),
    variable: $ => /\$[^\s()";]+/,
    string: $ => /"([^"\\]|\\.)*"/,
    symbol: $ => /[^\s()";]+/,
    comment: $ => token(seq(';', /.*/)),
  }
});
