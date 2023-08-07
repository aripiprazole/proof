use std::fmt::Display;

use chumsky::{error::Error, extra::Err, prelude::*, text::keyword, util::MaybeRef};

use crate::ast::*;

/// The token type used by the lexer.
#[derive(Debug, PartialEq, Clone)]
pub enum Token<'src> {
    Let,
    Data,
    In,
    Fun,
    Where,
    Identifier(&'src str),
    String(&'src str),
    Constructor(&'src str),
    Number(isize),
    Ctrl(char),
}

impl<'src> Display for Token<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Let => write!(f, "let"),
            Token::Data => write!(f, "data"),
            Token::In => write!(f, "in"),
            Token::Fun => write!(f, "fun"),
            Token::Where => write!(f, "where"),
            Token::Identifier(id) => write!(f, "{id}"),
            Token::String(str) => write!(f, "\"{str}\""),
            Token::Constructor(cons) => write!(f, "{cons}"),
            Token::Number(num) => write!(f, "{num}"),
            Token::Ctrl(ctrl) => write!(f, "{ctrl}"),
        }
    }
}

pub type LexerError<'src> = Err<Rich<'src, char, SimpleSpan>>;

pub type ParserInput<'tokens, 'src> =
    chumsky::input::SpannedInput<Token<'src>, Span, &'tokens [(Token<'src>, Span)]>;

pub type Span = SimpleSpan;

/// Parse a string into a set of tokens.
///
/// This function is a wrapper around the lexer and parser, and is the main entry point
/// for the calculator.
pub fn lexer<'src>() -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, LexerError<'src>> {
    let num = text::int(10)
        .try_map(|int, span| {
            // int: &str, decimal: Option<(char, &str)>
            // define the types of the variables, because the chumsky
            // parser tries to infer it
            let int: &str = int;

            let Ok(int) = int.parse::<isize>() else {
                return Err(Rich::custom(span, "invalid integer"));
            };

            Ok(Token::Number(int))
        })
        .labelled("number");

    let op = one_of("+*-/!^&<>=")
        .repeated()
        .at_least(1)
        .map_slice(Token::Identifier)
        .labelled("operator");

    // An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
    // characters or underscores. The regex pattern for it is `[A-Z][a-zA-Z0-9_'.]*`.
    let cons = any()
        // Use try_map over filter to get a better error on failure
        .try_map(|c: char, span| {
            if c.is_ascii_alphabetic() && c.is_uppercase() {
                Ok(c)
            } else {
                Err(Error::<&str>::expected_found(
                    [],
                    Some(MaybeRef::Val(c)),
                    span,
                ))
            }
        })
        .then(
            // This error never appears due to `repeated` so can use `filter`
            any()
                .filter(|c: &char| {
                    c.is_ascii_alphanumeric() || *c == '_' || *c == '\'' || *c == '.'
                })
                .repeated(),
        )
        .slice()
        .map(Token::Constructor);

    // An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
    // characters or underscores. The regex pattern for it is `[a-zA-Z_'.][a-zA-Z0-9_'.]*`.
    let id = any()
        // Use try_map over filter to get a better error on failure
        .try_map(|c: char, span| {
            if c.is_ascii_alphabetic() || c == '_' || c == '\'' || c == '.' {
                Ok(c)
            } else {
                Err(Error::<&str>::expected_found(
                    [],
                    Some(MaybeRef::Val(c)),
                    span,
                ))
            }
        })
        .then(
            any()
                // This error never appears due to `repeated` so can use `filter`
                .filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_')
                .repeated(),
        )
        .slice()
        .map(Token::Identifier);

    let ctrl = one_of("()[]{}:\\|,;").map(Token::Ctrl).labelled("ctrl");

    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    num.or(keyword("let").to(Token::Let))
        .or(keyword("data").to(Token::Data))
        .or(keyword("in").to(Token::In))
        .or(keyword("fun").to(Token::Fun))
        .or(keyword("where").to(Token::Where))
        .or(op)
        .or(ctrl)
        .or(cons)
        .or(id)
        .map_with_span(spanned)
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

/// Defines the base parser for the simple math language. It
/// does parse a set of tokens, into a equation.
///
/// The parser is defined as a function, because it is recursive.
///
/// [`recursive`]: https://docs.rs/chumsky/0.1.0/chumsky/recursive/index.html
/// [`Parser`]: https://docs.rs/chumsky/0.1.0/chumsky/prelude/trait.Parser.html
/// [`Term`]: [`Term`]
///
/// NOTE: The parsers uses the [`recursive`] combinator, which is a
/// combinator that allows for recursive parsers, even when it is
/// not needed, because this wraps the types and makes compilation
/// faster.
///
/// Chumsky uses session types to define the input and output of
/// a parser. So if we combine so much parser as this function do
/// we will get a very long type. To make it easier to read, and
/// faster to compile/type check, we use the [`recursive`].
pub fn parser<'tokens, 'src: 'tokens>() -> impl Parser<
    // Input Types
    'tokens,
    ParserInput<'tokens, 'src>,
    ProofFile,
    chumsky::extra::Err<Rich<'tokens, Token<'src>, Span>>,
> {
    let pattern_parser = recursive(move |pattern| {
        let id = select! { Token::Identifier(str) => PatternKind::Variable(str.into()) }
            .map_with_span(spanned)
            .labelled("identifier pattern");

        // A cons pattern is defined as a name but not followed by a list of patterns.
        //
        // It does parses without parenthesis, because it is easier to parse.
        let cons_id = select! { Token::Constructor(str) => str }
            .map(|name: &str| PatternKind::Constructor(name.into(), vec![]))
            .map_with_span(spanned)
            .labelled("constructor identifier pattern");

        // A cons pattern is defined as a name followed by a list of patterns.
        let cons = recursive(|_| {
            just(Token::Ctrl('('))
                .then(select! { Token::Constructor(str) => str })
                .then(pattern.clone().repeated().collect::<Vec<_>>())
                .then_ignore(just(Token::Ctrl(')')))
                .map(|((_, name), patterns)| PatternKind::Constructor(name.into(), patterns))
                .map_with_span(spanned)
                .labelled("constructor pattern")
        });

        id.or(cons).or(cons_id).labelled("pattern").as_context()
    });

    let expr_parser = recursive(|expr| {
        // Defines the parser for the value. It is the base of the
        // expression parser.
        let primary = recursive(|_| {
            // Defines the parser for the value. It is the base of the
            // expression parser.
            let value = select! {
                Token::Number(number) => ExprKind::Number(number),
                Token::Identifier(id) if id != "->" => ExprKind::Hole(id.into()),
                Token::Constructor(id) if id == "Type" => ExprKind::Type(0),
                Token::Constructor(id) => ExprKind::Constructor(id.into()),
                Token::String(str) => ExprKind::String(str.into()),
            }
            .map_with_span(spanned)
            .labelled("value");

            let group = expr
                .clone()
                .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                .labelled("group expression");

            value.or(group).labelled("primary")
        });

        // Defines the parser for the application. It is the second
        // level of the expression parser.
        let app = recursive(|_| {
            primary
                .clone()
                .foldl(primary.clone().repeated(), |acc, next| {
                    let first = acc.span;
                    let end = next.span;

                    Spanned {
                        data: ExprKind::Apply(acc.into(), next.into()),
                        span: (first.start..end.end).into(),
                    }
                })
        });

        // Defines an annotation parser. It does parse a type
        // annotation, which is a value followed by a type.
        let ann = recursive(|_| {
            app.clone()
                .foldl(
                    just(Token::Ctrl(':')).then(expr.clone()).repeated(),
                    |acc, (_, next)| {
                        let first = acc.span;
                        let end = next.span;

                        Spanned {
                            data: ExprKind::Ann(acc.into(), next.into()),
                            span: (first.start..end.end).into(),
                        }
                    },
                )
                .labelled("annotation")
        });

        // Defines a dependent function type parser. It does parse
        // a function type, which is a type followed by a type.
        let pi = recursive(|_| {
            app.clone()
                .map(|type_rep| match type_rep.data {
                    ExprKind::Ann(name, type_rep) => match name.data {
                        ExprKind::Hole(hole) => (hole, type_rep),
                        _ => ("_".into(), type_rep),
                    },
                    _ => ("_".into(), type_rep.into()),
                })
                .then(just(Token::Identifier("->")))
                .then(expr.clone())
                .map(|(((name, parameter), _), value)| ExprKind::Pi(name, parameter, value.into()))
                .map_with_span(spanned)
                .labelled("pi expression")
        });

        // Defines a lambda parser. It does parse a lambda expression,
        // which is a pattern followed by an expression.
        let lambda = recursive(|_| {
            just(Token::Ctrl('\\'))
                .then(pattern_parser.clone())
                .then_ignore(just(Token::Identifier(".")))
                .then(expr.clone())
                .map(|((_, pattern), expr)| ExprKind::Lambda(pattern, expr.into()))
                .map_with_span(spanned)
                .labelled("lambda exprression")
        });

        // Defines a let parser. It does parse a let expression,
        // which is a pattern followed by an expression.
        let let_expr = recursive(|_| {
            just(Token::Let)
                .then(pattern_parser.clone())
                .then_ignore(just(Token::Identifier("=")))
                .then(expr.clone())
                .then_ignore(just(Token::In))
                .then(expr.clone())
                .map(|(((_, pattern), value), expr)| {
                    ExprKind::Let(pattern, value.into(), expr.into())
                })
                .map_with_span(spanned)
                .labelled("let exprression")
                .as_context()
        });

        // Defines the expression parser. It is the top level of the
        // expression parser.
        pi.or(ann)
            .or(lambda)
            .or(let_expr)
            .recover_with(via_parser(nested_delimiters(
                Token::Ctrl('('),
                Token::Ctrl(')'),
                [
                    (Token::Ctrl('['), Token::Ctrl(']')),
                    (Token::Ctrl('{'), Token::Ctrl('}')),
                ],
                |span| Spanned {
                    data: ExprKind::Error,
                    span,
                },
            )))
            .labelled("expression")
            .as_context()
    });

    // Defines the statement parser. It is the top level of the
    // statement parser.
    let stmt_parser = recursive(|_| {
        // Defines a term parser. It does parse a term, which is an
        // expression followed by a semicolon.
        let expr_stmt = recursive(|_| {
            expr_parser
                .clone()
                .then_ignore(just(Token::Ctrl(';')))
                .map(StmtKind::Term)
                .map_with_span(spanned)
                .labelled("expression statement")
        });

        // Defines a maybe infer type representation parser. It does
        // parse a type representation, which is a colon followed by
        // a type representation. If there is no type representation,
        // it will parse a hole.
        let type_rep = recursive(|_| {
            just(Token::Ctrl(':'))
                .then(expr_parser.clone())
                .map(|(_, type_rep)| type_rep)
                .or_not()
                .map(|type_rep| match type_rep {
                    Some(type_rep) => type_rep,
                    None => Spanned {
                        data: ExprKind::Hole("_".into()),
                        span: (0..0).into(),
                    },
                })
        });

        let constructors = recursive(|_| {
            select! { Token::Constructor(str) => str }
                .then(type_rep.clone())
                .map(|(name, type_rep)| DataConstructor {
                    name: name.into(),
                    type_rep,
                })
                .labelled("data constructor")
        });

        let parameter = recursive(|_| {
            pattern_parser
                .clone()
                .then(type_rep.clone())
                .map(|(pattern, type_rep)| Parameter {
                    pattern,
                    type_rep,
                })
        });

        let implicit_parameters = recursive(|_| {
            parameter
                .clone()
                .separated_by(just(Token::Ctrl(',')))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
                .labelled("implicit parameters")
        });

        let explicit_parameters = recursive(|_| {
            parameter
                .clone()
                .separated_by(just(Token::Ctrl(',')))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                .labelled("explicit parameters")
        });

        // Defines a data parser. It does parse a data statement,
        // which is a data keyword followed by a name, a type
        // representation, a where keyword, and a list of data
        // constructors.
        let data_stmt = recursive(|_| {
            just(Token::Data)
                .then(select! { Token::Constructor(str) => str })
                .then(type_rep.clone())
                .then(implicit_parameters.or_not())
                .then(explicit_parameters.or_not())
                .then_ignore(just(Token::Where))
                .then(
                    constructors
                        .separated_by(just(Token::Ctrl(',')))
                        .collect::<Vec<_>>(),
                )
                .map(|(((((_, name), type_rep), implicits), explicits), vec)| {
                    StmtKind::Data(DataStmt {
                        name: name.into(),
                        parameters: Parameters {
                            implicit_parameters: implicits.unwrap_or_default(),
                            explicit_parameters: explicits.unwrap_or_default(),
                        },
                        type_rep,
                        constructors: vec,
                    })
                })
                .map_with_span(spanned)
                .labelled("data statement")
        });

        let clause = recursive(|_| {
            just(Token::Ctrl('|'))
                .then(
                    pattern_parser
                        .clone()
                        .separated_by(just(Token::Ctrl(',')))
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Token::Identifier("=")))
                .then(expr_parser.clone())
                .map(|((_, patterns), term)| Clause {
                    patterns,
                    term,
                })
                .labelled("clause")
                .as_context()
        });

        // Defines a fun parser. It does parse a fun statement, which
        // is a fun keyword followed by a name, a type representation,
        // a list of clauses, and a semicolon.
        let fun_stmt = recursive(|_| {
            just(Token::Fun)
                .then(select! { Token::Identifier(str) => str })
                .then(type_rep.clone())
                .then(clause.repeated().collect::<Vec<_>>().or_not())
                .then_ignore(just(Token::Ctrl(';')))
                .map(|(((_, name), type_rep), clauses)| {
                    let clauses: Vec<_> = clauses.unwrap_or_default();

                    StmtKind::Fun(FunStmt {
                        name: name.into(),
                        type_rep,
                        clauses,
                    })
                })
                .map_with_span(spanned)
        });

        data_stmt
            .or(fun_stmt)
            .or(expr_stmt)
            .labelled("statement")
            .recover_with(skip_then_retry_until(
                any().ignored(),
                one_of([Token::Ctrl(';'), Token::Fun, Token::Data]).ignored(),
            ))
    });

    // Defines a proof parser. It does parse a proof statement, which
    // is a proof keyword followed by a name, a type representation,
    // a list of clauses, and a semicolon.
    stmt_parser
        .repeated()
        .collect::<Vec<_>>()
        .map(|statements| ProofFile { statements })
}
