use std::hash::Hash;

use chumsky::{
    error::Error,
    extra::{self, Err},
    prelude::Rich,
    primitive::{any, just, one_of},
    recursive::recursive,
    select,
    span::SimpleSpan,
    text::{self, keyword},
    util::MaybeRef,
    IterParser, Parser,
};

/// The token type used by the lexer.
#[derive(Debug, PartialEq, Clone)]
pub enum Token<'src> {
    Let,
    Data,
    In,
    Id(&'src str),
    Str(&'src str),
    Cons(&'src str),
    Num(isize),
    Ctrl(char),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameters {
    pub implicit_parameters: Vec<(Identifier, Spanned<Expr>)>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataStmt {
    pub name: Constructor,
    pub parameters: Parameters,
    pub type_rep: Spanned<Expr>,
    pub constructors: Vec<(Constructor, Spanned<Expr>)>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Clause {
    pub patterns: Vec<Pattern>,
    pub value: Spanned<Expr>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct ValStmt {
    pub name: Constructor,
    pub parameters: Parameters,
    pub type_rep: Spanned<Expr>,
    pub constructors: Vec<Clause>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct ProofFile {
    pub statements: Vec<Spanned<Stmt>>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Stmt {
    Data(DataStmt),
    Val(ValStmt),
    Term(Spanned<Expr>),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Pattern {
    Var(Identifier),
    Cons(Constructor, Vec<Pattern>),
}

#[derive(Default, Debug, Hash, PartialEq, Eq, Clone)]
pub enum Expr {
    #[default]
    Error,
    Type,
    Star,
    Num(isize),
    Str(String),
    Var(Identifier),
    Ann(Term, Term),
    Abs(Spanned<Pattern>, Term),
    App(Term, Term),
    Let(Spanned<Pattern>, Term, Term),
    Pi(Identifier, Term, Term),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Spanned<T> {
    pub data: T,
    pub span: SimpleSpan,
}

pub fn spanned<T>(value: T, span: SimpleSpan) -> Spanned<T> {
    Spanned { data: value, span }
}

impl<T: Hash> Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
        self.span.start.hash(state);
        self.span.end.hash(state);
    }
}

pub type Identifier = String;
pub type Constructor = String;

pub type Term = Box<Spanned<Expr>>;

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

            Ok(Token::Num(int))
        })
        .labelled("number");

    let op = one_of("+*-/!^|&<>=")
        .repeated()
        .at_least(1)
        .map_slice(Token::Cons)
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
        .map(Token::Cons);

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
        .map(Token::Id);

    let ctrl = one_of("()[]{}:\\").map(Token::Ctrl).labelled("ctrl");

    num.or(op)
        .or(ctrl)
        .or(keyword("let").to(Token::Let))
        .or(keyword("data").to(Token::Let))
        .or(keyword("in").to(Token::In))
        .or(cons)
        .or(id)
        .map_with_span(spanned)
        .padded()
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
/// [`Expr`]: [`Expr`]
/// [`Equation`]: [`Equation`]
fn parser<'tokens, 'src: 'tokens>() -> impl Parser<
    // Input Types
    'tokens,
    ParserInput<'tokens, 'src>,
    ProofFile,
    extra::Full<Rich<'tokens, Token<'src>, Span>, (), ()>,
> {
    let pattern_parser = recursive(|pattern| {
        let id = select! {
            Token::Id(str) => Pattern::Var(str.into()),
        }
        .map_with_span(spanned)
        .labelled("id pattern");

        id
    });

    let expr_parser = recursive(|expr| {
        // Defines the parser for the value. It is the base of the
        // expression parser.
        let value = select! {
            Token::Num(number) => Expr::Num(number),
            Token::Str(str) => Expr::Str(str.into()),
        }
        .map_with_span(spanned)
        .labelled("value");

        let group = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        let primary = value.or(group).labelled("primary");

        let app = primary
            .clone()
            .foldl(primary.clone().repeated(), |acc, next| {
                let span = (acc.span.start..acc.span.end).into();
                let kind = Expr::App(Box::new(acc), Box::new(next));

                spanned(kind, span)
            });

        let abs = just(Token::Ctrl('\\'))
            .then(pattern_parser.clone())
            .then(just(Token::Id(".")))
            .then(expr.clone())
            .map(|(((_, pattern), _), expr)| Expr::Abs(pattern, expr.into()))
            .map_with_span(spanned);

        let let_expr = just(Token::Let)
            .then(pattern_parser)
            .then(just(Token::Id("=")))
            .then(expr.clone())
            .then(just(Token::In))
            .then(expr.clone())
            .map(|(((((_, pattern), _), value), _), expr)| {
                Expr::Let(pattern, value.into(), expr.into())
            })
            .map_with_span(spanned);

        app.or(abs).or(let_expr).labelled("expression")
    });

    let stmt_parser = recursive(|stmt| {
        let expr_stmt = expr_parser
            .map(Stmt::Term)
            .map_with_span(spanned)
            .labelled("expression statement");

        expr_stmt
    });

    stmt_parser
        .repeated()
        .collect()
        .map(|statements| ProofFile { statements })
}

fn main() {
    println!("Hello, world!");
}
