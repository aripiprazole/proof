use std::hash::Hash;

use chumsky::{
    error::Error,
    prelude::Rich,
    primitive::{any, one_of},
    span::SimpleSpan,
    text,
    util::MaybeRef,
    Parser, IterParser, extra::Err,
};

/// The token type used by the lexer.
#[derive(Debug, PartialEq, Clone)]
pub enum Token<'src> {
    Id(&'src str),
    Str(&'src str),
    Cons(&'src str),
    Num(isize),
    Ctrl(char),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataStmt {
    pub name: Constructor,
    pub type_rep: Term,
    pub constructors: Vec<(Constructor, Term)>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Clause {
    pub patterns: Vec<Pattern>,
    pub value: Term,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct ValStmt {
    pub name: Constructor,
    pub type_rep: Term,
    pub constructors: Vec<Clause>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Stmt {
    Data(DataStmt),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Pattern {
    Var(Identifier),
    Cons(Constructor, Vec<Pattern>),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Expr {
    Num(isize),
    Str(String),
    Var(Identifier),
    Abs(Identifier, Term),
    App(Term, Term),
    Let(String, Term, Term),
    Type(TypeRep),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum TypeRep {
    Pi(Identifier, Term, Term),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Spanned<T> {
    pub data: T,
    pub span: SimpleSpan,
}

impl<T: Hash> Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
        self.span.start.hash(state);
        self.span.end.hash(state);
    }
}

pub type Identifier = Spanned<String>;
pub type Constructor = Spanned<String>;

pub type Term = Box<Expr>;

pub type LexerError<'src> = Err<Rich<'src, char, SimpleSpan>>;

pub type Span = SimpleSpan;

/// Parse a string into a set of tokens.
///
/// This function is a wrapper around the lexer and parser, and is the main entry point
/// for the calculator.
pub fn lexer<'src>() -> impl Parser<'src, &'src str, Vec<(Token<'src>, Span)>, LexerError<'src>> {
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
    // characters or underscores. The regex pattern for it is `[A-Z_'][a-zA-Z0-9_'.]*`.
    let cons = any()
        // Use try_map over filter to get a better error on failure
        .try_map(|c: char, span| {
            if c.is_ascii_alphabetic() && c.is_uppercase() || c == '_' || c == '\'' {
                Ok(c)
            } else {
                Err(Error::<&str>::expected_found([], Some(MaybeRef::Val(c)), span))
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
            if c.is_ascii_alphabetic() || c == '_' {
                Ok(c)
            } else {
                Err(Error::<&str>::expected_found([], Some(MaybeRef::Val(c)), span))
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

    let ctrl = one_of("()[]{}").map(Token::Ctrl).labelled("ctrl");

    num.or(op)
        .or(ctrl)
        .or(cons)
        .or(id)
        .map_with_span(|token, span| (token, span))
        .padded()
        .repeated()
        .collect()
}

fn main() {
    println!("Hello, world!");
}
