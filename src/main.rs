use std::{cell::RefCell, hash::Hash, marker::PhantomData, rc::Rc};

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
use fxhash::FxHashMap;

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

/// Parameters are a list of implicit parameters.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameters {
    pub implicit_parameters: Vec<(Identifier, Term)>,
}

/// A data statement is used to declare a new algebraic
/// or a generalized algebraic data type.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataStmt {
    pub name: Constructor,
    pub parameters: Parameters,
    pub type_rep: Term,
    pub constructors: Vec<(Constructor, Term)>,
}

/// A clause is used to represent a pattern matching case.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Clause {
    pub patterns: Vec<Pattern>,
    pub value: Spanned<TermKind>,
}

/// A val statement is used to declare a new value.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct ValStmt {
    pub name: Constructor,
    pub parameters: Parameters,
    pub type_rep: Spanned<TermKind>,
    pub constructors: Vec<Clause>,
}

/// A proof file is a list of statements.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct ProofFile {
    pub statements: Vec<Stmt>,
}

/// A statement is a top-level declaration in the language.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum StmtKind {
    Data(DataStmt),
    Val(ValStmt),
    Term(Term),
}

/// An implementation of the `HasData` trait for the `TermKind`
impl HasData for Spanned<StmtKind> {
    type Output = StmtKind;

    fn data(&self) -> &Self::Output {
        &self.data
    }

    fn span(&self) -> Span {
        self.span
    }
}

/// A pattern is used to represent a value that is being matched
/// against.
///
/// The pattern can be a variable or a constructor applied to a list
/// of patterns.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum PatternKind {
    Var(Identifier),
    Cons(Constructor, Vec<Pattern>),
}

/// An implementation of the `HasData` trait for the `TermKind`
impl HasData for Spanned<PatternKind> {
    type Output = PatternKind;

    fn data(&self) -> &Self::Output {
        &self.data
    }

    fn span(&self) -> Span {
        self.span
    }
}

/// A variable is a name paired with a hole. The hole is used to
/// represent the value of the variable.
#[derive(Debug, Eq, Clone)]
pub struct Var {
    /// The name of the variable.
    pub name: Identifier,
    pub hole: Rc<RefCell<Option<Term>>>,
}

impl Var {
    /// Creates a new hole without a value filled.
    pub fn new(name: Identifier) -> Self {
        Self {
            name,
            hole: Rc::new(RefCell::new(None)),
        }
    }
}

impl Hash for Var {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

/// The expressions are the primary AST nodes of the programming
/// language. They represent dependent types, terms, and proofs.
#[derive(Default, Debug, Hash, PartialEq, Eq, Clone)]
pub enum TermKind {
    /// The error expression is used to represent an error.
    #[default]
    Error,

    /// The type expression is used to represent the type of types.
    Type(usize),

    /// The literal value expression is used to represent a literal
    /// value.
    Num(isize),

    /// The string literal expression is used to represent a string
    /// literal.
    Str(String),

    /// The variable expression is used to represent a variable
    Var(Var),

    /// The annotation expression is used to represent an annotated
    /// expression with a type.
    Ann(Term, Term),

    /// The abstraction expression is used to represent a lambda
    /// abstraction.
    ///
    /// The first argument is the name of the parameter, and the
    /// second argument is the value of the parameter.
    Abs(Pattern, Term),

    /// The application expression is used to represent a function
    /// application.
    App(Term, Term),

    /// The let expression is used to represent a let binding
    /// expression.
    Let(Pattern, Term, Term),

    /// The pi expression is used to represent a dependent function
    /// type.
    ///
    /// The first argument is the name of the parameter, the second
    /// argument is the type of the domain, and the third argument
    /// is the type of the codomain.
    Pi(Identifier, Term, Term),
}

/// An implementation of the `HasData` trait for the `TermKind`
impl HasData for Spanned<TermKind> {
    type Output = TermKind;

    fn data(&self) -> &Self::Output {
        &self.data
    }

    fn span(&self) -> Span {
        self.span
    }
}

/// A spanned value is a value paired with a span. The span is used
/// to represent the location of the value in the source code.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Spanned<T> {
    pub data: T,
    pub span: SimpleSpan,
}

/// Create a spanned value.
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

/// A type alias for the identifiers used in the language. They are
/// defined by the regex pattern `[a-zA-Z_'.][a-zA-Z0-9_'.]*`.
pub type Identifier = String;

/// A type alias for the constructors used in the language. They are
/// defined by the regex pattern `[A-Z][a-zA-Z0-9_'.]*`.
pub type Constructor = String;

macro_rules! new_interner_key {
    ($name:ident) => {
        #[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
        pub struct $name(usize);

        impl From<usize> for $name {
            fn from(value: usize) -> Self {
                Self(value)
            }
        }

        impl From<$name> for usize {
            fn from($name(value): $name) -> usize {
                value
            }
        }
    };
}

new_interner_key!(Term);
new_interner_key!(Pattern);
new_interner_key!(Stmt);

pub type LexerError<'src> = Err<Rich<'src, char, SimpleSpan>>;

pub type ParserInput<'tokens, 'src> =
    chumsky::input::SpannedInput<Token<'src>, Span, &'tokens [(Token<'src>, Span)]>;

pub type Span = SimpleSpan;

pub trait HasData {
    type Output;

    fn data(&self) -> &Self::Output;
    fn span(&self) -> Span;
}

pub struct Interner<K, V>
where
    K: From<usize> + Into<usize>,
{
    pub id_to_value: Rc<RefCell<FxHashMap<usize, V>>>,
    pub value_to_id: Rc<RefCell<FxHashMap<V, usize>>>,
    pub phantom: PhantomData<K>,
}

impl<K, V: Hash + PartialEq + Eq + Clone> Interner<K, V>
where
    K: From<usize> + Into<usize>,
{
    pub fn intern(&self, value: V) -> K {
        if let Some(id) = self.value_to_id.borrow().get(&value) {
            K::from(*id)
        } else {
            let id = fxhash::hash(&value);
            self.id_to_value.borrow_mut().insert(id, value.clone());
            self.value_to_id.borrow_mut().insert(value, id);
            K::from(id)
        }
    }
}

impl<K, V> Interner<K, V>
where
    K: From<usize> + Into<usize>,
    V: HasData + Hash + PartialEq + Eq + Clone,
    V::Output: Clone + Default,
{
    pub fn get(&self, key: K) -> V::Output {
        self.id_to_value
            .borrow()
            .get(&key.into())
            .map(|value| value.data())
            .cloned()
            .unwrap_or_default()
    }

    pub fn span(&self, key: K) -> Span {
        self.id_to_value
            .borrow()
            .get(&key.into())
            .map(|value| value.span())
            .unwrap_or((0..0).into())
    }
}

pub struct TermState {
    pub names: interner::global::GlobalPool<String>,
    pub patterns: Interner<Pattern, Spanned<PatternKind>>,
    pub terms: Interner<Term, Spanned<TermKind>>,
    pub stmts: Interner<Stmt, Spanned<StmtKind>>,
}

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
/// [`Term`]: [`Term`]
pub fn parser<'tokens, 'src: 'tokens>() -> impl Parser<
    // Input Types
    'tokens,
    ParserInput<'tokens, 'src>,
    ProofFile,
    extra::Full<Rich<'tokens, Token<'src>, Span>, TermState, ()>,
> {
    let pattern_parser = recursive(move |pattern| {
        let id = select! {
            Token::Id(str) => PatternKind::Var(str.into()),
        }
        .map_with_span(spanned)
        .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
        .labelled("id pattern");

        // A cons pattern is defined as a name followed by a list of patterns.
        let cons = just(Token::Ctrl('('))
            .then(select! { Token::Cons(str) => str })
            .then(pattern.clone().repeated().collect())
            .then_ignore(just(Token::Ctrl(')')))
            .map(|((_, name), patterns): (_, Vec<_>)| PatternKind::Cons(name.into(), patterns))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value));

        id.or(cons)
    });

    let expr_parser = recursive(|expr| {
        // Defines the parser for the value. It is the base of the
        // expression parser.
        let value = select! {
            Token::Num(number) => TermKind::Num(number),
            Token::Str(str) => TermKind::Str(str.into()),
        }
        .map_with_span(spanned)
        .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
        .labelled("value");

        let group = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        let primary = value.or(group).labelled("primary");

        let app = primary.clone().foldl_with_state(
            primary.clone().repeated(),
            |acc, next, state: &mut TermState| {
                let first = state.terms.span(acc);
                let end = state.terms.span(next);

                let span = (first.start..end.end).into();
                let kind = TermKind::App(acc, next);

                state.terms.intern(spanned(kind, span))
            },
        );

        let abs = just(Token::Ctrl('\\'))
            .then(pattern_parser.clone())
            .then_ignore(just(Token::Id(".")))
            .then(expr.clone())
            .map(|((_, pattern), expr)| TermKind::Abs(pattern, expr))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value));

        let let_expr = just(Token::Let)
            .then(pattern_parser)
            .then_ignore(just(Token::Id("=")))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|(((_, pattern), value), expr)| TermKind::Let(pattern, value, expr))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value));

        app.or(abs).or(let_expr).labelled("expression")
    });

    let stmt_parser = {
        let expr_stmt = expr_parser
            .map(StmtKind::Term)
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value))
            .labelled("expression statement");

        expr_stmt
    };

    stmt_parser
        .repeated()
        .collect()
        .map(|statements| ProofFile { statements })
}

fn main() {
    println!("Hello, world!");
}
