use std::{
    cell::RefCell,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    rc::Rc,
};

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::Error,
    extra::{self, Err},
    prelude::{Input, Rich},
    primitive::{any, just, one_of},
    recursive::recursive,
    select,
    span::SimpleSpan,
    text::{self, keyword},
    util::MaybeRef,
    IterParser, Parser,
};
use fxhash::FxHashMap;
use interner::global::GlobalPool;

/// The token type used by the lexer.
#[derive(Debug, PartialEq, Clone)]
pub enum Token<'src> {
    Let,
    Data,
    In,
    Val,
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
            Token::Val => write!(f, "val"),
            Token::Identifier(id) => write!(f, "{id}"),
            Token::String(str) => write!(f, "\"{str}\""),
            Token::Constructor(cons) => write!(f, "{cons}"),
            Token::Number(num) => write!(f, "{num}"),
            Token::Ctrl(ctrl) => write!(f, "{ctrl}"),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameter {
    pub pattern: Pattern,
    pub type_rep: Option<Term>,
}

impl Parameter {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> ParameterDebug<'state> {
        ParameterDebug {
            state,
            parameter: self.clone(),
        }
    }
}

pub struct ParameterDebug<'state> {
    pub state: &'state TermState,
    pub parameter: Parameter,
}

impl Debug for ParameterDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parameter")
            .field("pattern", &self.parameter.pattern.debug(self.state))
            .field(
                "type_rep",
                &self.parameter.type_rep.map(|value| value.debug(self.state)),
            )
            .finish()
    }
}

/// Parameters are a list of implicit parameters.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameters {
    pub implicit_parameters: Vec<Parameter>,
    pub explicit_parameters: Vec<Parameter>,
}

impl Parameters {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> ParametersDebug<'state> {
        ParametersDebug {
            state,
            parameters: self.clone(),
        }
    }
}

pub struct ParametersDebug<'state> {
    pub state: &'state TermState,
    pub parameters: Parameters,
}

impl Debug for ParametersDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parameters")
            .field(
                "implicit_parameters",
                &self
                    .parameters
                    .implicit_parameters
                    .iter()
                    .map(|value| value.debug(self.state))
                    .collect::<Vec<_>>(),
            )
            .field(
                "explicit_parameters",
                &self
                    .parameters
                    .explicit_parameters
                    .iter()
                    .map(|value| value.debug(self.state))
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataConstructor {
    pub name: Constructor,
    pub type_rep: Option<Term>,
}

impl DataConstructor {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> DataConstructorDebug<'state> {
        DataConstructorDebug {
            state,
            constructor: self.clone(),
        }
    }
}

pub struct DataConstructorDebug<'state> {
    pub state: &'state TermState,
    pub constructor: DataConstructor,
}

impl Debug for DataConstructorDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DataConstructor")
            .field("name", &self.constructor.name)
            .field(
                "type_rep",
                &self
                    .constructor
                    .type_rep
                    .map(|value| value.debug(self.state)),
            )
            .finish()
    }
}

/// A data statement is used to declare a new algebraic
/// or a generalized algebraic data type.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataStmt {
    pub name: Constructor,
    pub parameters: Parameters,
    pub type_rep: Option<Term>,
    pub constructors: Vec<DataConstructor>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Clause {
    pub patterns: Vec<Pattern>,
    pub term: Term,
}

impl Clause {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> ClauseDebug<'state> {
        ClauseDebug {
            state,
            clause: self.clone(),
        }
    }
}

pub struct ClauseDebug<'state> {
    pub state: &'state TermState,
    pub clause: Clause,
}

impl Debug for ClauseDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Clause")
            .field(
                "patterns",
                &self
                    .clause
                    .patterns
                    .iter()
                    .map(|value| value.debug(self.state))
                    .collect::<Vec<_>>(),
            )
            .field("term", &self.clause.term.debug(self.state))
            .finish()
    }
}

/// A val statement is used to declare a new value.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct ValStmt {
    pub name: Constructor,
    pub type_rep: Option<Term>,
    pub clauses: Vec<Clause>,
}

/// A proof file is a list of statements.
#[derive(Default, Debug, Hash, PartialEq, Eq, Clone)]
pub struct ProofFile {
    pub statements: Vec<Stmt>,
}

pub struct ProofFileDebug<'state> {
    pub state: &'state TermState,
    pub file: ProofFile,
}

impl ProofFile {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> ProofFileDebug<'state> {
        ProofFileDebug {
            state,
            file: self.clone(),
        }
    }
}

impl Debug for ProofFileDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_list();
        for stmt in &self.file.statements {
            debug.entry(&stmt.debug(self.state));
        }
        debug.finish()
    }
}

/// A statement is a top-level declaration in the language.
#[derive(Default, Debug, Hash, PartialEq, Eq, Clone)]
pub enum StmtKind {
    #[default]
    Error,
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

pub struct StmtDebug<'state> {
    pub state: &'state TermState,
    pub stmt: Stmt,
}

impl Stmt {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> StmtDebug<'state> {
        StmtDebug { state, stmt: *self }
    }
}

impl Debug for StmtDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.stmts.get(self.stmt) {
            StmtKind::Error => write!(f, "Error"),
            StmtKind::Data(data_stmt) => f
                .debug_struct("DataStmt")
                .field("name", &data_stmt.name)
                .field(
                    "type_rep",
                    &data_stmt.type_rep.map(|value| value.debug(self.state)),
                )
                .field(
                    "constructors",
                    &data_stmt
                        .constructors
                        .into_iter()
                        .map(|constructor| constructor.debug(self.state))
                        .collect::<Vec<_>>(),
                )
                .finish(),
            StmtKind::Val(val_stmt) => f
                .debug_struct("ValStmt")
                .field("name", &val_stmt.name)
                .field(
                    "type_rep",
                    &val_stmt.type_rep.map(|value| value.debug(self.state)),
                )
                .field("clauses", &val_stmt.clauses)
                .finish(),
            StmtKind::Term(_) => todo!(),
        }
    }
}

/// A pattern is used to represent a value that is being matched
/// against.
///
/// The pattern can be a variable or a constructor applied to a list
/// of patterns.
#[derive(Default, Debug, Hash, PartialEq, Eq, Clone)]
pub enum PatternKind {
    #[default]
    Error,
    Variable(Identifier),
    Constructor(Constructor, Vec<Pattern>),
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

pub struct PatternDebug<'state> {
    pub state: &'state TermState,
    pub pattern: Pattern,
}

impl Pattern {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> PatternDebug<'state> {
        PatternDebug {
            state,
            pattern: *self,
        }
    }
}

impl Debug for PatternDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.patterns.get(self.pattern) {
            PatternKind::Error => write!(f, "Error"),
            PatternKind::Variable(name) => write!(f, "Variable({})", name),
            PatternKind::Constructor(name, patterns) => f
                .debug_struct("Constructor")
                .field("name", &name)
                .field(
                    "patterns",
                    &patterns
                        .into_iter()
                        .map(|pattern| pattern.debug(self.state))
                        .collect::<Vec<_>>(),
                )
                .finish(),
        }
    }
}

/// A variable is a name paired with a hole. The hole is used to
/// represent the value of the variable.
#[derive(Eq, Clone)]
pub struct Hole {
    /// The name of the variable.
    pub name: Identifier,
    pub hole: Rc<RefCell<Option<Term>>>,
}

impl Hole {
    /// Creates a new hole without a value filled.
    pub fn new(name: Identifier) -> Self {
        Self {
            name,
            hole: Rc::new(RefCell::new(None)),
        }
    }
}

impl Debug for Hole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.name)
    }
}

impl Hash for Hole {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl PartialEq for Hole {
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
    Number(isize),

    /// The string literal expression is used to represent a string
    /// literal.
    String(String),

    /// The string literal expression is used to represent a
    /// constructor name.
    Constructor(String),

    /// The variable expression is used to represent a variable
    Hole(Hole),

    /// The annotation expression is used to represent an annotated
    /// expression with a type.
    Ann(Term, Term),

    /// The abstraction expression is used to represent a lambda
    /// abstraction.
    ///
    /// The first argument is the name of the parameter, and the
    /// second argument is the value of the parameter.
    Lambda(Pattern, Term),

    /// The application expression is used to represent a function
    /// application.
    Apply(Term, Term),

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

impl Term {
    /// Creates a new debug wrapper.
    pub fn debug<'state>(&self, state: &'state TermState) -> TermDebug<'state> {
        TermDebug { state, term: *self }
    }
}

/// A wrapper for the `Term` type that implements the `Debug` trait.
/// This wrapper is used to display the `Term` type in a more
/// readable format.
pub struct TermDebug<'state> {
    pub state: &'state TermState,
    pub term: Term,
}

impl Debug for TermDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.terms.get(self.term) {
            TermKind::Error => write!(f, "Error"),
            TermKind::Type(level) => write!(f, "Type({})", level),
            TermKind::Number(num) => write!(f, "Numer({})", num),
            TermKind::String(str) => write!(f, "String({})", str),
            TermKind::Constructor(con) => write!(f, "Constructor({})", con),
            TermKind::Hole(var) => write!(f, "Hole({})", var.name),
            TermKind::Ann(value, against) => write!(
                f,
                "Ann({:?}, {:?})",
                value.debug(self.state),
                against.debug(self.state)
            ),
            TermKind::Lambda(parameter, value) => write!(
                f,
                "Lambda({:?}, {:?})",
                parameter.debug(self.state),
                value.debug(self.state)
            ),
            TermKind::Apply(callee, argument) => write!(
                f,
                "Apply({:?}, {:?})",
                callee.debug(self.state),
                argument.debug(self.state)
            ),
            TermKind::Let(pattern, value, expr) => write!(
                f,
                "Let({:?}, {:?}, {:?})",
                pattern.debug(self.state),
                value.debug(self.state),
                expr.debug(self.state)
            ),
            TermKind::Pi(name, domain, codomain) => write!(
                f,
                "Pi({name:?}, {:?}, {:?})",
                domain.debug(self.state),
                codomain.debug(self.state)
            ),
        }
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

impl<K, V> Default for Interner<K, V>
where
    K: From<usize> + Into<usize>,
{
    fn default() -> Self {
        Self {
            id_to_value: Default::default(),
            value_to_id: Default::default(),
            phantom: Default::default(),
        }
    }
}

impl<K, V: Hash + PartialEq + Eq + Clone> Interner<K, V>
where
    K: From<usize> + Into<usize>,
{
    pub fn intern(&self, value: V) -> K {
        match self.get_id(&value) {
            Some(id) => id,
            None => {
                let id = fxhash::hash(&value);
                self.id_to_value.borrow_mut().insert(id, value.clone());
                self.value_to_id.borrow_mut().insert(value, id);
                K::from(id)
            }
        }
    }

    pub fn get_id(&self, value: &V) -> Option<K> {
        let value_to_id = self.value_to_id.borrow();
        let id = value_to_id.get(value)?;
        Some(K::from(*id))
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

impl Default for TermState {
    fn default() -> Self {
        Self {
            names: GlobalPool::new(),
            patterns: Default::default(),
            terms: Default::default(),
            stmts: Default::default(),
        }
    }
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

    num.or(op)
        .or(ctrl)
        .or(keyword("let").to(Token::Let))
        .or(keyword("data").to(Token::Data))
        .or(keyword("in").to(Token::In))
        .or(keyword("val").to(Token::Val))
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
            Token::Identifier(str) => PatternKind::Variable(str.into()),
        }
        .map_with_span(spanned)
        .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
        .labelled("identifier pattern");

        let cons_id = select! { Token::Constructor(str) => str }
            .map(|name: &str| PatternKind::Constructor(name.into(), vec![]))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
            .labelled("constructor identifier pattern");

        // A cons pattern is defined as a name followed by a list of patterns.
        let cons = just(Token::Ctrl('('))
            .then(select! { Token::Constructor(str) => str })
            .then(pattern.clone().repeated().collect::<Vec<_>>())
            .then_ignore(just(Token::Ctrl(')')))
            .map(|((_, name), patterns)| PatternKind::Constructor(name.into(), patterns))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
            .labelled("constructor pattern");

        id.or(cons).or(cons_id).labelled("pattern")
    });

    let expr_parser = recursive(|expr| {
        // Defines the parser for the value. It is the base of the
        // expression parser.
        let value = select! {
            Token::Number(number) => TermKind::Number(number),
            Token::Identifier(id) => TermKind::Hole(Hole::new(id.into())),
            Token::Constructor(id) => TermKind::Constructor(id.into()),
            Token::String(str) => TermKind::String(str.into()),
        }
        .map_with_span(spanned)
        .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
        .labelled("value");

        let group = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
            .labelled("group expression");

        let primary = value.or(group).labelled("primary");

        let app = primary.clone().foldl_with_state(
            primary.clone().repeated(),
            |acc, next, state: &mut TermState| {
                let first = state.terms.span(acc);
                let end = state.terms.span(next);

                let span = (first.start..end.end).into();
                let kind = TermKind::Apply(acc, next);

                state.terms.intern(spanned(kind, span))
            },
        );

        let abs = just(Token::Ctrl('\\'))
            .then(pattern_parser.clone())
            .then_ignore(just(Token::Identifier(".")))
            .then(expr.clone())
            .map(|((_, pattern), expr)| TermKind::Lambda(pattern, expr))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
            .labelled("lambda exprression");

        let let_expr = just(Token::Let)
            .then(pattern_parser.clone())
            .then_ignore(just(Token::Identifier("=")))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|(((_, pattern), value), expr)| TermKind::Let(pattern, value, expr))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
            .labelled("let exprression");

        app.or(abs).or(let_expr).labelled("expression")
    });

    let stmt_parser = {
        let expr_stmt = expr_parser
            .clone()
            .map(StmtKind::Term)
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value))
            .labelled("expression statement");

        let type_rep = just(Token::Ctrl(':'))
            .then(expr_parser.clone())
            .map(|(_, type_rep)| type_rep);

        let constructors = select! { Token::Constructor(str) => str }
            .then(type_rep.clone().or_not())
            .map(|(name, type_rep)| DataConstructor {
                name: name.into(),
                type_rep,
            })
            .labelled("data constructor");

        let parameter = pattern_parser
            .clone()
            .then(type_rep.clone().or_not())
            .map(|(pattern, type_rep)| Parameter { pattern, type_rep });

        let implicit_parameters = parameter
            .clone()
            .separated_by(just(Token::Ctrl(',')))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
            .labelled("implicit parameters");

        let explicit_parameters = parameter
            .clone()
            .separated_by(just(Token::Ctrl(',')))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
            .labelled("explicit parameters");

        let data_stmt = just(Token::Data)
            .then(select! { Token::Constructor(str) => str })
            .then(type_rep.clone().or_not())
            .then(implicit_parameters.or_not())
            .then(explicit_parameters.or_not())
            .then(
                constructors
                    .separated_by(just(Token::Ctrl(',')))
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::Ctrl('{')), just(Token::Ctrl('}'))),
            )
            .map(|(((((_, name), type_rep), implicits), explicits), cons)| {
                StmtKind::Data(DataStmt {
                    name: name.into(),
                    parameters: Parameters {
                        implicit_parameters: implicits.unwrap_or_default(),
                        explicit_parameters: explicits.unwrap_or_default(),
                    },
                    type_rep,
                    constructors: cons,
                })
            })
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value))
            .labelled("data statement");

        let clause = just(Token::Ctrl('|'))
            .then(
                pattern_parser
                    .clone()
                    .separated_by(just(Token::Ctrl(',')))
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Identifier("=")))
            .then(expr_parser.clone())
            .map(|((_, patterns), term)| Clause { patterns, term });

        let val_stmt = just(Token::Val)
            .then(select! { Token::Identifier(str) => str })
            .then(type_rep.clone().or_not())
            .then(clause.repeated().collect::<Vec<_>>().or_not())
            .try_map(|(((_, name), type_rep), clauses): (_, _), span| {
                let clauses: Vec<_> = clauses.unwrap_or_default();

                match type_rep {
                    Some(type_rep) => Ok(StmtKind::Val(ValStmt {
                        name: name.into(),
                        type_rep: Some(type_rep),
                        clauses,
                    })),
                    None if clauses.is_empty() => Err(Rich::custom(
                        span,
                        "you can either specify a type to a value or clauses, but not both",
                    )),
                    None => Ok(StmtKind::Val(ValStmt {
                        name: name.into(),
                        type_rep: None,
                        clauses,
                    })),
                }
            })
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value));

        data_stmt.or(val_stmt).or(expr_stmt).labelled("statement")
    };

    stmt_parser
        .repeated()
        .collect()
        .map(|statements| ProofFile { statements })
}

/// Parses a string into an [`ProofFile`].
///
/// [`ProofFile`]: [`ProofFile`]
pub fn parse(source: &str, state: &mut TermState) -> ProofFile {
    let filename = "terminal";

    let (tokens, lex_errors) = lexer().parse(source).into_output_errors();
    let tokens = tokens.unwrap_or_default();
    let tokens = tokens
        .into_iter()
        .map(|span| (span.data, span.span))
        .collect::<Vec<_>>();
    let tokens = tokens
        .as_slice()
        .spanned((source.len()..source.len()).into());
    let (proof_file, errors) = parser()
        .parse_with_state(tokens, state)
        .into_output_errors();

    // If there are no errors, return the parsed expression.
    if !errors.is_empty() || !lex_errors.is_empty() {
        // Combine the errors from the lexer and the parser.
        //
        // The lexer errors are converted to strings, and the
        // parser errors are converted to strings and the tokens
        // are converted to strings.

        report_ariadne_errors(
            filename,
            source,
            errors
                .into_iter()
                .map(|error| error.map_token(|c| c.to_string()))
                .chain(
                    lex_errors
                        .into_iter()
                        .map(|error| error.map_token(|token| token.to_string())),
                )
                .collect::<Vec<_>>(),
        );
    }

    // If the expression is not present, we return an error sentinel
    // value to avoid crashing.
    proof_file.unwrap_or_else(|| ProofFile { statements: vec![] })
}

/// Reports the errors from the [`parse`] function.
///
/// [`parse`]: [`parse`]
pub fn report_ariadne_errors(filename: &str, source: &str, errors: Vec<Rich<'_, String>>) {
    type AriadneSpan = (String, std::ops::Range<usize>);

    // Defines the filename of the source. And it is used to
    // create the report.
    let filename: String = filename.into();

    for error in errors {
        Report::<AriadneSpan>::build(ReportKind::Error, filename.clone(), 0)
            .with_code(1)
            .with_message(error.to_string())
            .with_label(
                Label::new((filename.clone(), error.span().into_range()))
                    .with_message(error.reason().to_string())
                    .with_color(Color::Red),
            )
            .with_labels(error.contexts().map(|(label, span)| {
                Label::new((filename.clone(), span.into_range()))
                    .with_message(format!("while parsing this {}", label))
                    .with_color(Color::Yellow)
            }))
            .finish()
            .eprint((filename.to_string(), Source::from(source.to_string())))
            .unwrap();
    }
}

impl TermState {
    /// Parses a file into an [`ProofFile`].
    pub fn parse<const N: usize>(&mut self, lines: [&str; N]) -> ProofFile {
        let mut src = String::new();

        for line in lines {
            src.push_str(line);
            src.push('\n');
        }

        parse(&src, self)
    }
}

fn main() {
    let mut state = TermState::default();

    let ast = state.parse([
        // Source code
        "data Bool : Type {",
        "  True : Bool",
        ", False : Bool",
        "}",
        "",
        "val not : Bool -> Bool",
        "        | True = False",
        "        | False = True",
    ]);

    println!("{:#?}", ast.debug(&state));
}
