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
    primitive::{any, end, just, one_of},
    recovery::{nested_delimiters, skip_then_retry_until, via_parser},
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

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameter {
    pub pattern: Pattern,
    pub type_rep: Term,
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
            .field("type_rep", &self.parameter.type_rep.debug(self.state))
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
    pub type_rep: Term,
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
            .field("type_rep", &self.constructor.type_rep.debug(self.state))
            .finish()
    }
}

/// A data statement is used to declare a new algebraic
/// or a generalized algebraic data type.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataStmt {
    pub name: Constructor,
    pub parameters: Parameters,
    pub type_rep: Term,
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
pub struct FunStmt {
    pub name: Constructor,
    pub type_rep: Term,
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
    Fun(FunStmt),
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
                .field("type_rep", &data_stmt.type_rep.debug(self.state))
                .field(
                    "constructors",
                    &data_stmt
                        .constructors
                        .into_iter()
                        .map(|constructor| constructor.debug(self.state))
                        .collect::<Vec<_>>(),
                )
                .finish(),
            StmtKind::Fun(val_stmt) => f
                .debug_struct("FunStmt")
                .field("name", &val_stmt.name)
                .field("type_rep", &val_stmt.type_rep.debug(self.state))
                .field(
                    "clauses",
                    &val_stmt
                        .clauses
                        .iter()
                        .map(|value| value.debug(self.state))
                        .collect::<Vec<_>>(),
                )
                .finish(),
            StmtKind::Term(term) => term.debug(self.state).fmt(f),
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
#[derive(Default, Eq, Clone)]
pub struct Hole {
    /// The name of the variable.
    pub name: Option<Identifier>,
    pub hole: Rc<RefCell<Option<Term>>>,
}

impl Hole {
    /// Creates a new hole without a value filled.
    pub fn new(name: Identifier) -> Self {
        Self {
            name: Some(name),
            hole: Rc::new(RefCell::new(None)),
        }
    }
}

impl Debug for Hole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.name.clone().unwrap_or("_".into()))
    }
}

impl Hash for Hole {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl PartialEq for Hole {
    fn eq(&self, other: &Self) -> bool {
        match (&self.name, &other.name) {
            (Some(name), Some(other_name)) => name == other_name,
            _ => {
                let value = self.hole.borrow();
                let other_value = other.hole.borrow();
                (*value).eq(&*other_value)
            }
        }
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
            TermKind::Hole(var) => write!(f, "Hole({})", var.name.unwrap_or("_".into())),
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
    extra::Full<Rich<'tokens, Token<'src>, Span>, TermState, ()>,
> {
    let pattern_parser = recursive(move |pattern| {
        let id = select! {
            Token::Identifier(str) => PatternKind::Variable(str.into()),
        }
        .map_with_span(spanned)
        .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
        .labelled("identifier pattern");

        // A cons pattern is defined as a name but not followed by a list of patterns.
        //
        // It does parses without parenthesis, because it is easier to parse.
        let cons_id = select! { Token::Constructor(str) => str }
            .map(|name: &str| PatternKind::Constructor(name.into(), vec![]))
            .map_with_span(spanned)
            .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
            .labelled("constructor identifier pattern");

        // A cons pattern is defined as a name followed by a list of patterns.
        let cons = recursive(|_| {
            just(Token::Ctrl('('))
                .then(select! { Token::Constructor(str) => str })
                .then(pattern.clone().repeated().collect::<Vec<_>>())
                .then_ignore(just(Token::Ctrl(')')))
                .map(|((_, name), patterns)| PatternKind::Constructor(name.into(), patterns))
                .map_with_span(spanned)
                .map_with_state(|value, _, state: &mut TermState| state.patterns.intern(value))
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
                Token::Number(number) => TermKind::Number(number),
                Token::Identifier(id) if id != "->" => TermKind::Hole(Hole::new(id.into())),
                Token::Constructor(id) if id == "Type" => TermKind::Type(0),
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

            value.or(group).labelled("primary")
        });

        // Defines the parser for the application. It is the second
        // level of the expression parser.
        let app = recursive(|_| {
            primary.clone().foldl_with_state(
                primary.clone().repeated(),
                |acc, next, state: &mut TermState| {
                    let first = state.terms.span(acc);
                    let end = state.terms.span(next);

                    let span = (first.start..end.end).into();
                    let kind = TermKind::Apply(acc, next);

                    state.terms.intern(spanned(kind, span))
                },
            )
        });

        // Defines an annotation parser. It does parse a type
        // annotation, which is a value followed by a type.
        let ann = recursive(|_| {
            app.clone()
                .foldl_with_state(
                    just(Token::Ctrl(':')).then(expr.clone()).repeated(),
                    |acc, (_, next), state: &mut TermState| {
                        let first = state.terms.span(acc);
                        let end = state.terms.span(next);

                        let span = (first.start..end.end).into();
                        let kind = TermKind::Ann(acc, next);

                        state.terms.intern(spanned(kind, span))
                    },
                )
                .labelled("annotation")
        });

        // Defines a dependent function type parser. It does parse
        // a function type, which is a type followed by a type.
        let pi = recursive(|_| {
            app.clone()
                .map_with_state(|type_rep, _, state: &mut TermState| {
                    match state.terms.get(type_rep) {
                        TermKind::Ann(name, type_rep) => match state.terms.get(name) {
                            TermKind::Hole(hole) => (hole.name.unwrap_or("_".into()), type_rep),
                            _ => ("_".into(), type_rep),
                        },
                        _ => ("_".into(), type_rep),
                    }
                })
                .then(just(Token::Identifier("->")))
                .then(expr.clone())
                .map(|(((name, parameter), _), value)| TermKind::Pi(name, parameter, value))
                .map_with_span(spanned)
                .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
                .labelled("pi expression")
        });

        // Defines a lambda parser. It does parse a lambda expression,
        // which is a pattern followed by an expression.
        let lambda = recursive(|_| {
            just(Token::Ctrl('\\'))
                .then(pattern_parser.clone())
                .then_ignore(just(Token::Identifier(".")))
                .then(expr.clone())
                .map(|((_, pattern), expr)| TermKind::Lambda(pattern, expr))
                .map_with_span(spanned)
                .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
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
                .map(|(((_, pattern), value), expr)| TermKind::Let(pattern, value, expr))
                .map_with_span(spanned)
                .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value))
                .labelled("let exprression")
                .as_context()
        });

        // Defines the expression parser. It is the top level of the
        // expression parser.
        pi.or(ann)
            .or(lambda)
            .or(let_expr)
            .recover_with(via_parser(
                nested_delimiters(
                    Token::Ctrl('('),
                    Token::Ctrl(')'),
                    [
                        (Token::Ctrl('['), Token::Ctrl(']')),
                        (Token::Ctrl('{'), Token::Ctrl('}')),
                    ],
                    |span| Spanned {
                        data: TermKind::Error,
                        span,
                    },
                )
                .map_with_state(|value, _, state: &mut TermState| state.terms.intern(value)),
            ))
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
                .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value))
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
                .map_with_state(|type_rep, _, state: &mut TermState| match type_rep {
                    Some(type_rep) => type_rep,
                    None => state.terms.intern(Spanned {
                        data: TermKind::Hole(Hole::default()),
                        span: (0..0).into(),
                    }),
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
                .map(|(pattern, type_rep)| Parameter { pattern, type_rep })
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
                .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value))
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
                .map(|((_, patterns), term)| Clause { patterns, term })
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
                .map_with_state(|value, _, state: &mut TermState| state.stmts.intern(value))
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
                    .with_message(format!("in the context {}", label))
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

impl Pattern {
    // Returns a debug representation of the pattern.
    pub fn display<'state>(&self, state: &'state TermState) -> PatternDisplay<'state> {
        PatternDisplay {
            state,
            pattern: *self,
        }
    }
}

pub struct PatternDisplay<'state> {
    pub state: &'state TermState,
    pub pattern: Pattern,
}

impl Display for PatternDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.patterns.get(self.pattern) {
            PatternKind::Error => write!(f, "error"),
            PatternKind::Variable(name) => write!(f, "{name}"),
            PatternKind::Constructor(constructor, patterns) => {
                write!(
                    f,
                    "({constructor} {})",
                    patterns
                        .into_iter()
                        .map(|pattern| pattern.display(self.state))
                        .fold("".to_string(), |acc, next| {
                            if acc.is_empty() {
                                format!("{next}")
                            } else {
                                format!("{acc} {next}")
                            }
                        })
                )
            }
        }
    }
}

impl Term {
    // Returns a debug representation of the term.
    pub fn display<'state>(&self, state: &'state TermState) -> TermDisplay<'state> {
        TermDisplay { state, term: *self }
    }
}

pub struct TermDisplay<'state> {
    pub state: &'state TermState,
    pub term: Term,
}

impl Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.terms.get(self.term) {
            TermKind::Error => write!(f, "error"),
            TermKind::Type(level) => write!(f, "type {level}"),
            TermKind::Number(n) => write!(f, "{n}"),
            TermKind::String(string) => write!(f, "\"{string}\""),
            TermKind::Constructor(constructor) => write!(f, "{constructor}"),
            TermKind::Hole(hole) => write!(f, "?{}", hole.name.unwrap_or("_".into())),
            TermKind::Ann(value, against) => write!(
                f,
                "{} : {}",
                value.display(self.state),
                against.display(self.state)
            ),
            TermKind::Lambda(parameter, value) => write!(
                f,
                "\\{}. {}",
                parameter.display(self.state),
                value.display(self.state)
            ),
            TermKind::Apply(callee, arg) => write!(
                f,
                "{} {}",
                callee.display(self.state),
                arg.display(self.state)
            ),
            TermKind::Let(name, value, expr) => write!(
                f,
                "let {} = {} in {}",
                name.display(self.state),
                value.display(self.state),
                expr.display(self.state)
            ),
            TermKind::Pi(name, domain, codomain) if name == "_" => write!(
                f,
                "{} -> {}",
                domain.display(self.state),
                codomain.display(self.state)
            ),
            TermKind::Pi(name, domain, codomain) => write!(
                f,
                "({name} : {}) -> {}",
                domain.display(self.state),
                codomain.display(self.state)
            ),
        }
    }
}

fn main() {
    let mut state = TermState::default();
    let ast = state.parse([
        "// simple file",
        "data Bool : Type where",
        "  True  : Bool",
        ", False : Bool",
        "",
        "fun and : Bool -> Bool -> Bool",
        "        | True, True   = True",
        "        | _,    False  = False",
        "        | _,    _      = False",
        "        ;",
        "",
        "and True False;",
    ]);

    println!("{:#?}", ast.debug(&state));
}
