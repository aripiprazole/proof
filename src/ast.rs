use std::{fmt::Debug, cell::RefCell, rc::Rc, hash::Hash};

use chumsky::span::SimpleSpan;

use crate::{state::{TermState, HasData}, parser::Span};

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameter {
    pub pattern: Pattern,
    pub type_rep: Expr,
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
    pub type_rep: Expr,
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
    pub type_rep: Expr,
    pub constructors: Vec<DataConstructor>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Clause {
    pub patterns: Vec<Pattern>,
    pub term: Expr,
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
    pub type_rep: Expr,
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
    Term(Expr),
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
    pub hole: Rc<RefCell<Option<Expr>>>,
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
pub enum ExprKind {
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
    Ann(Expr, Expr),

    /// The abstraction expression is used to represent a lambda
    /// abstraction.
    ///
    /// The first argument is the name of the parameter, and the
    /// second argument is the value of the parameter.
    Lambda(Pattern, Expr),

    /// The application expression is used to represent a function
    /// application.
    Apply(Expr, Expr),

    /// The let expression is used to represent a let binding
    /// expression.
    Let(Pattern, Expr, Expr),

    /// The pi expression is used to represent a dependent function
    /// type.
    ///
    /// The first argument is the name of the parameter, the second
    /// argument is the type of the domain, and the third argument
    /// is the type of the codomain.
    Pi(Identifier, Expr, Expr),
}

/// An implementation of the `HasData` trait for the `TermKind`
impl HasData for Spanned<ExprKind> {
    type Output = ExprKind;

    fn data(&self) -> &Self::Output {
        &self.data
    }

    fn span(&self) -> Span {
        self.span
    }
}

impl Expr {
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
    pub term: Expr,
}

impl Debug for TermDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.terms.get(self.term) {
            ExprKind::Error => write!(f, "Error"),
            ExprKind::Type(level) => write!(f, "Type({})", level),
            ExprKind::Number(num) => write!(f, "Numer({})", num),
            ExprKind::String(str) => write!(f, "String({})", str),
            ExprKind::Constructor(con) => write!(f, "Constructor({})", con),
            ExprKind::Hole(var) => write!(f, "Hole({})", var.name.unwrap_or("_".into())),
            ExprKind::Ann(value, against) => write!(
                f,
                "Ann({:?}, {:?})",
                value.debug(self.state),
                against.debug(self.state)
            ),
            ExprKind::Lambda(parameter, value) => write!(
                f,
                "Lambda({:?}, {:?})",
                parameter.debug(self.state),
                value.debug(self.state)
            ),
            ExprKind::Apply(callee, argument) => write!(
                f,
                "Apply({:?}, {:?})",
                callee.debug(self.state),
                argument.debug(self.state)
            ),
            ExprKind::Let(pattern, value, expr) => write!(
                f,
                "Let({:?}, {:?}, {:?})",
                pattern.debug(self.state),
                value.debug(self.state),
                expr.debug(self.state)
            ),
            ExprKind::Pi(name, domain, codomain) => write!(
                f,
                "Pi({name:?}, {:?}, {:?})",
                domain.debug(self.state),
                codomain.debug(self.state)
            ),
        }
    }
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

/// A spanned value is a value paired with a span. The span is used
/// to represent the location of the value in the source code.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Spanned<T> {
    pub data: T,
    pub span: SimpleSpan,
}

new_interner_key!(Expr);
new_interner_key!(Pattern);
new_interner_key!(Stmt);