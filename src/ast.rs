use std::{fmt::Debug, hash::Hash};

use chumsky::span::SimpleSpan;

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameter {
    pub pattern: Pattern,
    pub type_rep: Expr,
}

/// Parameters are a list of implicit parameters.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Parameters {
    pub implicit_parameters: Vec<Parameter>,
    pub explicit_parameters: Vec<Parameter>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DataConstructor {
    pub name: Constructor,
    pub type_rep: Expr,
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

/// A statement is a top-level declaration in the language.
#[derive(Default, Hash, PartialEq, Eq, Clone)]
pub enum StmtKind {
    #[default]
    Error,
    Data(DataStmt),
    Fun(FunStmt),
    Term(Expr),
}

impl Debug for StmtKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "Error"),
            Self::Data(arg0) => arg0.fmt(f),
            Self::Fun(arg0) => arg0.fmt(f),
            Self::Term(arg0) => arg0.fmt(f),
        }
    }
}

/// A pattern is used to represent a value that is being matched
/// against.
///
/// The pattern can be a variable or a constructor applied to a list
/// of patterns.
#[derive(Default, Hash, PartialEq, Eq, Clone)]
pub enum PatternKind {
    #[default]
    Error,
    Variable(Identifier),
    Constructor(Constructor, Vec<Pattern>),
}

impl Debug for PatternKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "Error"),
            Self::Variable(arg0) => arg0.fmt(f),
            Self::Constructor(constructor, patterns) => f
                .debug_struct("Constructor")
                .field("constructor", constructor)
                .field("patterns", patterns)
                .finish(),
        }
    }
}

/// The expressions are the primary AST nodes of the programming
/// language. They represent dependent types, terms, and proofs.
#[derive(Default, Hash, PartialEq, Eq, Clone)]
pub enum ExprKind {
    /// The error expression is used to represent an error.
    #[default]
    Error,

    Hole,

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
    Variable(String),

    /// The annotation expression is used to represent an annotated
    /// expression with a type.
    Ann(Box<Expr>, Box<Expr>),

    /// The abstraction expression is used to represent a lambda
    /// abstraction.
    ///
    /// The first argument is the name of the parameter, and the
    /// second argument is the value of the parameter.
    Lambda(Pattern, Box<Expr>),

    /// The application expression is used to represent a function
    /// application.
    Apply(Box<Expr>, Box<Expr>),

    /// The let expression is used to represent a let binding
    /// expression.
    Let(Pattern, Box<Expr>, Box<Expr>),

    /// The pi expression is used to represent a dependent function
    /// type.
    ///
    /// The first argument is the name of the parameter, the second
    /// argument is the type of the domain, and the third argument
    /// is the type of the codomain.
    Pi(Identifier, Box<Expr>, Box<Expr>),
}

impl Debug for ExprKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "Error"),
            Self::Hole => write!(f, "Hole"),
            Self::Type(arg0) => arg0.fmt(f),
            Self::Number(arg0) => arg0.fmt(f),
            Self::String(arg0) => arg0.fmt(f),
            Self::Constructor(arg0) => arg0.fmt(f),
            Self::Variable(arg0) => arg0.fmt(f),
            Self::Ann(value, against) => write!(f, "Ann({:?}, {:?})", value, against),
            Self::Lambda(parameter, value) => f
                .debug_struct("Lambda")
                .field("parameter", &parameter)
                .field("value", &value)
                .finish(),
            Self::Apply(callee, argument) => f
                .debug_struct("Apply")
                .field("callee", &callee)
                .field("argument", argument)
                .finish(),
            Self::Let(name, value, expr) => f
                .debug_struct("Let")
                .field("name", name)
                .field("value", value)
                .field("expr", expr)
                .finish(),
            Self::Pi(arg0, domain, codomain) => f
                .debug_struct("Pi")
                .field("name", &arg0)
                .field("domain", domain)
                .field("codomain", codomain)
                .finish(),
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

pub type Expr = Spanned<ExprKind>;
pub type Pattern = Spanned<PatternKind>;
pub type Stmt = Spanned<StmtKind>;

/// A spanned value is a value paired with a span. The span is used
/// to represent the location of the value in the source code.
#[derive(PartialEq, Eq, Clone)]
pub struct Spanned<T> {
    pub data: T,
    pub span: SimpleSpan,
}

impl<T: Debug> Debug for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}
