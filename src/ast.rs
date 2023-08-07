use std::{fmt::Debug, cell::RefCell, rc::Rc, hash::Hash};

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
#[derive(Default, Debug, Hash, PartialEq, Eq, Clone)]
pub enum StmtKind {
    #[default]
    Error,
    Data(DataStmt),
    Fun(FunStmt),
    Term(Expr),
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

pub type Expr = Box<Spanned<ExprKind>>;
pub type Pattern = Box<Spanned<PatternKind>>;
pub type Stmt = Box<Spanned<StmtKind>>;

/// A spanned value is a value paired with a span. The span is used
/// to represent the location of the value in the source code.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Spanned<T> {
    pub data: T,
    pub span: SimpleSpan,
}
