use std::rc::Rc;

use crate::{
    ast::{Expr, Identifier, Pattern},
    parser::Span,
};

/// Represents a HOAS term. It's used for representing
/// the AST, but also for representing the type of a
/// term.
///
/// HOAS stands for Higher Order Abstract Syntax. It's
/// a technique for representing binders in a language.
#[derive(Default, Clone)]
pub enum Term {
    #[default]
    Error,
    
    Number(isize),
    String(String),
    Constructor(String),
    Variable(String),
    Ann(Box<Term>, Box<Term>),
    Let(Pattern, Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Pi(Identifier, Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Lambda(Pattern, Rc<dyn Fn(Box<Term>) -> Term>),
    Apply(Box<Term>, Box<Term>),

    /// Represents a type universe with a level
    /// of `usize`.
    Type(usize),

    /// This is used to represent the location of a term
    /// in the source code.
    /// 
    /// This is a variant, because we don't want to
    /// represent the location of a term in the type
    /// of a term, as we want to construct terms a lot
    /// of times.
    SrcPos(Span, Box<Term>),
}

impl From<Expr> for Term {
    /// This converts the concrete syntax tree into a HOAS
    /// term.
    /// 
    /// It does also provides the location of the term
    /// in the source code, as the [Expr] is based on
    /// a [crate::ast::Spanned] type.
    fn from(value: Expr) -> Self {
        use crate::ast::ExprKind::*;

        // Creates a HOAS term from an AST expression.
        let term = match value.data {
            Error => Self::Error,
            Type(level) => Self::Type(level),
            Number(number) => Self::Number(number),
            String(string) => Self::String(string),
            Constructor(constructor) => Self::Constructor(constructor),
            Hole(hole) => Self::Variable(hole),
            Ann(value, against) => {
                Self::Ann(Self::from(*value).into(), Self::from(*against).into())
            }
            Lambda(parameter, value) => {
                let value = Self::from(*value);

                Self::Lambda(
                    parameter,
                    Rc::new(move |_| {
                        // TODO: Substitution
                        value.clone()
                    }),
                )
            }
            Apply(callee, argument) => {
                let callee = Self::from(*callee);
                let argument = Self::from(*argument);

                Self::Apply(Box::new(callee), Box::new(argument))
            }
            Let(name, value, expr) => {
                let value = Self::from(*value);
                let expr = Self::from(*expr);

                Self::Let(
                    name,
                    value.into(),
                    Rc::new(move |_| {
                        // TODO: Substitution
                        expr.clone()
                    }),
                )
            }
            Pi(name, domain, codomain) => {
                let domain = Self::from(*domain);
                let codomain = Self::from(*codomain);

                Self::Pi(
                    name,
                    domain.into(),
                    Rc::new(move |_| {
                        // TODO: Substitution
                        codomain.clone()
                    }),
                )
            }
        };

        // Converts the location's into a HOAS location's.
        Self::SrcPos(value.span, term.into())
    }
}
