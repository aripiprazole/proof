use std::rc::Rc;

use fxhash::FxHashMap;

use crate::{
    ast::{Expr, Identifier, Pattern},
    parser::Span,
};

pub struct Env {
    pub env: FxHashMap<String, Term>,
}

impl Env {
    pub fn extend(&self, name: String, term: Term) -> Self {
        let mut env = self.env.clone();
        env.insert(name, term);
        Self { env }
    }
}

pub struct Ctx {
    pub ctx: FxHashMap<String, Term>,
}

impl Ctx {
    pub fn extend(&self, name: String, term: Term) -> Self {
        let mut ctx = self.ctx.clone();
        ctx.insert(name, term);
        Self { ctx }
    }
}

pub struct Error {
    pub message: String,
    pub span: Option<Span>,
}

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

    Hole,
    Number(isize),
    String(String),
    Constructor(String),
    Variable(String),
    Let(Pattern, Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Pi(Identifier, Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Lambda(Pattern, Rc<dyn Fn(Box<Term>) -> Term>),
    Apply(Box<Term>, Box<Term>),

    /// Represents a type universe with a level
    /// of `usize`.
    Type(usize),
}

impl Term {
    /// This evaluates the concrete syntax tree as a HOAS
    /// term.
    pub fn eval(&self, env: &Env, ctx: &Ctx) -> Result<Term, Error> {
        todo!()
    }
}

impl Expr {
    /// This checks the concrete syntax tree as a HOAS
    /// term.
    pub fn check(&self, env: &Env, ctx: &Ctx, type_rep: Term) -> Result<Term, Error> {
        todo!()
    }

    /// This infers the concrete syntax tree as a HOAS
    /// term.
    ///
    /// It does also provides the location of the term
    /// in the source code, as the [Expr] is based on
    /// a [crate::ast::Spanned] type.
    pub fn infer(&self, env: &Env, ctx: &Ctx) -> Result<Term, Error> {
        self.imp_infer(env, ctx).map_err(|span| Error {
            message: span.message,
            span: Some(self.span),
        })
    }

    /// This infers the concrete syntax tree as a HOAS
    /// term.
    ///
    /// It does also provides the location of the term
    /// in the source code, as the [Expr] is based on
    /// a [crate::ast::Spanned] type.
    pub fn imp_infer(&self, env: &Env, ctx: &Ctx) -> Result<Term, Error> {
        use crate::ast::ExprKind::*;

        // Creates a HOAS term from an AST expression.
        Ok(match self.data.clone() {
            Error => Term::Error,
            Hole => Term::Hole,
            Type(level) => Term::Type(level),
            Number(number) => Term::Number(number),
            String(string) => Term::String(string),
            Constructor(constructor) => Term::Constructor(constructor),
            Variable(hole) => Term::Variable(hole),
            Ann(value, type_rep) => {
                let type_rep = type_rep.infer(env, ctx)?;

                value.check(env, ctx, type_rep)?
            }
            Lambda(..) => {
                panic!("Can't infer lambda expression")
            }
            Apply(callee, argument) => {
                let callee = callee.infer(env, ctx)?;

                match callee {
                    Term::Pi(_, domain, f) => {
                        argument.check(env, ctx, *domain.clone())?;
                        f(domain)
                    }
                    _ => {
                        panic!("Can't infer application")
                    }
                }
            }
            Let(name, value, expr) => {
                value.check(env, ctx, Term::Type(0))?;

                todo!()
            }
            Pi(name, domain, codomain) => {
                todo!()
            }
        })
    }
}
