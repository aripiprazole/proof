use std::rc::Rc;

use crate::parser::Span;

/// Represents a HOAS term. It's used for representing
/// the AST, but also for representing the type of a
/// term.

#[derive(Clone)]
pub enum Term {
    Pi(Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Lambda(Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Apply(Box<Term>, Box<Term>),
    SrcPos(Span, Box<Term>),
}