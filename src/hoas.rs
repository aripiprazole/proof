use std::rc::Rc;

use crate::{parser::Span, ast::Identifier};

/// Represents a HOAS term. It's used for representing
/// the AST, but also for representing the type of a
/// term.

#[derive(Clone)]
pub enum Term {
    Type(usize),
    Number(isize),
    String(String),
    Constructor(String),
    Variable(String),
    Ann(Box<Term>, Box<Term>),
    Let(Identifier, Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Pi(Identifier, Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Lambda(Box<Term>, Rc<dyn Fn(Box<Term>) -> Term>),
    Apply(Box<Term>, Box<Term>),
    SrcPos(Span, Box<Term>),
}
