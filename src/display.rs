use std::fmt::Display;

use crate::ast::*;

impl Expr {
    // Returns a debug representation of the term.
    pub fn display<'state>(&self, state: &'state crate::state::TermState) -> TermDisplay<'state> {
        TermDisplay { state, term: *self }
    }
}

pub struct TermDisplay<'state> {
    pub state: &'state crate::state::TermState,
    pub term: Expr,
}

impl Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.state.terms.get(self.term) {
            ExprKind::Error => write!(f, "error"),
            ExprKind::Type(level) => write!(f, "type {level}"),
            ExprKind::Number(n) => write!(f, "{n}"),
            ExprKind::String(string) => write!(f, "\"{string}\""),
            ExprKind::Constructor(constructor) => write!(f, "{constructor}"),
            ExprKind::Hole(hole) => write!(f, "?{}", hole.name.unwrap_or("_".into())),
            ExprKind::Ann(value, against) => write!(
                f,
                "{} : {}",
                value.display(self.state),
                against.display(self.state)
            ),
            ExprKind::Lambda(parameter, value) => write!(
                f,
                "\\{}. {}",
                parameter.display(self.state),
                value.display(self.state)
            ),
            ExprKind::Apply(callee, arg) => write!(
                f,
                "{} {}",
                callee.display(self.state),
                arg.display(self.state)
            ),
            ExprKind::Let(name, value, expr) => write!(
                f,
                "let {} = {} in {}",
                name.display(self.state),
                value.display(self.state),
                expr.display(self.state)
            ),
            ExprKind::Pi(name, domain, codomain) if name == "_" => write!(
                f,
                "{} -> {}",
                domain.display(self.state),
                codomain.display(self.state)
            ),
            ExprKind::Pi(name, domain, codomain) => write!(
                f,
                "({name} : {}) -> {}",
                domain.display(self.state),
                codomain.display(self.state)
            ),
        }
    }
}

impl Pattern {
    // Returns a debug representation of the pattern.
    pub fn display<'state>(
        &self,
        state: &'state crate::state::TermState,
    ) -> PatternDisplay<'state> {
        PatternDisplay {
            state,
            pattern: *self,
        }
    }
}

pub struct PatternDisplay<'state> {
    pub state: &'state crate::state::TermState,
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
