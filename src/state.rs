use std::{cell::RefCell, rc::Rc, marker::PhantomData, hash::Hash};

use fxhash::FxHashMap;
use interner::global::GlobalPool;

use crate::{parser::Span, ast::{Expr, Stmt, Spanned, StmtKind, PatternKind, ExprKind, Pattern}};

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
    pub terms: Interner<Expr, Spanned<ExprKind>>,
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