use super::symbol::SymbolId;

/// Identifier used for variables.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VariableId(pub u16);

impl VariableId {
    pub const fn new(id: u16) -> Self {
        Self(id)
    }

    pub const fn as_u16(self) -> u16 {
        self.0
    }
}

/// Basic classification of terms, mirroring `NAME`, `VARIABLE`, and `COMPLEX`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TermKind {
    Name,
    Variable,
    Complex,
}

/// Representation of a first-order term.
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Variable { id: VariableId, symbol: Option<SymbolId> },
    Application { symbol: SymbolId, args: Vec<Term> },
}

impl Term {
    pub fn variable(id: VariableId) -> Self {
        Self::Variable { id, symbol: None }
    }

    pub fn named_variable(id: VariableId, symbol: SymbolId) -> Self {
        Self::Variable { id, symbol: Some(symbol) }
    }

    pub fn application(symbol: SymbolId, args: Vec<Term>) -> Self {
        Self::Application { symbol, args }
    }

    pub fn kind(&self) -> TermKind {
        match self {
            Term::Variable { .. } => TermKind::Variable,
            Term::Application { args, .. } if args.is_empty() => {
                TermKind::Name
            }
            Term::Application { .. } => TermKind::Complex,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Term::Variable { .. } => 0,
            Term::Application { args, .. } => args.len(),
        }
    }

    pub fn symbol(&self) -> Option<SymbolId> {
        match self {
            Term::Variable { symbol, .. } => *symbol,
            Term::Application { symbol, .. } => Some(*symbol),
        }
    }

    pub fn iter_args(&self) -> std::slice::Iter<'_, Term> {
        match self {
            Term::Variable { .. } => [].iter(),
            Term::Application { args, .. } => args.iter(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Term, TermKind, VariableId};
    use crate::data::symbol::{SymbolKind, SymbolTable};

    #[test]
    fn classify_terms() {
        let table = SymbolTable::new();
        let const_id = table.intern("a", 0, SymbolKind::Constant);
        let fun_id = table.intern("f", 2, SymbolKind::Function);
        let t_const = Term::application(const_id, vec![]);
        let t_var = Term::variable(VariableId::new(0));
        let t_fun =
            Term::application(fun_id, vec![t_const.clone(), t_var.clone()]);
        assert_eq!(t_const.kind(), TermKind::Name);
        assert_eq!(t_var.kind(), TermKind::Variable);
        assert_eq!(t_fun.kind(), TermKind::Complex);
        assert_eq!(t_fun.arity(), 2);
        assert_eq!(t_var.arity(), 0);
    }
}
