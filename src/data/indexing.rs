use super::{Literal, SymbolId, Term, TermKind};
use std::collections::VecDeque;

/// Node type used in the IMD tree (index/match/demodulation).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImdNodeKind {
    Variable,
    Symbol(SymbolId),
}

/// IMD tree node capturing a portion of the term index.
#[derive(Clone, Debug, PartialEq)]
pub struct ImdNode {
    pub kind: ImdNodeKind,
    pub children: Vec<ImdNode>,
    pub literals: Vec<Literal>,
}

impl ImdNode {
    pub fn new(kind: ImdNodeKind) -> Self {
        Self { kind, children: Vec::new(), literals: Vec::new() }
    }

    pub fn add_child(&mut self, child: ImdNode) {
        self.children.push(child);
    }

    pub fn attach_literal(&mut self, literal: Literal) {
        self.literals.push(literal);
    }
}

/// IS tree node used for subsumption indexing.
#[derive(Clone, Debug, PartialEq)]
pub struct IsNode {
    pub kind: ImdNodeKind,
    pub children: Vec<IsNode>,
    pub terms: Vec<Term>,
}

impl IsNode {
    pub fn new(kind: ImdNodeKind) -> Self {
        Self { kind, children: Vec::new(), terms: Vec::new() }
    }

    pub fn add_child(&mut self, child: IsNode) {
        self.children.push(child);
    }

    pub fn attach_term(&mut self, term: Term) {
        self.terms.push(term);
    }
}

/// Breadth-first iterator helper for IMD nodes.
pub struct ImdBfs<'a> {
    queue: VecDeque<&'a ImdNode>,
}

impl<'a> ImdBfs<'a> {
    pub fn new(root: &'a ImdNode) -> Self {
        let mut queue = VecDeque::new();
        queue.push_back(root);
        Self { queue }
    }
}

impl<'a> Iterator for ImdBfs<'a> {
    type Item = &'a ImdNode;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.queue.pop_front() {
            for child in &node.children {
                self.queue.push_back(child);
            }
            Some(node)
        } else {
            None
        }
    }
}

/// Helper to classify a term into an IMD node kind.
pub fn term_to_imd_kind(term: &Term) -> ImdNodeKind {
    match term.kind() {
        TermKind::Variable => ImdNodeKind::Variable,
        _ => ImdNodeKind::Symbol(
            term.symbol().expect("non-variable term must have symbol"),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::{ImdBfs, ImdNode, ImdNodeKind, IsNode, term_to_imd_kind};
    use crate::data::{Literal, SymbolKind, SymbolTable, Term, VariableId};

    #[test]
    fn term_kind_conversion() {
        let table = SymbolTable::new();
        let const_id = table.intern("a", 0, SymbolKind::Constant);
        let term = Term::application(const_id, vec![]);
        match term_to_imd_kind(&term) {
            ImdNodeKind::Symbol(id) => assert_eq!(id, const_id),
            ImdNodeKind::Variable => panic!("expected symbol"),
        }
    }

    #[test]
    fn bfs_traversal_iterates_children() {
        let table = SymbolTable::new();
        let f = table.intern("f", 1, SymbolKind::Function);
        let mut root = ImdNode::new(ImdNodeKind::Symbol(f));
        root.add_child(ImdNode::new(ImdNodeKind::Variable));
        let mut iter = ImdBfs::new(&root);
        assert!(iter.next().is_some());
        assert!(iter.next().is_some());
        assert!(iter.next().is_none());
    }

    #[test]
    fn is_node_collects_terms() {
        let mut node = IsNode::new(ImdNodeKind::Variable);
        node.attach_term(Term::variable(VariableId::new(0)));
        assert_eq!(node.terms.len(), 1);
    }

    #[test]
    fn imd_node_can_attach_literal() {
        let mut node = ImdNode::new(ImdNodeKind::Variable);
        let literal = Literal::new(true, Term::variable(VariableId::new(1)));
        node.attach_literal(literal.clone());
        assert_eq!(node.literals.len(), 1);
    }
}
