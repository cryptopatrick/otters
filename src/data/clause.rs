use super::literal::Literal;
use super::{ClauseAttribute, ParentList};

/// Identifier for clauses produced during search.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClauseId(pub u32);

/// Clause structure mirroring the original Otter representation.
#[derive(Clone, Debug, PartialEq)]
pub struct Clause {
    pub id: Option<ClauseId>,
    pub literals: Vec<Literal>,
    pub pick_weight: i32,
    pub parents: ParentList,
    pub attributes: Vec<ClauseAttribute>,
    pub heat_level: i8,
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Self {
        Self {
            id: None,
            literals,
            pick_weight: 0,
            parents: ParentList::new(),
            attributes: Vec::new(),
            heat_level: 0,
        }
    }

    pub fn with_id(mut self, id: ClauseId) -> Self {
        self.id = Some(id);
        self
    }

    pub fn add_literal(&mut self, literal: Literal) {
        self.literals.push(literal);
    }

    pub fn add_parent(&mut self, id: ClauseId) {
        self.parents.push(id);
    }

    pub fn add_attribute(&mut self, attribute: ClauseAttribute) {
        self.attributes.push(attribute);
    }
}

#[cfg(test)]
mod tests {
    use super::{Clause, ClauseId};
    use crate::data::{
        ClauseAttribute, ClauseAttributeValue, Literal, Term, VariableId,
    };

    #[test]
    fn clause_construction() {
        let literal = Literal::new(true, Term::variable(VariableId::new(0)));
        let clause = Clause::new(vec![literal]).with_id(ClauseId(1));
        assert_eq!(clause.id, Some(ClauseId(1)));
        assert_eq!(clause.literals.len(), 1);
        assert!(clause.parents.is_empty());
        assert!(clause.attributes.is_empty());
    }

    #[test]
    fn clause_parents_and_attributes() {
        let literal = Literal::new(true, Term::variable(VariableId::new(1)));
        let mut clause = Clause::new(vec![literal]);
        clause.add_parent(ClauseId(42));
        assert_eq!(clause.parents.len(), 1);
        clause.add_attribute(ClauseAttribute::new(
            "weight",
            ClauseAttributeValue::Integer(3),
        ));
        assert_eq!(clause.attributes.len(), 1);
    }
}
