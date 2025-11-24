use super::{Clause, ClauseId};

/// Storage for clauses that also assigns unique identifiers.
#[derive(Default, Debug, Clone)]
pub struct ClauseArena {
    next_id: u32,
    clauses: Vec<Clause>,
}

impl ClauseArena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, mut clause: Clause) -> ClauseId {
        self.next_id += 1;
        let id = ClauseId(self.next_id);
        clause.id = Some(id);
        self.clauses.push(clause);
        id
    }

    pub fn get(&self, id: ClauseId) -> Option<&Clause> {
        self.clauses.iter().find(|cl| cl.id == Some(id))
    }

    pub fn get_mut(&mut self, id: ClauseId) -> Option<&mut Clause> {
        self.clauses.iter_mut().find(|cl| cl.id == Some(id))
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::ClauseArena;
    use crate::data::{Clause, ClauseId, Literal, Term, VariableId};

    #[test]
    fn clause_arena_assigns_ids() {
        let mut arena = ClauseArena::new();
        let clause = Clause::new(vec![Literal::new(
            true,
            Term::variable(VariableId::new(0)),
        )]);
        let id = arena.insert(clause);
        assert_eq!(id, ClauseId(1));
        assert_eq!(arena.len(), 1);
        assert!(arena.get(id).is_some());
    }
}
