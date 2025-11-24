use super::ClauseId;

/// Ordered collection of clause identifiers, mirroring the `list` struct in C.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClauseList {
    name: String,
    members: Vec<ClauseId>,
}

impl ClauseList {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into(), members: Vec::new() }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn push(&mut self, id: ClauseId) {
        self.members.push(id);
    }

    pub fn pop(&mut self) -> Option<ClauseId> {
        self.members.pop()
    }

    pub fn remove(&mut self, index: usize) -> Option<ClauseId> {
        if index < self.members.len() {
            Some(self.members.remove(index))
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.members.len()
    }

    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &ClauseId> {
        self.members.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::ClauseList;
    use crate::data::ClauseId;

    #[test]
    fn append_and_pop_from_clause_list() {
        let mut list = ClauseList::new("sos");
        assert!(list.is_empty());
        list.push(ClauseId(1));
        list.push(ClauseId(2));
        assert_eq!(list.len(), 2);
        assert_eq!(list.pop(), Some(ClauseId(2)));
        assert_eq!(list.pop(), Some(ClauseId(1)));
        assert!(list.pop().is_none());
    }
}
