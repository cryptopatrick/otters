use super::ClauseId;

/// Represents a collection of clause parents, mirroring Otter's `struct ilist`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ParentList {
    entries: Vec<ClauseId>,
}

impl ParentList {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, id: ClauseId) {
        self.entries.push(id);
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = ClauseId>,
    {
        self.entries.extend(iter);
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &ClauseId> {
        self.entries.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::ParentList;
    use crate::data::ClauseId;

    #[test]
    fn parent_list_push_and_iterate() {
        let mut parents = ParentList::new();
        parents.push(ClauseId(1));
        parents.push(ClauseId(2));
        let collected: Vec<_> = parents.iter().cloned().collect();
        assert_eq!(collected, vec![ClauseId(1), ClauseId(2)]);
    }
}
