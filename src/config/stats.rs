use std::collections::HashMap;

/// Stores counters analogous to the legacy `Stats` array.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    counters: HashMap<String, u64>,
}

impl Statistics {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&mut self, name: impl Into<String>, value: u64) {
        self.counters.insert(name.into(), value);
    }

    pub fn increment(&mut self, name: impl Into<String>) -> u64 {
        self.increment_by(name, 1)
    }

    pub fn increment_by(
        &mut self,
        name: impl Into<String>,
        amount: u64,
    ) -> u64 {
        let name_string = name.into();
        let entry = self.counters.entry(name_string).or_insert(0);
        *entry += amount;
        *entry
    }

    pub fn get(&self, name: &str) -> Option<u64> {
        self.counters.get(name).copied()
    }

    pub fn reset(&mut self, name: &str) {
        self.counters.remove(name);
    }

    pub fn clear(&mut self) {
        self.counters.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::Statistics;

    #[test]
    fn counters_increment() {
        let mut stats = Statistics::new();
        assert_eq!(stats.increment("cl_given"), 1);
        assert_eq!(stats.increment_by("cl_given", 4), 5);
        assert_eq!(stats.get("cl_given"), Some(5));
        stats.reset("cl_given");
        assert!(stats.get("cl_given").is_none());
    }
}
