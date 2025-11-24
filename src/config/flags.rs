use std::collections::HashMap;

/// Boolean toggle that mimics the behaviour of the legacy `Flags` array.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Flag {
    pub name: String,
    pub enabled: bool,
}

impl Flag {
    pub fn new(name: impl Into<String>, enabled: bool) -> Self {
        Self { name: name.into(), enabled }
    }
}

/// Collection of flags keyed by name.  Provides ergonomic access for modules
/// that previously relied on global arrays.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FlagSet {
    flags: HashMap<String, Flag>,
}

impl FlagSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&mut self, name: impl Into<String>, enabled: bool) {
        let name_str = name.into();
        self.flags
            .entry(name_str.clone())
            .and_modify(|flag| flag.enabled = enabled)
            .or_insert_with(|| Flag::new(name_str, enabled));
    }

    pub fn is_enabled(&self, name: &str) -> bool {
        self.flags.get(name).map(|flag| flag.enabled).unwrap_or(false)
    }

    pub fn enable(&mut self, name: impl Into<String>) {
        self.set(name, true);
    }

    pub fn disable(&mut self, name: impl Into<String>) {
        self.set(name, false);
    }
}

#[cfg(test)]
mod tests {
    use super::FlagSet;

    #[test]
    fn update_flags() {
        let mut flags = FlagSet::new();
        assert!(!flags.is_enabled("verbose"));
        flags.enable("verbose");
        assert!(flags.is_enabled("verbose"));
        flags.disable("verbose");
        assert!(!flags.is_enabled("verbose"));
    }
}
