use std::collections::HashMap;

/// Values maintained in the parameter table.
#[derive(Clone, Debug, PartialEq)]
pub enum ParameterValue {
    Integer(i64),
    Float(f64),
    Text(String),
}

impl Default for ParameterValue {
    fn default() -> Self {
        ParameterValue::Integer(0)
    }
}

/// Parameter collection keyed by name.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ParameterSet {
    parameters: HashMap<String, ParameterValue>,
}

impl ParameterSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&mut self, name: impl Into<String>, value: ParameterValue) {
        self.parameters.insert(name.into(), value);
    }

    pub fn get(&self, name: &str) -> Option<&ParameterValue> {
        self.parameters.get(name)
    }

    pub fn get_int(&self, name: &str) -> Option<i64> {
        match self.get(name) {
            Some(ParameterValue::Integer(v)) => Some(*v),
            _ => None,
        }
    }

    pub fn get_float(&self, name: &str) -> Option<f64> {
        match self.get(name) {
            Some(ParameterValue::Float(v)) => Some(*v),
            _ => None,
        }
    }

    pub fn get_text(&self, name: &str) -> Option<&str> {
        match self.get(name) {
            Some(ParameterValue::Text(v)) => Some(v.as_str()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ParameterSet, ParameterValue};

    #[test]
    fn store_and_fetch_parameters() {
        let mut params = ParameterSet::new();
        params.set("max_seconds", ParameterValue::Integer(42));
        params.set("epsilon", ParameterValue::Float(0.5));
        params.set("name", ParameterValue::Text("otter".into()));
        assert_eq!(params.get_int("max_seconds"), Some(42));
        assert!(params.get_int("missing").is_none());
        assert_eq!(params.get_float("epsilon"), Some(0.5));
        assert_eq!(params.get_text("name"), Some("otter"));
    }
}
