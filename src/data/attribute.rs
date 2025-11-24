/// Represents additional metadata attached to clauses, similar to Otter's
/// `struct cl_attribute`.
#[derive(Clone, Debug, PartialEq)]
pub struct ClauseAttribute {
    pub name: String,
    pub value: ClauseAttributeValue,
}

impl ClauseAttribute {
    pub fn new(name: impl Into<String>, value: ClauseAttributeValue) -> Self {
        Self { name: name.into(), value }
    }
}

/// Possible attribute values.
#[derive(Clone, Debug, PartialEq)]
pub enum ClauseAttributeValue {
    Integer(i64),
    Float(f64),
    Text(String),
    Flag(bool),
}

#[cfg(test)]
mod tests {
    use super::{ClauseAttribute, ClauseAttributeValue};

    #[test]
    fn create_attribute() {
        let attr =
            ClauseAttribute::new("weight", ClauseAttributeValue::Integer(5));
        assert_eq!(attr.name, "weight");
    }
}
