//! Custom operator declarations and precedence handling.
//!
//! Otter allows custom infix and prefix operators with configurable
//! precedence and associativity via `op(precedence, fixity, symbol)` declarations.

use std::collections::HashMap;

/// Operator fixity (position and associativity)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fixity {
    /// Prefix operator, non-associative (fx)
    Prefix,
    /// Prefix operator, right-associative (fy)
    PrefixRightAssoc,
    /// Infix operator, non-associative (xfx)
    Infix,
    /// Infix operator, right-associative (xfy)
    InfixRightAssoc,
    /// Infix operator, left-associative (yfx)
    InfixLeftAssoc,
    /// Postfix operator, non-associative (xf)
    Postfix,
    /// Postfix operator, left-associative (yf)
    PostfixLeftAssoc,
}

impl Fixity {
    /// Parse fixity from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "fx" => Some(Fixity::Prefix),
            "fy" => Some(Fixity::PrefixRightAssoc),
            "xfx" => Some(Fixity::Infix),
            "xfy" => Some(Fixity::InfixRightAssoc),
            "yfx" => Some(Fixity::InfixLeftAssoc),
            "xf" => Some(Fixity::Postfix),
            "yf" => Some(Fixity::PostfixLeftAssoc),
            _ => None,
        }
    }

    /// Check if this is a prefix operator
    pub fn is_prefix(&self) -> bool {
        matches!(self, Fixity::Prefix | Fixity::PrefixRightAssoc)
    }

    /// Check if this is an infix operator
    pub fn is_infix(&self) -> bool {
        matches!(
            self,
            Fixity::Infix | Fixity::InfixRightAssoc | Fixity::InfixLeftAssoc
        )
    }

    /// Check if this is a postfix operator
    pub fn is_postfix(&self) -> bool {
        matches!(self, Fixity::Postfix | Fixity::PostfixLeftAssoc)
    }

    /// Check if this is right-associative
    pub fn is_right_assoc(&self) -> bool {
        matches!(self, Fixity::PrefixRightAssoc | Fixity::InfixRightAssoc)
    }

    /// Check if this is left-associative
    pub fn is_left_assoc(&self) -> bool {
        matches!(self, Fixity::InfixLeftAssoc | Fixity::PostfixLeftAssoc)
    }
}

/// Operator metadata
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operator {
    pub symbol: String,
    pub precedence: u16,
    pub fixity: Fixity,
}

/// Operator table for managing custom operators
/// Note: A symbol can have multiple operator definitions with different fixities
/// (e.g., "-" can be both infix for subtraction and prefix for negation)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct OperatorTable {
    operators: HashMap<String, Vec<Operator>>,
}

impl OperatorTable {
    /// Create a new operator table with default Otter operators
    pub fn new() -> Self {
        let mut table = Self::default();

        // Default Otter operators (hardcoded from original implementation)
        // Lower precedence = binds less tightly
        table.add_operator("=", 700, Fixity::Infix);
        table.add_operator("!=", 700, Fixity::Infix);

        // Comparison operators (same precedence as equality)
        table.add_operator("==", 700, Fixity::Infix);
        table.add_operator("<", 700, Fixity::Infix);
        table.add_operator("<=", 700, Fixity::Infix);
        table.add_operator(">", 700, Fixity::Infix);
        table.add_operator(">=", 700, Fixity::Infix);

        // Arithmetic operators
        table.add_operator("+", 500, Fixity::InfixLeftAssoc);
        table.add_operator("-", 500, Fixity::InfixLeftAssoc);
        table.add_operator("*", 400, Fixity::InfixLeftAssoc);
        table.add_operator("/", 400, Fixity::InfixLeftAssoc);

        // Negation as prefix operator (higher precedence to bind tightly)
        table.add_operator("-", 200, Fixity::Prefix);

        table
    }

    /// Add an operator (supports multiple fixities for the same symbol)
    pub fn add_operator(&mut self, symbol: &str, precedence: u16, fixity: Fixity) {
        let op = Operator {
            symbol: symbol.to_string(),
            precedence,
            fixity,
        };
        self.operators
            .entry(symbol.to_string())
            .or_insert_with(Vec::new)
            .push(op);
    }

    /// Get all operator definitions for a symbol
    pub fn get_operators(&self, symbol: &str) -> Option<&Vec<Operator>> {
        self.operators.get(symbol)
    }

    /// Get all infix operators sorted by precedence (highest first), then by length (longest first)
    /// In Otter, higher precedence numbers bind LESS tightly, so we check them first
    /// Length-second ensures longer operators match before shorter ones at the same precedence
    pub fn infix_operators(&self) -> Vec<&Operator> {
        let mut ops: Vec<&Operator> = self
            .operators
            .values()
            .flatten()
            .filter(|op| op.fixity.is_infix())
            .collect();
        // Sort by precedence (highest first = binds less tightly), then by symbol length (longest first)
        // This finds the lowest-binding operator first, and prefers longer operators at same precedence
        ops.sort_by(|a, b| {
            b.precedence
                .cmp(&a.precedence)
                .then_with(|| b.symbol.len().cmp(&a.symbol.len()))
        });
        ops
    }

    /// Get all prefix operators
    pub fn prefix_operators(&self) -> Vec<&Operator> {
        self.operators
            .values()
            .flatten()
            .filter(|op| op.fixity.is_prefix())
            .collect()
    }

    /// Get all postfix operators
    pub fn postfix_operators(&self) -> Vec<&Operator> {
        self.operators
            .values()
            .flatten()
            .filter(|op| op.fixity.is_postfix())
            .collect()
    }

    /// Check if a string is a known operator
    pub fn is_operator(&self, symbol: &str) -> bool {
        self.operators.contains_key(symbol)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_operators() {
        let table = OperatorTable::new();
        assert!(table.is_operator("="));
        assert!(table.is_operator("+"));
        assert!(table.is_operator("*"));
        assert!(!table.is_operator("&"));
    }

    #[test]
    fn add_custom_operator() {
        let mut table = OperatorTable::new();
        table.add_operator("&", 460, Fixity::InfixRightAssoc);

        let ops = table.get_operators("&").unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(ops[0].precedence, 460);
        assert!(ops[0].fixity.is_right_assoc());
    }

    #[test]
    fn fixity_parsing() {
        assert_eq!(Fixity::from_str("fx"), Some(Fixity::Prefix));
        assert_eq!(Fixity::from_str("xfy"), Some(Fixity::InfixRightAssoc));
        assert_eq!(Fixity::from_str("yfx"), Some(Fixity::InfixLeftAssoc));
        assert_eq!(Fixity::from_str("invalid"), None);
    }

    #[test]
    fn operator_precedence_ordering() {
        let mut table = OperatorTable::new();
        table.add_operator("&", 460, Fixity::InfixRightAssoc);
        table.add_operator("|", 450, Fixity::InfixRightAssoc);

        let ops = table.infix_operators();
        // Lower precedence first
        assert!(ops.iter().position(|op| op.symbol == "*").unwrap()
                < ops.iter().position(|op| op.symbol == "+").unwrap());
    }
}
