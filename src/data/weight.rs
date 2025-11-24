//! Symbol weight table for clause selection.
//!
//! This module implements the weighting scheme used by Otter for prioritizing
//! clauses during the given-clause loop. Each symbol can be assigned a weight,
//! and the weight of a clause is the sum of the weights of all its symbols.

use super::{Clause, Literal, SymbolId, Term};
use std::collections::HashMap;

/// Table mapping symbols to their weights.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WeightTable {
    /// Map from symbol ID to weight
    weights: HashMap<SymbolId, i32>,
    /// Default weight for symbols not in the table
    default_weight: i32,
}

impl WeightTable {
    /// Create a new empty weight table with default weight of 1.
    pub fn new() -> Self {
        Self {
            weights: HashMap::new(),
            default_weight: 1,
        }
    }

    /// Create a new weight table with a specific default weight.
    pub fn with_default(default_weight: i32) -> Self {
        Self {
            weights: HashMap::new(),
            default_weight,
        }
    }

    /// Set the weight for a specific symbol.
    pub fn set_weight(&mut self, symbol: SymbolId, weight: i32) {
        self.weights.insert(symbol, weight);
    }

    /// Get the weight for a symbol, or the default if not set.
    pub fn get_weight(&self, symbol: SymbolId) -> i32 {
        self.weights.get(&symbol).copied().unwrap_or(self.default_weight)
    }

    /// Set the default weight for unlisted symbols.
    pub fn set_default(&mut self, weight: i32) {
        self.default_weight = weight;
    }

    /// Calculate the weight of a term.
    pub fn weight_term(&self, term: &Term) -> i32 {
        match term {
            Term::Variable { .. } => {
                // Variables typically have weight 1
                1
            }
            Term::Application { symbol, args } => {
                // Symbol weight plus weights of all arguments
                let mut weight = self.get_weight(*symbol);
                for arg in args {
                    weight += self.weight_term(arg);
                }
                weight
            }
        }
    }

    /// Calculate the weight of a literal.
    pub fn weight_literal(&self, literal: &Literal) -> i32 {
        self.weight_term(&literal.atom)
    }

    /// Calculate the weight of a clause.
    /// The weight is the sum of all literal weights.
    pub fn weight_clause(&self, clause: &Clause) -> i32 {
        clause.literals.iter().map(|lit| self.weight_literal(lit)).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{Literal, Term, VariableId};

    #[test]
    fn default_weights() {
        let table = WeightTable::new();
        assert_eq!(table.get_weight(SymbolId::from_raw(42)), 1);
        assert_eq!(table.default_weight, 1);
    }

    #[test]
    fn custom_default() {
        let table = WeightTable::with_default(5);
        assert_eq!(table.get_weight(SymbolId::from_raw(42)), 5);
    }

    #[test]
    fn set_and_get_weight() {
        let mut table = WeightTable::new();
        let sym = SymbolId::from_raw(10);
        table.set_weight(sym, 3);
        assert_eq!(table.get_weight(sym), 3);
    }

    #[test]
    fn weight_variable() {
        let table = WeightTable::new();
        let var = Term::variable(VariableId::new(0));
        assert_eq!(table.weight_term(&var), 1);
    }

    #[test]
    fn weight_constant() {
        let mut table = WeightTable::new();
        let sym = SymbolId::from_raw(5);
        table.set_weight(sym, 2);

        let constant = Term::Application { symbol: sym, args: vec![] };
        assert_eq!(table.weight_term(&constant), 2);
    }

    #[test]
    fn weight_function() {
        let mut table = WeightTable::new();
        let f = SymbolId::from_raw(1);
        let g = SymbolId::from_raw(2);

        table.set_weight(f, 3);
        table.set_weight(g, 2);

        // f(g(X), Y) = f_weight + g_weight + X_weight + Y_weight = 3 + 2 + 1 + 1 = 7
        let x = Term::variable(VariableId::new(0));
        let y = Term::variable(VariableId::new(1));
        let g_x = Term::Application { symbol: g, args: vec![x] };
        let f_g_x_y = Term::Application { symbol: f, args: vec![g_x, y] };

        assert_eq!(table.weight_term(&f_g_x_y), 7);
    }

    #[test]
    fn weight_literal() {
        let mut table = WeightTable::new();
        let p = SymbolId::from_raw(10);
        table.set_weight(p, 5);

        let term = Term::Application { symbol: p, args: vec![Term::variable(VariableId::new(0))] };
        let literal = Literal::new(true, term);

        assert_eq!(table.weight_literal(&literal), 6); // 5 (P) + 1 (X) = 6
    }

    #[test]
    fn weight_clause() {
        let mut table = WeightTable::new();
        let p = SymbolId::from_raw(10);
        let q = SymbolId::from_raw(11);

        table.set_weight(p, 2);
        table.set_weight(q, 3);

        // Clause: P(X) | Q(Y)
        let p_x = Literal::new(true, Term::Application {
            symbol: p,
            args: vec![Term::variable(VariableId::new(0))]
        });
        let q_y = Literal::new(true, Term::Application {
            symbol: q,
            args: vec![Term::variable(VariableId::new(1))]
        });

        let clause = Clause::new(vec![p_x, q_y]);

        // P(X) = 2 + 1 = 3, Q(Y) = 3 + 1 = 4, total = 7
        assert_eq!(table.weight_clause(&clause), 7);
    }
}
