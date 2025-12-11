//! Term ordering for orienting equalities.
//!
//! Implements LRPO (Lexicographic Path Ordering), which is used to:
//! - Orient equalities (determine if l=r should be rewritten as l→r or r→l)
//! - Prevent infinite loops in paramodulation and demodulation
//! - Guide the search by choosing "simpler" terms

use crate::data::{SymbolId, Term, VariableId};
use std::cmp::Ordering;

/// Lexicographic Path Ordering (LRPO) for terms.
///
/// LRPO is a simplification ordering that satisfies:
/// - Well-founded: No infinite descending chains
/// - Total on ground terms: Any two ground terms can be compared
/// - Compatible with term structure: If s > t then f(...s...) > f(...t...)
///
/// The ordering is based on:
/// 1. Symbol precedence (lower symbol ID = higher precedence by default)
/// 2. Lexicographic comparison of arguments for same function symbol
/// 3. Variables are smaller than non-variable terms
#[derive(Debug, Clone)]
pub struct LRPO {
    /// Symbol precedence (lower value = higher precedence)
    /// If not specified, use symbol ID as precedence
    precedence: Vec<(SymbolId, u32)>,
}

impl LRPO {
    /// Create a new LRPO ordering with default precedence.
    pub fn new() -> Self {
        Self {
            precedence: Vec::new(),
        }
    }

    /// Set explicit precedence for a symbol (lower value = higher precedence).
    pub fn set_precedence(&mut self, symbol: SymbolId, prec: u32) {
        // Remove old precedence if exists
        self.precedence.retain(|(s, _)| *s != symbol);
        self.precedence.push((symbol, prec));
    }

    /// Get precedence for a symbol (lower = higher precedence).
    fn precedence(&self, symbol: SymbolId) -> u32 {
        self.precedence
            .iter()
            .find(|(s, _)| *s == symbol)
            .map(|(_, p)| *p)
            .unwrap_or_else(|| symbol.as_raw()) // Default: use symbol ID
    }

    /// Compare two terms using LRPO.
    ///
    /// Returns:
    /// - `Ordering::Greater` if `s > t` (s is "bigger" than t)
    /// - `Ordering::Less` if `s < t`
    /// - `Ordering::Equal` if `s = t` syntactically
    pub fn compare(&self, s: &Term, t: &Term) -> Ordering {
        match (s, t) {
            // Variables
            (Term::Variable { id: x, .. }, Term::Variable { id: y, .. }) => {
                if x == y {
                    Ordering::Equal
                } else {
                    // Arbitrary but consistent: compare by variable ID
                    x.cmp(y)
                }
            }

            // Variable vs non-variable: non-variable is greater
            (Term::Variable { .. }, Term::Application { .. }) => {
                // Check if variable occurs in t - if so, s < t
                if self.occurs_check(s, t) {
                    Ordering::Less
                } else {
                    Ordering::Less // Variables are always smaller
                }
            }

            (Term::Application { .. }, Term::Variable { .. }) => {
                // Check if t occurs in s - if so, s > t
                if self.occurs_check(t, s) {
                    Ordering::Greater
                } else {
                    Ordering::Greater // Non-variables are always bigger
                }
            }

            // Both are applications
            (
                Term::Application {
                    symbol: f,
                    args: s_args,
                },
                Term::Application {
                    symbol: g,
                    args: t_args,
                },
            ) => {
                // Case 1: If some s_arg >= t, then s > t
                for s_arg in s_args {
                    match self.compare(s_arg, t) {
                        Ordering::Greater | Ordering::Equal => return Ordering::Greater,
                        Ordering::Less => {}
                    }
                }

                // Case 2: If f = g and same arity, compare lexicographically
                if f == g && s_args.len() == t_args.len() {
                    return self.lex_compare(s_args, t_args);
                }

                // Case 3: Compare by precedence
                let f_prec = self.precedence(*f);
                let g_prec = self.precedence(*g);

                if f_prec < g_prec {
                    // f has higher precedence
                    // Check if s > all t_args
                    if t_args.iter().all(|t_arg| self.compare(s, t_arg) == Ordering::Greater) {
                        return Ordering::Greater;
                    }
                } else if f_prec > g_prec {
                    // g has higher precedence
                    // Check if all s_args < t
                    if s_args.iter().all(|s_arg| self.compare(s_arg, t) == Ordering::Less) {
                        return Ordering::Less;
                    }
                }

                // Default: compare by symbol ID if no other rule applies
                f.as_raw().cmp(&g.as_raw())
            }
        }
    }

    /// Lexicographic comparison of argument lists.
    fn lex_compare(&self, s_args: &[Term], t_args: &[Term]) -> Ordering {
        for (s_arg, t_arg) in s_args.iter().zip(t_args.iter()) {
            match self.compare(s_arg, t_arg) {
                Ordering::Equal => continue,
                other => return other,
            }
        }

        // All arguments equal, compare by length
        s_args.len().cmp(&t_args.len())
    }

    /// Check if variable v occurs in term t.
    fn occurs_check(&self, v: &Term, t: &Term) -> bool {
        match (v, t) {
            (Term::Variable { id: x, .. }, Term::Variable { id: y, .. }) => x == y,
            (Term::Variable { .. }, Term::Application { args, .. }) => {
                args.iter().any(|arg| self.occurs_check(v, arg))
            }
            _ => false,
        }
    }

    /// Check if s > t in LRPO ordering.
    pub fn greater(&self, s: &Term, t: &Term) -> bool {
        self.compare(s, t) == Ordering::Greater
    }

    /// Check if s >= t in LRPO ordering.
    pub fn greater_or_equal(&self, s: &Term, t: &Term) -> bool {
        matches!(self.compare(s, t), Ordering::Greater | Ordering::Equal)
    }
}

impl Default for LRPO {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::symbol::{SymbolKind, SymbolTable};

    fn make_var(id: u16) -> Term {
        Term::variable(VariableId::new(id))
    }

    fn make_const(table: &SymbolTable, name: &str) -> Term {
        let sym = table.intern(name, 0, SymbolKind::Constant);
        Term::application(sym, vec![])
    }

    fn make_fun(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Function);
        Term::application(sym, args)
    }

    #[test]
    fn lrpo_variable_vs_constant() {
        let table = SymbolTable::new();
        let lrpo = LRPO::new();

        let x = make_var(0);
        let a = make_const(&table, "a");

        // Constant > Variable
        assert_eq!(lrpo.compare(&a, &x), Ordering::Greater);
        assert_eq!(lrpo.compare(&x, &a), Ordering::Less);
    }

    #[test]
    fn lrpo_same_function_lex() {
        let table = SymbolTable::new();
        let lrpo = LRPO::new();

        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        let f_a = make_fun(&table, "f", vec![a.clone()]);
        let f_b = make_fun(&table, "f", vec![b.clone()]);

        // f(a) vs f(b) - depends on a vs b
        let result = lrpo.compare(&f_a, &f_b);
        // Should be consistent
        assert!(result != Ordering::Equal);
    }

    #[test]
    fn lrpo_nested_terms() {
        let table = SymbolTable::new();
        let lrpo = LRPO::new();

        let a = make_const(&table, "a");
        let f_a = make_fun(&table, "f", vec![a.clone()]);
        let f_f_a = make_fun(&table, "f", vec![f_a.clone()]);

        // f(f(a)) > f(a) > a
        assert_eq!(lrpo.compare(&f_f_a, &f_a), Ordering::Greater);
        assert_eq!(lrpo.compare(&f_a, &a), Ordering::Greater);
        assert_eq!(lrpo.compare(&f_f_a, &a), Ordering::Greater);
    }

    #[test]
    fn lrpo_variable_occurrence() {
        let table = SymbolTable::new();
        let lrpo = LRPO::new();

        let x = make_var(0);
        let f_x = make_fun(&table, "f", vec![x.clone()]);

        // f(x) > x (occurs check)
        assert_eq!(lrpo.compare(&f_x, &x), Ordering::Greater);
        assert_eq!(lrpo.compare(&x, &f_x), Ordering::Less);
    }
}
