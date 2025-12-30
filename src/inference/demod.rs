//! Demodulation (equation-based rewriting).
//!
//! Demodulation simplifies terms by applying oriented equations as rewrite rules.

use crate::data::{Clause, Literal, LRPO, Term, VariableId};
use crate::inference::{apply_to_literal, Substitution, Unifier};
use std::cmp::Ordering;

/// A demodulator (oriented equation used for rewriting).
#[derive(Clone, Debug)]
pub struct Demodulator {
    /// Left-hand side of the equation (pattern to match)
    pub lhs: Term,
    /// Right-hand side (replacement)
    pub rhs: Term,
    /// Source clause ID (if any)
    pub source_id: Option<crate::data::ClauseId>,
}

impl Demodulator {
    /// Create a new demodulator from an equation.
    pub fn new(lhs: Term, rhs: Term) -> Self {
        Self {
            lhs,
            rhs,
            source_id: None,
        }
    }

    /// Create a demodulator with source information.
    pub fn with_source(mut self, id: crate::data::ClauseId) -> Self {
        self.source_id = Some(id);
        self
    }

    /// Try to apply this demodulator to a term.
    ///
    /// Returns Some(new_term) if the demodulator matches, None otherwise.
    pub fn apply(&self, term: &Term) -> Option<Term> {
        // Try to match the term against the LHS using one-way matching
        let mut subst = Substitution::new();

        if self.match_pattern(&self.lhs, term, &mut subst) {
            // Apply the substitution to the RHS
            Some(subst.apply(&self.rhs))
        } else {
            None
        }
    }

    /// One-way matching: pattern variables match term subterms.
    fn match_pattern(&self, pattern: &Term, term: &Term, subst: &mut Substitution) -> bool {
        match (pattern, term) {
            // Pattern variable matches any term
            (Term::Variable { id, .. }, _) => {
                if let Some(bound) = subst.lookup(*id) {
                    // Already bound - must match the same term
                    bound == term
                } else {
                    // Bind the variable
                    subst.bind(*id, term.clone());
                    true
                }
            }
            // Both applications - must have same symbol and matching args
            (
                Term::Application { symbol: s1, args: args1 },
                Term::Application { symbol: s2, args: args2 },
            ) => {
                if s1 != s2 || args1.len() != args2.len() {
                    return false;
                }
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    if !self.match_pattern(a1, a2, subst) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

/// Apply demodulators to simplify a term.
pub fn demodulate_term(term: &Term, demods: &[Demodulator]) -> Term {
    // First, recursively demodulate subterms
    let simplified = match term {
        Term::Variable { .. } => term.clone(),
        Term::Application { symbol, args } => {
            let new_args: Vec<Term> = args
                .iter()
                .map(|arg| demodulate_term(arg, demods))
                .collect();
            Term::Application {
                symbol: *symbol,
                args: new_args,
            }
        }
    };

    // Then try to apply demodulators at the root
    for demod in demods {
        if let Some(result) = demod.apply(&simplified) {
            // Recursively demodulate the result
            return demodulate_term(&result, demods);
        }
    }

    simplified
}

/// Apply demodulators to simplify a literal.
pub fn demodulate_literal(lit: &Literal, demods: &[Demodulator]) -> Literal {
    let new_atom = demodulate_term(&lit.atom, demods);
    Literal::new(lit.sign, new_atom).with_target(lit.target)
}

/// Apply demodulators to simplify a clause.
pub fn demodulate_clause(clause: &Clause, demods: &[Demodulator]) -> Clause {
    let new_literals: Vec<Literal> = clause
        .literals
        .iter()
        .map(|lit| demodulate_literal(lit, demods))
        .collect();

    let mut new_clause = Clause::new(new_literals);
    new_clause.pick_weight = clause.pick_weight;
    new_clause.heat_level = clause.heat_level;
    new_clause.attributes = clause.attributes.clone();
    new_clause.parents = clause.parents.clone();
    new_clause
}

/// Extract demodulators from a clause using LRPO ordering.
///
/// A clause can be used as a demodulator if it's a positive unit equality
/// where one side is greater than the other in LRPO ordering.
///
/// If `lrpo` is None, a default LRPO ordering is used.
pub fn extract_demodulator(
    clause: &Clause,
    eq_symbol: crate::data::SymbolId,
    lrpo: Option<&LRPO>,
) -> Option<Demodulator> {
    // Must be a unit clause
    if clause.literals.len() != 1 {
        return None;
    }

    let lit = &clause.literals[0];

    // Must be positive
    if !lit.sign {
        return None;
    }

    // Must be an equality
    match &lit.atom {
        Term::Application { symbol, args } if *symbol == eq_symbol && args.len() == 2 => {
            let lhs = &args[0];
            let rhs = &args[1];

            // Don't create demodulators for reflexivity (x = x)
            if terms_equal(lhs, rhs) {
                return None;
            }

            // Use LRPO to orient the equation: greater term becomes LHS
            // This ensures termination by always rewriting to "smaller" terms
            let default_lrpo;
            let ordering = match lrpo {
                Some(o) => o,
                None => {
                    default_lrpo = LRPO::new();
                    &default_lrpo
                }
            };
            match ordering.compare(lhs, rhs) {
                Ordering::Greater => {
                    // lhs > rhs: use lhs → rhs
                    Some(Demodulator::new(lhs.clone(), rhs.clone()))
                }
                Ordering::Less => {
                    // rhs > lhs: use rhs → lhs
                    Some(Demodulator::new(rhs.clone(), lhs.clone()))
                }
                Ordering::Equal => {
                    // Syntactically equal - should be caught by terms_equal above
                    // But if not, don't create a demodulator
                    None
                }
            }
        }
        _ => None,
    }
}

/// Check if two terms are structurally equal.
fn terms_equal(t1: &Term, t2: &Term) -> bool {
    match (t1, t2) {
        (Term::Variable { id: id1, .. }, Term::Variable { id: id2, .. }) => id1 == id2,
        (
            Term::Application { symbol: s1, args: args1 },
            Term::Application { symbol: s2, args: args2 },
        ) => {
            s1 == s2
                && args1.len() == args2.len()
                && args1.iter().zip(args2.iter()).all(|(a, b)| terms_equal(a, b))
        }
        _ => false,
    }
}

/// Compute a simple weight for a term (number of symbols).
fn term_weight(term: &Term) -> usize {
    match term {
        Term::Variable { .. } => 1,
        Term::Application { args, .. } => {
            1 + args.iter().map(term_weight).sum::<usize>()
        }
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

    fn make_app(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Function);
        Term::application(sym, args)
    }

    #[test]
    fn demodulate_simple() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // Demodulator: a -> b
        let demod = Demodulator::new(a.clone(), b.clone());

        // Apply to term a
        let result = demod.apply(&a);
        assert_eq!(result, Some(b.clone()));

        // Apply to term b (no match)
        let result = demod.apply(&b);
        assert_eq!(result, None);
    }

    #[test]
    fn demodulate_with_variable() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");
        let e = make_const(&table, "e");

        // Demodulator: f(e, x) -> x (left identity)
        let f_e_x = make_app(&table, "f", vec![e.clone(), x.clone()]);
        let demod = Demodulator::new(f_e_x, x.clone());

        // Apply to f(e, a)
        let f_e_a = make_app(&table, "f", vec![e, a.clone()]);
        let result = demod.apply(&f_e_a);
        assert_eq!(result, Some(a));
    }

    #[test]
    fn demodulate_nested() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // Demodulator: a -> b
        let demod = Demodulator::new(a.clone(), b.clone());

        // Apply to f(a, a)
        let f_a_a = make_app(&table, "f", vec![a.clone(), a.clone()]);
        let result = demodulate_term(&f_a_a, &[demod]);

        // Should become f(b, b)
        let f_b_b = make_app(&table, "f", vec![b.clone(), b.clone()]);
        assert_eq!(result, f_b_b);
    }

    #[test]
    fn term_weight_calculation() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);

        assert_eq!(term_weight(&a), 1);
        assert_eq!(term_weight(&x), 1);

        let f_a = make_app(&table, "f", vec![a.clone()]);
        assert_eq!(term_weight(&f_a), 2);

        let f_a_a = make_app(&table, "f", vec![a.clone(), a]);
        assert_eq!(term_weight(&f_a_a), 3);
    }

    #[test]
    fn extract_demodulator_from_equality() {
        let table = SymbolTable::new();
        let eq_sym = table.intern("=", 2, SymbolKind::Function);

        let a = make_const(&table, "a");
        let b = make_const(&table, "b");
        let f_a = make_app(&table, "f", vec![a.clone()]);

        // f(a) = b should become demodulator f(a) -> b
        let eq = Term::application(eq_sym, vec![f_a.clone(), b.clone()]);
        let clause = Clause::new(vec![Literal::new(true, eq)]);

        let demod = extract_demodulator(&clause, eq_sym, None);
        assert!(demod.is_some());

        let demod = demod.unwrap();
        assert_eq!(demod.lhs, f_a);
        assert_eq!(demod.rhs, b);
    }
}
