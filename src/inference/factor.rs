//! Factoring inference rule.
//!
//! Factoring simplifies clauses by merging unifiable literals of the same sign.
//!
//! Example:
//!   Input:  P(X) | P(f(a)) | Q(b)
//!   Output: P(f(a)) | Q(b)    (by unifying X with f(a))

use crate::data::{Clause, ClauseId, Literal};
use crate::inference::{Substitution, Unifier};

/// Result of factoring a clause.
#[derive(Clone, Debug)]
pub struct Factor {
    /// The factored clause
    pub clause: Clause,
    /// The parent clause ID
    pub parent_id: Option<ClauseId>,
    /// The substitution used
    pub substitution: Substitution,
}

/// Attempt to factor a clause by finding two unifiable literals of the same sign.
///
/// Returns all possible factors (there may be multiple if several pairs unify).
pub fn factor_clause(clause: &Clause, parent_id: Option<ClauseId>) -> Vec<Factor> {
    let mut factors = Vec::new();

    // Try all pairs of literals
    for i in 0..clause.literals.len() {
        for j in (i + 1)..clause.literals.len() {
            let lit1 = &clause.literals[i];
            let lit2 = &clause.literals[j];

            // Can only factor literals with the same sign
            if lit1.sign != lit2.sign {
                continue;
            }

            // Try to unify the atoms
            let mut unifier = Unifier::new();
            if unifier.unify(&lit1.atom, &lit2.atom).is_ok() {
                let subst = unifier.into_substitution();

                // Build the factored clause: keep all literals except lit2,
                // and apply the substitution
                let mut new_literals = Vec::new();
                for (idx, lit) in clause.literals.iter().enumerate() {
                    if idx != j {
                        // Skip the second literal (it's merged with the first)
                        new_literals.push(subst.apply_to_literal(lit));
                    }
                }

                let mut factored_clause = Clause::new(new_literals);
                if let Some(id) = parent_id {
                    factored_clause.add_parent(id);
                }

                factors.push(Factor {
                    clause: factored_clause,
                    parent_id,
                    substitution: subst,
                });
            }
        }
    }

    factors
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::symbol::{SymbolKind, SymbolTable};
    use crate::data::{Term, VariableId};

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

    fn make_pred(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Predicate);
        Term::application(sym, args)
    }

    #[test]
    fn factor_simple_clause() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");
        let f_a = make_fun(&table, "f", vec![a.clone()]);

        // P(X) | P(f(a))
        let p_x = make_pred(&table, "P", vec![x]);
        let p_fa = make_pred(&table, "P", vec![f_a.clone()]);

        let clause = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(true, p_fa),
        ]);

        let factors = factor_clause(&clause, None);

        assert_eq!(factors.len(), 1, "Should produce one factor");
        assert_eq!(factors[0].clause.literals.len(), 1, "Should have one literal");
        // The remaining literal should be P(f(a))
    }

    #[test]
    fn factor_three_literals() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // P(X) | P(a) | Q(b)
        let p_x = make_pred(&table, "P", vec![x]);
        let p_a = make_pred(&table, "P", vec![a]);
        let q_b = make_pred(&table, "Q", vec![b]);

        let clause = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(true, p_a),
            Literal::new(true, q_b.clone()),
        ]);

        let factors = factor_clause(&clause, None);

        assert_eq!(factors.len(), 1);
        // Should result in P(a) | Q(b)
        assert_eq!(factors[0].clause.literals.len(), 2);
    }

    #[test]
    fn no_factor_different_signs() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        // P(X) | -P(a)  (different signs, cannot factor)
        let p_x = make_pred(&table, "P", vec![x]);
        let p_a = make_pred(&table, "P", vec![a]);

        let clause = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(false, p_a),
        ]);

        let factors = factor_clause(&clause, None);

        assert_eq!(factors.len(), 0, "Should not factor different signs");
    }

    #[test]
    fn no_factor_different_predicates() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        // P(X) | Q(a)  (different predicates)
        let p_x = make_pred(&table, "P", vec![x]);
        let q_a = make_pred(&table, "Q", vec![a]);

        let clause = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(true, q_a),
        ]);

        let factors = factor_clause(&clause, None);

        assert_eq!(factors.len(), 0, "Should not factor different predicates");
    }
}
