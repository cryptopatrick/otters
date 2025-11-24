//! Subsumption checking for clauses.
//!
//! A clause C subsumes clause D if there exists a substitution θ such that
//! Cθ ⊆ D. This means C is more general than D, and D can be deleted.

use crate::data::{Clause, Literal, Term, VariableId};
use crate::inference::Substitution;

/// Check if clause `general` subsumes clause `specific`.
///
/// Returns true if general is more general than (or equal to) specific.
pub fn subsumes(general: &Clause, specific: &Clause) -> bool {
    // Quick check: general must have <= literals than specific
    if general.literals.len() > specific.literals.len() {
        return false;
    }

    // Try to find a substitution that maps general's literals into specific
    subsumes_recursive(
        &general.literals,
        0,
        &specific.literals,
        &mut vec![false; specific.literals.len()],
        &mut Substitution::new(),
    )
}

/// Recursive backtracking search for subsumption.
fn subsumes_recursive(
    general_lits: &[Literal],
    gen_idx: usize,
    specific_lits: &[Literal],
    used: &mut [bool],
    subst: &mut Substitution,
) -> bool {
    // Base case: all general literals matched
    if gen_idx >= general_lits.len() {
        return true;
    }

    let gen_lit = &general_lits[gen_idx];

    // Try to match this general literal with each unused specific literal
    for (spec_idx, spec_lit) in specific_lits.iter().enumerate() {
        if used[spec_idx] {
            continue;
        }

        // Signs must match
        if gen_lit.sign != spec_lit.sign {
            continue;
        }

        // Try to match the atoms
        let old_subst = subst.clone();

        if match_term(&gen_lit.atom, &spec_lit.atom, subst) {
            used[spec_idx] = true;

            // Recurse to match remaining literals
            if subsumes_recursive(general_lits, gen_idx + 1, specific_lits, used, subst) {
                return true;
            }

            // Backtrack
            used[spec_idx] = false;
        }

        *subst = old_subst;
    }

    false
}

/// One-way matching of terms (general to specific).
fn match_term(general: &Term, specific: &Term, subst: &mut Substitution) -> bool {
    match (general, specific) {
        // Variable in general can match anything in specific
        (Term::Variable { id, .. }, _) => {
            if let Some(bound) = subst.lookup(*id) {
                // Must match same term
                terms_equal(bound, specific)
            } else {
                subst.bind(*id, specific.clone());
                true
            }
        }
        // Both applications
        (
            Term::Application { symbol: s1, args: args1 },
            Term::Application { symbol: s2, args: args2 },
        ) => {
            if s1 != s2 || args1.len() != args2.len() {
                return false;
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                if !match_term(a1, a2, subst) {
                    return false;
                }
            }
            true
        }
        _ => false,
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

/// Check if a clause is subsumed by any clause in a list.
pub fn forward_subsumed(clause: &Clause, clauses: &[&Clause]) -> bool {
    clauses.iter().any(|c| subsumes(c, clause))
}

/// Find clauses in a list that are subsumed by the given clause.
pub fn back_subsumed<'a>(clause: &Clause, clauses: &[&'a Clause]) -> Vec<&'a Clause> {
    clauses
        .iter()
        .filter(|c| subsumes(clause, c))
        .copied()
        .collect()
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

    fn make_pred(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Predicate);
        Term::application(sym, args)
    }

    #[test]
    fn identical_clauses_subsume() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let p_a = make_pred(&table, "P", vec![a]);

        let c1 = Clause::new(vec![Literal::new(true, p_a.clone())]);
        let c2 = Clause::new(vec![Literal::new(true, p_a)]);

        assert!(subsumes(&c1, &c2));
        assert!(subsumes(&c2, &c1));
    }

    #[test]
    fn variable_subsumes_constant() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        // P(x) subsumes P(a)
        let p_x = make_pred(&table, "P", vec![x]);
        let p_a = make_pred(&table, "P", vec![a]);

        let general = Clause::new(vec![Literal::new(true, p_x)]);
        let specific = Clause::new(vec![Literal::new(true, p_a)]);

        assert!(subsumes(&general, &specific));
        assert!(!subsumes(&specific, &general));
    }

    #[test]
    fn smaller_clause_subsumes_larger() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // P(x) subsumes P(a) | Q(b)
        let p_x = make_pred(&table, "P", vec![x]);
        let p_a = make_pred(&table, "P", vec![a]);
        let q_b = make_pred(&table, "Q", vec![b]);

        let general = Clause::new(vec![Literal::new(true, p_x)]);
        let specific = Clause::new(vec![
            Literal::new(true, p_a),
            Literal::new(true, q_b),
        ]);

        assert!(subsumes(&general, &specific));
        assert!(!subsumes(&specific, &general));
    }

    #[test]
    fn different_predicates_dont_subsume() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let q_a = make_pred(&table, "Q", vec![a]);

        let c1 = Clause::new(vec![Literal::new(true, p_a)]);
        let c2 = Clause::new(vec![Literal::new(true, q_a)]);

        assert!(!subsumes(&c1, &c2));
        assert!(!subsumes(&c2, &c1));
    }

    #[test]
    fn different_signs_dont_subsume() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let p_a = make_pred(&table, "P", vec![a]);

        let c1 = Clause::new(vec![Literal::new(true, p_a.clone())]);
        let c2 = Clause::new(vec![Literal::new(false, p_a)]);

        assert!(!subsumes(&c1, &c2));
        assert!(!subsumes(&c2, &c1));
    }

    #[test]
    fn shared_variable_constraint() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // P(x, x) subsumes P(a, a) but not P(a, b)
        let p_xx = make_pred(&table, "P", vec![x.clone(), x]);
        let p_aa = make_pred(&table, "P", vec![a.clone(), a.clone()]);
        let p_ab = make_pred(&table, "P", vec![a, b]);

        let general = Clause::new(vec![Literal::new(true, p_xx)]);
        let specific1 = Clause::new(vec![Literal::new(true, p_aa)]);
        let specific2 = Clause::new(vec![Literal::new(true, p_ab)]);

        assert!(subsumes(&general, &specific1));
        assert!(!subsumes(&general, &specific2));
    }

    #[test]
    fn forward_subsumption_check() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        let p_x = make_pred(&table, "P", vec![x]);
        let p_a = make_pred(&table, "P", vec![a]);

        let general = Clause::new(vec![Literal::new(true, p_x)]);
        let specific = Clause::new(vec![Literal::new(true, p_a)]);

        assert!(forward_subsumed(&specific, &[&general]));
        assert!(!forward_subsumed(&general, &[&specific]));
    }

    #[test]
    fn back_subsumption_check() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        let p_x = make_pred(&table, "P", vec![x]);
        let p_a = make_pred(&table, "P", vec![a]);
        let p_b = make_pred(&table, "P", vec![b]);

        let general = Clause::new(vec![Literal::new(true, p_x)]);
        let specific1 = Clause::new(vec![Literal::new(true, p_a)]);
        let specific2 = Clause::new(vec![Literal::new(true, p_b)]);

        let subsumed = back_subsumed(&general, &[&specific1, &specific2]);
        assert_eq!(subsumed.len(), 2);
    }
}
