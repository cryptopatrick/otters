//! Resolution inference rule for clause-based theorem proving.

use crate::data::{Clause, ClauseId, Literal, Term, VariableId};
use crate::inference::{Substitution, UnificationError, Unifier};

/// Result of a resolution attempt.
#[derive(Clone, Debug)]
pub struct Resolvent {
    /// The resulting clause after resolution
    pub clause: Clause,
    /// Index of literal in first clause that was resolved
    pub lit1_index: usize,
    /// Index of literal in second clause that was resolved
    pub lit2_index: usize,
    /// The unifying substitution used
    pub substitution: Substitution,
}

/// Apply a substitution to a literal.
pub fn apply_to_literal(subst: &Substitution, lit: &Literal) -> Literal {
    Literal::new(lit.sign, subst.apply(&lit.atom)).with_target(lit.target)
}

/// Apply a substitution to a clause.
pub fn apply_to_clause(subst: &Substitution, clause: &Clause) -> Clause {
    let new_literals = clause
        .literals
        .iter()
        .map(|lit| apply_to_literal(subst, lit))
        .collect();

    let mut new_clause = Clause::new(new_literals);
    new_clause.pick_weight = clause.pick_weight;
    new_clause.heat_level = clause.heat_level;
    // Copy attributes but not parents or id
    new_clause.attributes = clause.attributes.clone();
    new_clause
}

/// Rename variables in a clause to avoid conflicts.
///
/// Adds an offset to all variable IDs to make them distinct from another clause.
pub fn rename_variables(clause: &Clause, offset: u16) -> Clause {
    let new_literals = clause
        .literals
        .iter()
        .map(|lit| {
            Literal::new(lit.sign, rename_term_variables(&lit.atom, offset))
                .with_target(lit.target)
        })
        .collect();

    let mut new_clause = Clause::new(new_literals);
    new_clause.pick_weight = clause.pick_weight;
    new_clause.heat_level = clause.heat_level;
    new_clause.attributes = clause.attributes.clone();
    new_clause
}

fn rename_term_variables(term: &Term, offset: u16) -> Term {
    match term {
        Term::Variable { id, symbol } => {
            Term::Variable {
                id: VariableId::new(id.as_u16() + offset),
                symbol: *symbol,
            }
        }
        Term::Application { symbol, args } => {
            let new_args = args
                .iter()
                .map(|arg| rename_term_variables(arg, offset))
                .collect();
            Term::Application { symbol: *symbol, args: new_args }
        }
    }
}

/// Attempt binary resolution between two clauses.
///
/// Tries to resolve clause1's literal at lit1_index with clause2's literal at lit2_index.
/// Returns the resolvent if the literals have opposite signs and their atoms unify.
pub fn binary_resolve(
    clause1: &Clause,
    lit1_index: usize,
    clause2: &Clause,
    lit2_index: usize,
    parent1_id: Option<ClauseId>,
    parent2_id: Option<ClauseId>,
) -> Result<Resolvent, UnificationError> {
    let lit1 = &clause1.literals[lit1_index];
    let lit2 = &clause2.literals[lit2_index];

    // Literals must have opposite signs to resolve
    if lit1.sign == lit2.sign {
        return Err(UnificationError::SymbolClash {
            expected: lit1.atom.clone(),
            found: lit2.atom.clone(),
        });
    }

    // Try to unify the atoms
    let mut unifier = Unifier::new();
    unifier.unify(&lit1.atom, &lit2.atom)?;
    let subst = unifier.into_substitution();

    // Build the resolvent by combining non-resolved literals
    let mut new_literals = Vec::new();

    // Add literals from clause1 (except the resolved one)
    for (i, lit) in clause1.literals.iter().enumerate() {
        if i != lit1_index {
            new_literals.push(apply_to_literal(&subst, lit));
        }
    }

    // Add literals from clause2 (except the resolved one)
    for (i, lit) in clause2.literals.iter().enumerate() {
        if i != lit2_index {
            new_literals.push(apply_to_literal(&subst, lit));
        }
    }

    let mut resolvent_clause = Clause::new(new_literals);

    // Add parent information
    if let Some(id) = parent1_id {
        resolvent_clause.add_parent(id);
    }
    if let Some(id) = parent2_id {
        resolvent_clause.add_parent(id);
    }

    Ok(Resolvent {
        clause: resolvent_clause,
        lit1_index,
        lit2_index,
        substitution: subst,
    })
}

/// Find all possible resolvents between two clauses.
///
/// Returns all clause pairs where resolution is possible.
pub fn all_resolvents(
    clause1: &Clause,
    clause2: &Clause,
    parent1_id: Option<ClauseId>,
    parent2_id: Option<ClauseId>,
) -> Vec<Resolvent> {
    let mut results = Vec::new();

    // Rename variables in clause2 to avoid conflicts
    let clause2_renamed = rename_variables(clause2, 100);

    for i in 0..clause1.literals.len() {
        for j in 0..clause2_renamed.literals.len() {
            if let Ok(resolvent) = binary_resolve(
                clause1,
                i,
                &clause2_renamed,
                j,
                parent1_id,
                parent2_id,
            ) {
                results.push(resolvent);
            }
        }
    }

    results
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
    fn resolve_simple_clauses() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        // Clause 1: P(a)
        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let clause1 = Clause::new(vec![Literal::new(true, p_a)]);

        // Clause 2: -P(x)
        let x = make_var(0);
        let p_x = make_pred(&table, "P", vec![x]);
        let clause2 = Clause::new(vec![Literal::new(false, p_x)]);

        let result = binary_resolve(&clause1, 0, &clause2, 0, None, None);
        assert!(result.is_ok());

        let resolvent = result.unwrap();
        // Should produce empty clause
        assert!(resolvent.clause.literals.is_empty());
    }

    #[test]
    fn resolve_with_remaining_literals() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // Clause 1: P(a) | Q(b)
        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let q_b = make_pred(&table, "Q", vec![b.clone()]);
        let clause1 = Clause::new(vec![
            Literal::new(true, p_a),
            Literal::new(true, q_b.clone()),
        ]);

        // Clause 2: -P(x) | R(x)
        let x = make_var(0);
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let r_x = make_pred(&table, "R", vec![x]);
        let clause2 = Clause::new(vec![
            Literal::new(false, p_x),
            Literal::new(true, r_x),
        ]);

        let result = binary_resolve(&clause1, 0, &clause2, 0, None, None);
        assert!(result.is_ok());

        let resolvent = result.unwrap();
        // Should produce: Q(b) | R(a)
        assert_eq!(resolvent.clause.literals.len(), 2);
    }

    #[test]
    fn resolve_same_sign_fails() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        // Both positive
        let p_a = make_pred(&table, "P", vec![a]);
        let clause1 = Clause::new(vec![Literal::new(true, p_a.clone())]);
        let clause2 = Clause::new(vec![Literal::new(true, p_a)]);

        let result = binary_resolve(&clause1, 0, &clause2, 0, None, None);
        assert!(result.is_err());
    }

    #[test]
    fn resolve_non_unifiable_fails() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        // P(a) and -P(b) don't unify
        let p_a = make_pred(&table, "P", vec![a]);
        let p_b = make_pred(&table, "P", vec![b]);
        let clause1 = Clause::new(vec![Literal::new(true, p_a)]);
        let clause2 = Clause::new(vec![Literal::new(false, p_b)]);

        let result = binary_resolve(&clause1, 0, &clause2, 0, None, None);
        assert!(result.is_err());
    }

    #[test]
    fn all_resolvents_finds_multiple() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let y = make_var(1);

        // Clause 1: P(x) | Q(x)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_x = make_pred(&table, "Q", vec![x]);
        let clause1 = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(true, q_x),
        ]);

        // Clause 2: -P(y) | -Q(y)
        let p_y = make_pred(&table, "P", vec![y.clone()]);
        let q_y = make_pred(&table, "Q", vec![y]);
        let clause2 = Clause::new(vec![
            Literal::new(false, p_y),
            Literal::new(false, q_y),
        ]);

        let resolvents = all_resolvents(&clause1, &clause2, None, None);
        // Should find 2 resolvents: P with -P, Q with -Q
        assert_eq!(resolvents.len(), 2);
    }

    #[test]
    fn rename_variables_works() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let p_x = make_pred(&table, "P", vec![x]);
        let clause = Clause::new(vec![Literal::new(true, p_x)]);

        let renamed = rename_variables(&clause, 100);

        // Variable should now be 100
        match &renamed.literals[0].atom {
            Term::Application { args, .. } => {
                match &args[0] {
                    Term::Variable { id, .. } => {
                        assert_eq!(id.as_u16(), 100);
                    }
                    _ => panic!("expected variable"),
                }
            }
            _ => panic!("expected application"),
        }
    }

    #[test]
    fn substitution_applied_correctly() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        let mut subst = Substitution::new();
        subst.bind(VariableId::new(0), a.clone());

        let p_x = make_pred(&table, "P", vec![x]);
        let lit = Literal::new(true, p_x);

        let applied = apply_to_literal(&subst, &lit);

        // Should be P(a)
        match &applied.atom {
            Term::Application { args, .. } => {
                assert_eq!(args[0], a);
            }
            _ => panic!("expected application"),
        }
    }
}
