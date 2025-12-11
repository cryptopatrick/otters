//! Unit deletion inference rule.
//!
//! Unit deletion simplifies clauses by removing literals that are complementary
//! to existing unit clauses. This is essentially binary resolution with a unit
//! clause where we delete a literal rather than produce a resolvent.
//!
//! Example: Given clause `P(x) | Q(x)` and unit clause `~P(a)`,
//! unit deletion produces `Q(a)` by deleting the `P(x)` literal.

use crate::data::{Clause, ClauseId, Literal};
use crate::inference::{apply_to_clause, apply_to_literal, rename_variables, unify};

/// Result of unit deletion on a clause.
#[derive(Debug, Clone)]
pub struct UnitDeleted {
    pub clause: Clause,
    pub parents: Vec<ClauseId>,
}

/// Attempt to delete literals from a clause using unit clauses.
///
/// For each literal in the target clause, checks if there exists a unit clause
/// with the opposite sign that unifies with it. If so, the literal is deleted
/// and the substitution is applied to the remaining literals.
///
/// # Arguments
/// * `clause` - The clause to simplify
/// * `clause_id` - Optional ID of the clause (for parent tracking)
/// * `units` - List of unit clauses to use for deletion
/// * `unit_ids` - Optional IDs corresponding to the units
///
/// # Returns
/// Some(UnitDeleted) if any deletions occurred, None otherwise
pub fn unit_delete(
    clause: &Clause,
    clause_id: Option<ClauseId>,
    units: &[Clause],
    unit_ids: &[Option<ClauseId>],
) -> Option<UnitDeleted> {
    // Only apply to multi-literal clauses
    if clause.literals.len() <= 1 {
        return None;
    }

    let mut current = clause.clone();
    let mut parents = clause_id.map(|id| vec![id]).unwrap_or_default();
    let mut deletions_made = false;

    // Keep trying to delete literals until no more can be deleted
    loop {
        let mut deleted_this_round = false;

        // Try each unit clause
        for (idx, unit) in units.iter().enumerate() {
            // Skip non-unit clauses
            if unit.literals.len() != 1 {
                continue;
            }

            let unit_lit = &unit.literals[0];

            // Try to find a literal in current clause with opposite sign
            let mut new_literals = Vec::new();
            let mut found_match = false;
            let mut substitution = None;

            for lit in &current.literals {
                // Check if opposite sign and atoms unify
                if lit.sign != unit_lit.sign {
                    if let Ok(subst) = unify(&lit.atom, &unit_lit.atom) {
                        // Found a match - delete this literal
                        found_match = true;
                        substitution = Some(subst);
                        deleted_this_round = true;
                        deletions_made = true;

                        // Add unit clause to parents
                        if let Some(unit_id) = unit_ids.get(idx).and_then(|id| *id) {
                            parents.push(unit_id);
                        }

                        // Don't add this literal to new_literals (delete it)
                        continue;
                    }
                }

                // Keep this literal
                new_literals.push(lit.clone());
            }

            // If we deleted a literal, apply substitution to remaining literals
            if found_match && !new_literals.is_empty() {
                if let Some(ref subst) = substitution {
                    new_literals = new_literals
                        .iter()
                        .map(|lit| apply_to_literal(subst, lit))
                        .collect();
                }

                // Update current clause with new literals
                current = Clause {
                    literals: new_literals,
                    ..current
                };

                // Break to restart from the beginning with the simplified clause
                break;
            } else if found_match && new_literals.is_empty() {
                // Deleted all literals - this shouldn't happen with unit deletion
                // but if it does, return a single-literal false clause
                return None;
            }
        }

        // If no deletions this round, we're done
        if !deleted_this_round {
            break;
        }
    }

    if deletions_made {
        // Rename variables to avoid conflicts
        let renamed = rename_variables(&current, 0);

        Some(UnitDeleted {
            clause: renamed,
            parents,
        })
    } else {
        None
    }
}

/// Forward unit deletion: simplify a clause using existing unit clauses.
///
/// This is the main entry point for unit deletion in the prover loop.
pub fn forward_unit_deletion(
    clause: &Clause,
    clause_id: Option<ClauseId>,
    usable_clauses: &[Clause],
    usable_ids: &[Option<ClauseId>],
) -> Option<UnitDeleted> {
    // Extract only unit clauses for efficiency
    let mut units = Vec::new();
    let mut unit_ids = Vec::new();

    for (idx, c) in usable_clauses.iter().enumerate() {
        if c.literals.len() == 1 {
            units.push(c.clone());
            unit_ids.push(usable_ids.get(idx).copied().flatten());
        }
    }

    if units.is_empty() {
        return None;
    }

    unit_delete(clause, clause_id, &units, &unit_ids)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{Literal, SymbolTable, Term, SymbolKind, VariableId};

    #[test]
    fn unit_delete_removes_matching_literal() {
        let symbols = SymbolTable::new();
        let p = symbols.intern("P", 1, SymbolKind::Predicate);
        let q = symbols.intern("Q", 1, SymbolKind::Predicate);
        let a = symbols.intern("a", 0, SymbolKind::Constant);

        // Clause: P(x) | Q(x)
        let clause = Clause {
            literals: vec![
                Literal::new(true, Term::application(p, vec![Term::variable(VariableId::new(0))])),
                Literal::new(true, Term::application(q, vec![Term::variable(VariableId::new(0))])),
            ],
            ..Default::default()
        };

        // Unit: ~P(a)
        let unit = Clause {
            literals: vec![
                Literal::new(false, Term::application(p, vec![Term::application(a, vec![])])),
            ],
            ..Default::default()
        };

        let result = unit_delete(&clause, None, &[unit], &[None]);
        assert!(result.is_some());

        let deleted = result.unwrap();
        // Should have Q(a) remaining
        assert_eq!(deleted.clause.literals.len(), 1);
    }

    #[test]
    fn unit_delete_requires_opposite_sign() {
        let symbols = SymbolTable::new();
        let p = symbols.intern("P", 1, SymbolKind::Predicate);
        let a = symbols.intern("a", 0, SymbolKind::Constant);

        // Clause: P(x) | Q(x)
        let clause = Clause {
            literals: vec![
                Literal::new(true, Term::application(p, vec![Term::variable(VariableId::new(0))])),
            ],
            ..Default::default()
        };

        // Unit: P(a) (same sign - should not delete)
        let unit = Clause {
            literals: vec![
                Literal::new(true, Term::application(p, vec![Term::application(a, vec![])])),
            ],
            ..Default::default()
        };

        let result = unit_delete(&clause, None, &[unit], &[None]);
        // Should not delete (same sign)
        assert!(result.is_none());
    }

    #[test]
    fn unit_delete_skips_unit_clauses() {
        let symbols = SymbolTable::new();
        let p = symbols.intern("P", 1, SymbolKind::Predicate);
        let a = symbols.intern("a", 0, SymbolKind::Constant);

        // Unit clause: P(a)
        let clause = Clause {
            literals: vec![
                Literal::new(true, Term::application(p, vec![Term::application(a, vec![])])),
            ],
            ..Default::default()
        };

        // Unit: ~P(a)
        let unit = Clause {
            literals: vec![
                Literal::new(false, Term::application(p, vec![Term::application(a, vec![])])),
            ],
            ..Default::default()
        };

        // Should not apply to unit clauses
        let result = unit_delete(&clause, None, &[unit], &[None]);
        assert!(result.is_none());
    }
}
