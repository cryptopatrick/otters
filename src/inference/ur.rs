//! UR-resolution (Unit-Resulting Resolution) inference rule.
//!
//! UR-resolution resolves a non-unit clause (nucleus) with n-1 unit clauses
//! (satellites) to produce a unit clause (single literal).
//!
//! Given:
//! - Nucleus: L1 | L2 | ... | Ln (where n > 1)
//! - Satellites: n-1 unit clauses that resolve with n-1 literals in the nucleus
//! - Result: A single literal (unit clause)
//!
//! Example:
//!   Nucleus:    -P(x) | -Q(x) | R(x)
//!   Satellite1:  P(a)
//!   Satellite2:  Q(a)
//!   Resolvent:   R(a)

use crate::data::{Clause, ClauseId, Literal, Term, VariableId};
use crate::inference::{Substitution, Unifier};

/// Result of a UR-resolution step.
#[derive(Clone, Debug)]
pub struct URResolvent {
    /// The resulting unit clause (single literal)
    pub clause: Clause,
    /// The nucleus clause ID
    pub nucleus_id: Option<ClauseId>,
    /// The satellite clause IDs used (in order matching nucleus literals)
    pub satellite_ids: Vec<Option<ClauseId>>,
    /// The combined substitution
    pub substitution: Substitution,
}

/// Rename variables in a term by adding an offset.
fn rename_term(term: &Term, offset: u16) -> Term {
    match term {
        Term::Variable { id, symbol } => Term::Variable {
            id: VariableId::new(id.as_u16() + offset),
            symbol: *symbol,
        },
        Term::Application { symbol, args } => {
            let new_args = args.iter().map(|a| rename_term(a, offset)).collect();
            Term::Application {
                symbol: *symbol,
                args: new_args,
            }
        }
    }
}

/// Rename variables in a literal.
fn rename_literal(lit: &Literal, offset: u16) -> Literal {
    Literal::new(lit.sign, rename_term(&lit.atom, offset)).with_target(lit.target)
}

/// Apply a substitution to a literal.
fn apply_subst_to_literal(lit: &Literal, subst: &Substitution) -> Literal {
    Literal::new(lit.sign, subst.apply(&lit.atom)).with_target(lit.target)
}

/// Perform UR-resolution with unit clauses.
///
/// Given a nucleus (non-unit clause) and a set of unit clause satellites,
/// attempt to resolve all but one literal in the nucleus, producing a unit clause.
///
/// # Arguments
/// * `nucleus` - The multi-literal clause
/// * `nucleus_id` - Optional ID of the nucleus clause
/// * `satellites` - Available unit clauses to use as satellites
/// * `satellite_ids` - Optional IDs corresponding to satellites
///
/// # Returns
/// A vector of UR-resolvents (unit clauses) generated.
pub fn ur_resolve(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
) -> Vec<URResolvent> {
    let mut results = Vec::new();

    // UR-resolution only applies to non-unit clauses
    if nucleus.literals.len() <= 1 {
        return results;
    }

    // Filter satellites to only unit clauses
    let unit_satellites: Vec<(usize, &Clause)> = satellites
        .iter()
        .enumerate()
        .filter(|(_, c)| c.literals.len() == 1)
        .collect();

    if unit_satellites.is_empty() {
        return results;
    }

    // Try leaving each literal in the nucleus unresolved
    for keep_idx in 0..nucleus.literals.len() {
        let kept_literal = &nucleus.literals[keep_idx];

        // Collect the literals that need to be resolved (all except keep_idx)
        let resolve_literals: Vec<(usize, &Literal)> = nucleus
            .literals
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != keep_idx)
            .collect();

        // Try to find satellites for all resolve_literals
        if let Some(resolvent) = try_ur_resolve_keeping(
            kept_literal,
            &resolve_literals,
            &unit_satellites,
            nucleus_id,
            satellite_ids,
        ) {
            results.push(resolvent);
        }
    }

    results
}

/// Attempt UR-resolution keeping one specific literal.
fn try_ur_resolve_keeping(
    kept_literal: &Literal,
    resolve_literals: &[(usize, &Literal)],
    unit_satellites: &[(usize, &Clause)],
    nucleus_id: Option<ClauseId>,
    satellite_ids: &[Option<ClauseId>],
) -> Option<URResolvent> {
    // We need to find unit satellites that resolve with each of resolve_literals
    // Start with an empty substitution
    let mut current_subst = Substitution::new();
    let mut used_satellites = Vec::new();
    let mut var_offset = 100; // Offset for renaming satellite variables

    // Try to resolve each literal in resolve_literals
    for (_, nucleus_lit) in resolve_literals {
        // Find a satellite that resolves with this literal
        let mut found = false;

        for (sat_idx, satellite) in unit_satellites {
            // Skip if already used
            if used_satellites.contains(sat_idx) {
                continue;
            }

            let sat_lit = &satellite.literals[0];

            // Can only resolve if signs are opposite
            if sat_lit.sign == nucleus_lit.sign {
                continue;
            }

            // Rename satellite variables to avoid conflicts
            let renamed_sat_lit = rename_literal(sat_lit, var_offset);
            var_offset += 100;

            // Try to unify
            let mut unifier = Unifier::new();
            if unifier
                .unify(&nucleus_lit.atom, &renamed_sat_lit.atom)
                .is_ok()
            {
                // Compose the new substitution with the current one
                let new_subst = unifier.substitution().clone();
                current_subst = current_subst.compose(&new_subst);

                used_satellites.push(*sat_idx);
                found = true;
                break;
            }
        }

        if !found {
            // Could not resolve this literal, fail
            return None;
        }
    }

    // All literals except kept_literal were resolved
    // Apply the final substitution to the kept literal
    let result_literal = apply_subst_to_literal(kept_literal, &current_subst);

    // Build the satellite IDs list
    let result_satellite_ids: Vec<Option<ClauseId>> = used_satellites
        .iter()
        .map(|&idx| satellite_ids.get(idx).copied().flatten())
        .collect();

    Some(URResolvent {
        clause: Clause::new(vec![result_literal]),
        nucleus_id,
        satellite_ids: result_satellite_ids,
        substitution: current_subst,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{SymbolId, SymbolKind, SymbolTable, Term};

    fn make_var(offset: u16) -> Term {
        Term::Variable {
            id: VariableId::new(offset),
            symbol: None,
        }
    }

    fn make_const(table: &SymbolTable, name: &str) -> Term {
        let sym = table.intern(name, 0, SymbolKind::Constant);
        Term::Application {
            symbol: sym,
            args: vec![],
        }
    }

    fn make_pred(table: &SymbolTable, name: &str, args: Vec<Term>) -> Literal {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Predicate);
        Literal::new(
            true,
            Term::Application {
                symbol: sym,
                args,
            },
        )
    }

    #[test]
    fn test_ur_simple() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        // Nucleus: -P(x) | -Q(x) | R(x)
        let nucleus = Clause::new(vec![
            Literal::new(false, make_pred(&table, "P", vec![x.clone()]).atom),
            Literal::new(false, make_pred(&table, "Q", vec![x.clone()]).atom),
            make_pred(&table, "R", vec![x.clone()]),
        ]);

        // Satellites: P(a), Q(a)
        let satellites = vec![
            Clause::new(vec![make_pred(&table, "P", vec![a.clone()])]),
            Clause::new(vec![make_pred(&table, "Q", vec![a.clone()])]),
        ];

        let resolvents = ur_resolve(&nucleus, None, &satellites, &[None, None]);

        assert!(!resolvents.is_empty(), "Should produce UR-resolvents");
        // Should produce R(a)
        assert_eq!(resolvents[0].clause.literals.len(), 1);
    }

    #[test]
    fn test_ur_no_units() {
        let table = SymbolTable::new();
        let x = make_var(0);

        // Nucleus: -P(x) | Q(x)
        let nucleus = Clause::new(vec![
            Literal::new(false, make_pred(&table, "P", vec![x.clone()]).atom),
            make_pred(&table, "Q", vec![x]),
        ]);

        // Satellites: P(a) | Q(b) (not a unit clause)
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");
        let satellites = vec![Clause::new(vec![
            make_pred(&table, "P", vec![a]),
            make_pred(&table, "Q", vec![b]),
        ])];

        let resolvents = ur_resolve(&nucleus, None, &satellites, &[None]);

        assert!(
            resolvents.is_empty(),
            "Should not produce resolvents with non-unit satellites"
        );
    }

    #[test]
    fn test_ur_unit_nucleus() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        // Nucleus: P(a) (unit clause)
        let nucleus = Clause::new(vec![make_pred(&table, "P", vec![a.clone()])]);

        // Satellites: -P(a)
        let satellites = vec![Clause::new(vec![Literal::new(
            false,
            make_pred(&table, "P", vec![a]).atom,
        )])];

        let resolvents = ur_resolve(&nucleus, None, &satellites, &[None]);

        assert!(
            resolvents.is_empty(),
            "UR-resolution should not apply to unit nucleus"
        );
    }
}
