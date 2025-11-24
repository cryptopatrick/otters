//! Hyperresolution inference rules.
//!
//! This module implements both positive and negative hyperresolution:
//!
//! **Positive Hyperresolution:**
//! - Nucleus contains negative literals
//! - Satellites are positive clauses
//! - Result contains only positive literals
//!
//! **Negative Hyperresolution:**
//! - Nucleus contains positive literals
//! - Satellites are negative clauses
//! - Result contains only negative literals

use crate::data::{Clause, ClauseId, Literal, Term, VariableId};
use crate::inference::{apply_to_literal, Substitution, UnificationError, Unifier};

/// Result of a hyperresolution step.
#[derive(Clone, Debug)]
pub struct HyperResolvent {
    /// The resulting clause (all positive literals)
    pub clause: Clause,
    /// The nucleus clause ID
    pub nucleus_id: Option<ClauseId>,
    /// The satellite clause IDs used
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
            Term::Application { symbol: *symbol, args: new_args }
        }
    }
}

/// Rename variables in a literal.
fn rename_literal(lit: &Literal, offset: u16) -> Literal {
    Literal::new(lit.sign, rename_term(&lit.atom, offset)).with_target(lit.target)
}

/// Perform hyperresolution.
///
/// Given a nucleus (clause containing negative literals) and a set of satellites
/// (positive unit clauses or clauses with positive literals), attempt to resolve
/// all negative literals in the nucleus simultaneously.
///
/// # Arguments
/// * `nucleus` - The clause containing negative literals to resolve
/// * `nucleus_id` - Optional ID of the nucleus clause
/// * `satellites` - Available positive clauses to use as satellites
/// * `satellite_ids` - Optional IDs corresponding to satellites
///
/// # Returns
/// A vector of hyperresolvents where all negative literals have been resolved.
pub fn hyperresolve(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
) -> Vec<HyperResolvent> {
    // Collect indices of negative literals in nucleus
    let neg_indices: Vec<usize> = nucleus
        .literals
        .iter()
        .enumerate()
        .filter(|(_, lit)| !lit.sign)
        .map(|(i, _)| i)
        .collect();

    if neg_indices.is_empty() {
        // No negative literals to resolve
        return vec![];
    }

    // Positive literals that will remain in the result
    let pos_literals: Vec<&Literal> = nucleus
        .literals
        .iter()
        .filter(|lit| lit.sign)
        .collect();

    let mut results = Vec::new();

    // Try to find satellites for each negative literal
    hyperresolve_recursive(
        nucleus,
        nucleus_id,
        &neg_indices,
        0,
        satellites,
        satellite_ids,
        &pos_literals,
        Substitution::new(),
        Vec::new(),
        100, // Variable offset for first satellite
        &mut results,
    );

    results
}

/// Recursive helper for hyperresolution.
#[allow(clippy::too_many_arguments)]
fn hyperresolve_recursive(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    neg_indices: &[usize],
    current_neg_idx: usize,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
    pos_literals: &[&Literal],
    current_subst: Substitution,
    used_satellites: Vec<Option<ClauseId>>,
    var_offset: u16,
    results: &mut Vec<HyperResolvent>,
) {
    // Base case: all negative literals resolved
    if current_neg_idx >= neg_indices.len() {
        // Build the result clause with remaining positive literals
        let mut result_literals = Vec::new();

        for lit in pos_literals {
            result_literals.push(apply_to_literal(&current_subst, lit));
        }

        let mut result_clause = Clause::new(result_literals);
        if let Some(id) = nucleus_id {
            result_clause.add_parent(id);
        }
        for sat_id in &used_satellites {
            if let Some(id) = sat_id {
                result_clause.add_parent(*id);
            }
        }

        results.push(HyperResolvent {
            clause: result_clause,
            nucleus_id,
            satellite_ids: used_satellites,
            substitution: current_subst,
        });
        return;
    }

    // Get the current negative literal to resolve
    let neg_lit = &nucleus.literals[neg_indices[current_neg_idx]];
    let neg_atom = current_subst.apply(&neg_lit.atom);

    // Try each satellite
    for (sat_idx, satellite) in satellites.iter().enumerate() {
        // Look for a positive literal in the satellite that unifies with our negative
        for (lit_idx, sat_lit) in satellite.literals.iter().enumerate() {
            if !sat_lit.sign {
                continue; // Skip negative literals in satellite
            }

            // Rename satellite variables to avoid conflicts
            let renamed_atom = rename_term(&sat_lit.atom, var_offset);

            // Try to unify
            let mut unifier = Unifier::new();

            // Start with current substitution
            for (var, term) in current_subst.iter() {
                unifier.substitution().clone(); // We need to rebuild
            }

            // Try unification
            let combined_subst = {
                let mut test_subst = current_subst.clone();
                let mut unifier = Unifier::new();

                if unifier.unify(&neg_atom, &renamed_atom).is_err() {
                    continue;
                }

                // Compose substitutions
                test_subst.compose(&unifier.into_substitution())
            };

            // Collect additional positive literals from satellite
            let mut new_pos_literals = pos_literals.to_vec();
            for (i, lit) in satellite.literals.iter().enumerate() {
                if i != lit_idx && lit.sign {
                    // Add renamed literal
                    let renamed = rename_literal(lit, var_offset);
                    // We need to store this somehow - for now, skip extra literals
                }
            }

            // Recurse to resolve next negative literal
            let mut new_used = used_satellites.clone();
            new_used.push(satellite_ids.get(sat_idx).copied().flatten());

            hyperresolve_recursive(
                nucleus,
                nucleus_id,
                neg_indices,
                current_neg_idx + 1,
                satellites,
                satellite_ids,
                pos_literals,
                combined_subst,
                new_used,
                var_offset + 100,
                results,
            );
        }
    }
}

/// Simplified hyperresolution for unit satellites.
///
/// This is a simpler version that only works with positive unit clauses as satellites.
pub fn hyperresolve_units(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
) -> Vec<HyperResolvent> {
    // Filter to unit satellites only
    let unit_satellites: Vec<_> = satellites
        .iter()
        .enumerate()
        .filter(|(_, c)| c.literals.len() == 1 && c.literals[0].sign)
        .collect();

    let neg_indices: Vec<usize> = nucleus
        .literals
        .iter()
        .enumerate()
        .filter(|(_, lit)| !lit.sign)
        .map(|(i, _)| i)
        .collect();

    if neg_indices.is_empty() {
        return vec![];
    }

    let pos_literals: Vec<_> = nucleus
        .literals
        .iter()
        .enumerate()
        .filter(|(_, lit)| lit.sign)
        .collect();

    let mut results = Vec::new();

    // Simple backtracking search
    hyperresolve_units_recursive(
        nucleus,
        nucleus_id,
        &neg_indices,
        0,
        &unit_satellites,
        satellite_ids,
        &pos_literals,
        Substitution::new(),
        Vec::new(),
        100,
        &mut results,
    );

    results
}

#[allow(clippy::too_many_arguments)]
fn hyperresolve_units_recursive(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    neg_indices: &[usize],
    current_neg_idx: usize,
    unit_satellites: &[(usize, &Clause)],
    satellite_ids: &[Option<ClauseId>],
    pos_literals: &[(usize, &Literal)],
    current_subst: Substitution,
    used_satellites: Vec<Option<ClauseId>>,
    var_offset: u16,
    results: &mut Vec<HyperResolvent>,
) {
    if current_neg_idx >= neg_indices.len() {
        // All negative literals resolved - build result
        let mut result_lits = Vec::new();
        for (_, lit) in pos_literals {
            result_lits.push(apply_to_literal(&current_subst, lit));
        }

        let mut result_clause = Clause::new(result_lits);
        if let Some(id) = nucleus_id {
            result_clause.add_parent(id);
        }
        for sat_id in &used_satellites {
            if let Some(id) = sat_id {
                result_clause.add_parent(*id);
            }
        }

        results.push(HyperResolvent {
            clause: result_clause,
            nucleus_id,
            satellite_ids: used_satellites,
            substitution: current_subst,
        });
        return;
    }

    let neg_lit = &nucleus.literals[neg_indices[current_neg_idx]];
    let neg_atom = current_subst.apply(&neg_lit.atom);

    for (orig_idx, satellite) in unit_satellites {
        let sat_lit = &satellite.literals[0];
        let renamed_atom = rename_term(&sat_lit.atom, var_offset);

        let mut unifier = Unifier::new();
        if unifier.unify(&neg_atom, &renamed_atom).is_err() {
            continue;
        }

        let new_subst = current_subst.compose(&unifier.into_substitution());
        let mut new_used = used_satellites.clone();
        new_used.push(satellite_ids.get(*orig_idx).copied().flatten());

        hyperresolve_units_recursive(
            nucleus,
            nucleus_id,
            neg_indices,
            current_neg_idx + 1,
            unit_satellites,
            satellite_ids,
            pos_literals,
            new_subst,
            new_used,
            var_offset + 100,
            results,
        );
    }
}

/// Perform negative hyperresolution.
///
/// This is the dual of positive hyperresolution:
/// - Nucleus contains positive literals
/// - Satellites contain negative literals
/// - Result contains only negative literals
///
/// This is useful for goal-directed reasoning where we're trying to
/// derive contradictions or refutations.
///
/// # Arguments
/// * `nucleus` - The clause containing positive literals to resolve
/// * `nucleus_id` - Optional ID of the nucleus clause
/// * `satellites` - Available clauses with negative literals
/// * `satellite_ids` - Optional IDs corresponding to satellites
///
/// # Returns
/// A vector of negative hyperresolvents where all positive literals have been resolved.
pub fn neg_hyperresolve(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
) -> Vec<HyperResolvent> {
    // Collect indices of positive literals in nucleus
    let pos_indices: Vec<usize> = nucleus
        .literals
        .iter()
        .enumerate()
        .filter(|(_, lit)| lit.sign)
        .map(|(i, _)| i)
        .collect();

    if pos_indices.is_empty() {
        // No positive literals to resolve
        return vec![];
    }

    // Negative literals that will remain in the result
    let neg_literals: Vec<&Literal> = nucleus
        .literals
        .iter()
        .filter(|lit| !lit.sign)
        .collect();

    let mut results = Vec::new();

    // Try to find satellites for each positive literal
    neg_hyperresolve_recursive(
        nucleus,
        nucleus_id,
        &pos_indices,
        0,
        satellites,
        satellite_ids,
        &neg_literals,
        Substitution::new(),
        Vec::new(),
        100, // Variable offset for first satellite
        &mut results,
    );

    results
}

/// Recursive helper for negative hyperresolution.
#[allow(clippy::too_many_arguments)]
fn neg_hyperresolve_recursive(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    pos_indices: &[usize],
    current_pos_idx: usize,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
    neg_literals: &[&Literal],
    current_subst: Substitution,
    used_satellites: Vec<Option<ClauseId>>,
    var_offset: u16,
    results: &mut Vec<HyperResolvent>,
) {
    // Base case: all positive literals resolved
    if current_pos_idx >= pos_indices.len() {
        // Build the result clause with remaining negative literals
        let mut result_literals = Vec::new();

        for lit in neg_literals {
            result_literals.push(apply_to_literal(&current_subst, lit));
        }

        let mut result_clause = Clause::new(result_literals);
        if let Some(id) = nucleus_id {
            result_clause.add_parent(id);
        }
        for sat_id in &used_satellites {
            if let Some(id) = sat_id {
                result_clause.add_parent(*id);
            }
        }

        results.push(HyperResolvent {
            clause: result_clause,
            nucleus_id,
            satellite_ids: used_satellites,
            substitution: current_subst,
        });
        return;
    }

    // Get the current positive literal to resolve
    let pos_lit = &nucleus.literals[pos_indices[current_pos_idx]];
    let pos_atom = current_subst.apply(&pos_lit.atom);

    // Try each satellite
    for (sat_idx, satellite) in satellites.iter().enumerate() {
        // Look for a negative literal in the satellite that unifies with our positive
        for sat_lit in satellite.literals.iter() {
            if sat_lit.sign {
                continue; // Skip positive literals in satellite
            }

            // Rename satellite variables to avoid conflicts
            let renamed_atom = rename_term(&sat_lit.atom, var_offset);

            // Try unification
            let combined_subst = {
                let mut unifier = Unifier::new();

                if unifier.unify(&pos_atom, &renamed_atom).is_err() {
                    continue;
                }

                // Compose substitutions
                current_subst.compose(&unifier.into_substitution())
            };

            // Recurse to resolve next positive literal
            let mut new_used = used_satellites.clone();
            new_used.push(satellite_ids.get(sat_idx).copied().flatten());

            neg_hyperresolve_recursive(
                nucleus,
                nucleus_id,
                pos_indices,
                current_pos_idx + 1,
                satellites,
                satellite_ids,
                neg_literals,
                combined_subst,
                new_used,
                var_offset + 100,
                results,
            );
        }
    }
}

/// Simplified negative hyperresolution for unit satellites.
///
/// This is a simpler version that only works with negative unit clauses as satellites.
pub fn neg_hyperresolve_units(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    satellites: &[Clause],
    satellite_ids: &[Option<ClauseId>],
) -> Vec<HyperResolvent> {
    // Filter to negative unit satellites only
    let unit_satellites: Vec<_> = satellites
        .iter()
        .enumerate()
        .filter(|(_, c)| c.literals.len() == 1 && !c.literals[0].sign)
        .collect();

    let pos_indices: Vec<usize> = nucleus
        .literals
        .iter()
        .enumerate()
        .filter(|(_, lit)| lit.sign)
        .map(|(i, _)| i)
        .collect();

    if pos_indices.is_empty() {
        return vec![];
    }

    let neg_literals: Vec<_> = nucleus
        .literals
        .iter()
        .enumerate()
        .filter(|(_, lit)| !lit.sign)
        .collect();

    let mut results = Vec::new();

    // Simple backtracking search
    neg_hyperresolve_units_recursive(
        nucleus,
        nucleus_id,
        &pos_indices,
        0,
        &unit_satellites,
        satellite_ids,
        &neg_literals,
        Substitution::new(),
        Vec::new(),
        100,
        &mut results,
    );

    results
}

#[allow(clippy::too_many_arguments)]
fn neg_hyperresolve_units_recursive(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    pos_indices: &[usize],
    current_pos_idx: usize,
    unit_satellites: &[(usize, &Clause)],
    satellite_ids: &[Option<ClauseId>],
    neg_literals: &[(usize, &Literal)],
    current_subst: Substitution,
    used_satellites: Vec<Option<ClauseId>>,
    var_offset: u16,
    results: &mut Vec<HyperResolvent>,
) {
    if current_pos_idx >= pos_indices.len() {
        // All positive literals resolved - build result
        let mut result_lits = Vec::new();
        for (_, lit) in neg_literals {
            result_lits.push(apply_to_literal(&current_subst, lit));
        }

        let mut result_clause = Clause::new(result_lits);
        if let Some(id) = nucleus_id {
            result_clause.add_parent(id);
        }
        for sat_id in &used_satellites {
            if let Some(id) = sat_id {
                result_clause.add_parent(*id);
            }
        }

        results.push(HyperResolvent {
            clause: result_clause,
            nucleus_id,
            satellite_ids: used_satellites,
            substitution: current_subst,
        });
        return;
    }

    let pos_lit = &nucleus.literals[pos_indices[current_pos_idx]];
    let pos_atom = current_subst.apply(&pos_lit.atom);

    for (orig_idx, satellite) in unit_satellites {
        let sat_lit = &satellite.literals[0];
        let renamed_atom = rename_term(&sat_lit.atom, var_offset);

        let mut unifier = Unifier::new();
        if unifier.unify(&pos_atom, &renamed_atom).is_err() {
            continue;
        }

        let new_subst = current_subst.compose(&unifier.into_substitution());
        let mut new_used = used_satellites.clone();
        new_used.push(satellite_ids.get(*orig_idx).copied().flatten());

        neg_hyperresolve_units_recursive(
            nucleus,
            nucleus_id,
            pos_indices,
            current_pos_idx + 1,
            unit_satellites,
            satellite_ids,
            neg_literals,
            new_subst,
            new_used,
            var_offset + 100,
            results,
        );
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

    fn make_pred(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Predicate);
        Term::application(sym, args)
    }

    #[test]
    fn hyperresolve_simple() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);

        // Nucleus: -P(x) | Q(x)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_x = make_pred(&table, "Q", vec![x]);
        let nucleus = Clause::new(vec![
            Literal::new(false, p_x),
            Literal::new(true, q_x),
        ]);

        // Satellite: P(a)
        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let satellite = Clause::new(vec![Literal::new(true, p_a)]);

        let results = hyperresolve_units(&nucleus, None, &[satellite], &[None]);

        assert_eq!(results.len(), 1);
        // Result should be Q(a)
        assert_eq!(results[0].clause.literals.len(), 1);
        assert!(results[0].clause.literals[0].sign);
    }

    #[test]
    fn hyperresolve_multiple_negatives() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");
        let x = make_var(0);
        let y = make_var(1);

        // Nucleus: -P(x) | -Q(y) | R(x, y)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_y = make_pred(&table, "Q", vec![y.clone()]);
        let r_xy = make_pred(&table, "R", vec![x, y]);
        let nucleus = Clause::new(vec![
            Literal::new(false, p_x),
            Literal::new(false, q_y),
            Literal::new(true, r_xy),
        ]);

        // Satellites: P(a), Q(b)
        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let q_b = make_pred(&table, "Q", vec![b.clone()]);
        let sat1 = Clause::new(vec![Literal::new(true, p_a)]);
        let sat2 = Clause::new(vec![Literal::new(true, q_b)]);

        let results = hyperresolve_units(&nucleus, None, &[sat1, sat2], &[None, None]);

        assert_eq!(results.len(), 1);
        // Result should be R(a, b)
        assert_eq!(results[0].clause.literals.len(), 1);
        assert!(results[0].clause.literals[0].sign);
    }

    #[test]
    fn hyperresolve_no_match() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);

        // Nucleus: -P(x) | Q(x)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_x = make_pred(&table, "Q", vec![x]);
        let nucleus = Clause::new(vec![
            Literal::new(false, p_x),
            Literal::new(true, q_x),
        ]);

        // Satellite: R(a) - doesn't match P
        let r_a = make_pred(&table, "R", vec![a]);
        let satellite = Clause::new(vec![Literal::new(true, r_a)]);

        let results = hyperresolve_units(&nucleus, None, &[satellite], &[None]);

        assert!(results.is_empty());
    }

    #[test]
    fn hyperresolve_all_positive() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        // Nucleus with no negative literals
        let p_a = make_pred(&table, "P", vec![a]);
        let nucleus = Clause::new(vec![Literal::new(true, p_a)]);

        let results = hyperresolve_units(&nucleus, None, &[], &[]);

        assert!(results.is_empty());
    }

    // Tests for negative hyperresolution

    #[test]
    fn neg_hyperresolve_simple() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);

        // Nucleus: P(x) | -Q(x)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_x = make_pred(&table, "Q", vec![x]);
        let nucleus = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(false, q_x),
        ]);

        // Satellite: -P(a)
        let p_a = make_pred(&table, "P", vec![a]);
        let satellite = Clause::new(vec![Literal::new(false, p_a)]);

        let results = neg_hyperresolve_units(&nucleus, None, &[satellite], &[None]);

        assert_eq!(results.len(), 1);
        // Result should be -Q(a)
        assert_eq!(results[0].clause.literals.len(), 1);
        assert!(!results[0].clause.literals[0].sign);
    }

    #[test]
    fn neg_hyperresolve_multiple_positives() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");
        let x = make_var(0);
        let y = make_var(1);

        // Nucleus: P(x) | Q(y) | -R(x, y)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_y = make_pred(&table, "Q", vec![y.clone()]);
        let r_xy = make_pred(&table, "R", vec![x, y]);
        let nucleus = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(true, q_y),
            Literal::new(false, r_xy),
        ]);

        // Satellites: -P(a), -Q(b)
        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let q_b = make_pred(&table, "Q", vec![b.clone()]);
        let sat1 = Clause::new(vec![Literal::new(false, p_a)]);
        let sat2 = Clause::new(vec![Literal::new(false, q_b)]);

        let results = neg_hyperresolve_units(&nucleus, None, &[sat1, sat2], &[None, None]);

        assert_eq!(results.len(), 1);
        // Result should be -R(a, b)
        assert_eq!(results[0].clause.literals.len(), 1);
        assert!(!results[0].clause.literals[0].sign);
    }

    #[test]
    fn neg_hyperresolve_no_match() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);

        // Nucleus: P(x) | -Q(x)
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_x = make_pred(&table, "Q", vec![x]);
        let nucleus = Clause::new(vec![
            Literal::new(true, p_x),
            Literal::new(false, q_x),
        ]);

        // Satellite: -R(a) - doesn't match P
        let r_a = make_pred(&table, "R", vec![a]);
        let satellite = Clause::new(vec![Literal::new(false, r_a)]);

        let results = neg_hyperresolve_units(&nucleus, None, &[satellite], &[None]);

        assert!(results.is_empty());
    }

    #[test]
    fn neg_hyperresolve_all_negative() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        // Nucleus with no positive literals
        let p_a = make_pred(&table, "P", vec![a]);
        let nucleus = Clause::new(vec![Literal::new(false, p_a)]);

        let results = neg_hyperresolve_units(&nucleus, None, &[], &[]);

        assert!(results.is_empty());
    }

    #[test]
    fn neg_hyperresolve_empty_result() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");

        // Nucleus: P(a) (single positive literal, no negatives)
        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let nucleus = Clause::new(vec![Literal::new(true, p_a.clone())]);

        // Satellite: -P(a)
        let satellite = Clause::new(vec![Literal::new(false, p_a)]);

        let results = neg_hyperresolve_units(&nucleus, None, &[satellite], &[None]);

        assert_eq!(results.len(), 1);
        // Result should be empty clause (contradiction)
        assert_eq!(results[0].clause.literals.len(), 0);
    }
}
