//! Hints mechanism for guiding theorem proving.
//!
//! Hints are clauses from known proofs or proof sketches that guide the search
//! by adjusting the pick-given weight of generated clauses that match them.
//!
//! Three matching modes are supported:
//! - Forward subsumption (fsub): Hint subsumes generated clause
//! - Back subsumption (bsub): Generated clause subsumes hint
//! - Equivalence (equiv): Both directions (most specific)
//!
//! When a clause matches a hint, its weight is adjusted to prioritize it
//! in the given-clause selection process.

use crate::data::{Clause, ClauseId};
use crate::inference::subsumes;

/// Maximum weight value (disabled indicator).
pub const MAX_WEIGHT: i32 = i32::MAX;

/// Hint configuration data attached to each hint clause.
#[derive(Debug, Clone)]
pub struct HintData {
    /// Forward subsumption enabled
    pub fsub_enabled: bool,
    /// Back subsumption enabled
    pub bsub_enabled: bool,
    /// Equivalence enabled
    pub equiv_enabled: bool,

    /// Replacement weight for forward subsumption matches
    pub fsub_wt: i32,
    /// Additive weight adjustment for forward subsumption
    pub fsub_add_wt: i32,

    /// Replacement weight for back subsumption matches
    pub bsub_wt: i32,
    /// Additive weight adjustment for back subsumption
    pub bsub_add_wt: i32,

    /// Replacement weight for equivalence matches
    pub equiv_wt: i32,
    /// Additive weight adjustment for equivalence
    pub equiv_add_wt: i32,

    /// Optional label copied to matching clauses
    pub label: Option<String>,
}

impl HintData {
    /// Create hint data from global parameters.
    pub fn new(
        fsub_wt: i32,
        fsub_add_wt: i32,
        bsub_wt: i32,
        bsub_add_wt: i32,
        equiv_wt: i32,
        equiv_add_wt: i32,
    ) -> Self {
        Self {
            fsub_enabled: !(fsub_wt == MAX_WEIGHT && fsub_add_wt == 0),
            bsub_enabled: !(bsub_wt == MAX_WEIGHT && bsub_add_wt == 0),
            equiv_enabled: !(equiv_wt == MAX_WEIGHT && equiv_add_wt == 0),
            fsub_wt,
            fsub_add_wt,
            bsub_wt,
            bsub_add_wt,
            equiv_wt,
            equiv_add_wt,
            label: None,
        }
    }

    /// Check if this hint has any active matching modes.
    pub fn is_active(&self) -> bool {
        self.fsub_enabled || self.bsub_enabled || self.equiv_enabled
    }
}

impl Default for HintData {
    fn default() -> Self {
        Self::new(MAX_WEIGHT, 0, MAX_WEIGHT, -1000, MAX_WEIGHT, 0)
    }
}

/// Collection of hint clauses with their configuration.
#[derive(Debug, Clone)]
pub struct HintsList {
    /// Hint clauses paired with their configuration data
    pub hints: Vec<(Clause, HintData)>,
}

impl HintsList {
    /// Create an empty hints list.
    pub fn new() -> Self {
        Self { hints: Vec::new() }
    }

    /// Add a hint with its configuration.
    pub fn add_hint(&mut self, clause: Clause, data: HintData) {
        if data.is_active() {
            self.hints.push((clause, data));
        }
    }

    /// Check if there are any hints.
    pub fn is_empty(&self) -> bool {
        self.hints.is_empty()
    }

    /// Get the number of hints.
    pub fn len(&self) -> usize {
        self.hints.len()
    }
}

impl Default for HintsList {
    fn default() -> Self {
        Self::new()
    }
}

/// Adjust a clause's pick-given weight based on hint matching.
///
/// This function checks if the clause matches any hint and adjusts its
/// weight accordingly. Matching is done in order of specificity:
/// 1. Equivalence (both directions)
/// 2. Forward subsumption (hint subsumes clause)
/// 3. Back subsumption (clause subsumes hint)
///
/// Returns true if the clause matched any hint.
pub fn adjust_weight_with_hints(
    clause: &mut Clause,
    hints: &HintsList,
) -> bool {
    for (hint, hint_data) in &hints.hints {
        // Check for equivalence (most specific)
        if hint_data.equiv_enabled {
            let fsub = subsumes(hint, clause);
            let bsub = subsumes(clause, hint);

            if fsub && bsub {
                // Equivalence match
                if hint_data.equiv_wt != MAX_WEIGHT {
                    clause.pick_weight = hint_data.equiv_wt;
                }
                clause.pick_weight += hint_data.equiv_add_wt;

                // Copy label if present
                if let Some(ref label) = hint_data.label {
                    // Store label in clause (would need to extend Clause struct)
                    // For now, just return success
                }

                return true;
            }
        }

        // Check for forward subsumption (hint subsumes clause)
        if hint_data.fsub_enabled {
            if subsumes(hint, clause) {
                if hint_data.fsub_wt != MAX_WEIGHT {
                    clause.pick_weight = hint_data.fsub_wt;
                }
                clause.pick_weight += hint_data.fsub_add_wt;

                if let Some(ref label) = hint_data.label {
                    // Copy label
                }

                return true;
            }
        }

        // Check for back subsumption (clause subsumes hint)
        if hint_data.bsub_enabled {
            if subsumes(clause, hint) {
                if hint_data.bsub_wt != MAX_WEIGHT {
                    clause.pick_weight = hint_data.bsub_wt;
                }
                clause.pick_weight += hint_data.bsub_add_wt;

                if let Some(ref label) = hint_data.label {
                    // Copy label
                }

                return true;
            }
        }
    }

    false
}

/// Check if a clause should be kept despite exceeding max weight.
///
/// A clause is kept if:
/// - `keep_hint_subsumers` is set and the clause subsumes some hint (bsub)
/// - `keep_hint_equivalents` is set and the clause is equivalent to some hint
pub fn hint_keep_test(
    clause: &Clause,
    hints: &HintsList,
    keep_subsumers: bool,
    keep_equivalents: bool,
) -> bool {
    if !keep_subsumers && !keep_equivalents {
        return false;
    }

    for (hint, _) in &hints.hints {
        if keep_equivalents {
            let fsub = subsumes(hint, clause);
            let bsub = subsumes(clause, hint);
            if fsub && bsub {
                return true;
            }
        }

        if keep_subsumers {
            if subsumes(clause, hint) {
                return true;
            }
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{Literal, SymbolTable, Term, SymbolKind, VariableId};

    fn make_simple_clause(pred: &str, is_positive: bool, symbols: &SymbolTable) -> Clause {
        let sym = symbols.intern(pred, 1, SymbolKind::Predicate);
        let lit = Literal::new(
            is_positive,
            Term::application(sym, vec![Term::variable(VariableId::new(0))]),
        );
        Clause::new(vec![lit])
    }

    #[test]
    fn test_hint_data_activation() {
        // All disabled
        let data = HintData::new(MAX_WEIGHT, 0, MAX_WEIGHT, 0, MAX_WEIGHT, 0);
        assert!(!data.is_active());

        // Back subsumption enabled via add_wt
        let data = HintData::new(MAX_WEIGHT, 0, MAX_WEIGHT, -1000, MAX_WEIGHT, 0);
        assert!(data.is_active());
        assert!(data.bsub_enabled);

        // Forward subsumption enabled via wt
        let data = HintData::new(100, 0, MAX_WEIGHT, 0, MAX_WEIGHT, 0);
        assert!(data.is_active());
        assert!(data.fsub_enabled);
    }

    #[test]
    fn test_weight_adjustment_bsub() {
        let symbols = SymbolTable::new();

        // Hint: P(a) - more specific
        let p_sym = symbols.intern("P", 1, SymbolKind::Predicate);
        let a_sym = symbols.intern("a", 0, SymbolKind::Constant);
        let hint_lit = Literal::new(
            true,
            Term::application(p_sym, vec![Term::application(a_sym, vec![])]),
        );
        let hint = Clause::new(vec![hint_lit]);

        // Clause: P(x) - more general (subsumes hint)
        let clause_lit = Literal::new(
            true,
            Term::application(p_sym, vec![Term::variable(VariableId::new(0))]),
        );
        let mut clause = Clause::new(vec![clause_lit]);
        clause.pick_weight = 1000;

        // Create hint data with back subsumption enabled
        let hint_data = HintData::new(MAX_WEIGHT, 0, MAX_WEIGHT, -500, MAX_WEIGHT, 0);

        let mut hints_list = HintsList::new();
        hints_list.add_hint(hint, hint_data);

        // Adjust weight
        let matched = adjust_weight_with_hints(&mut clause, &hints_list);

        assert!(matched);
        assert_eq!(clause.pick_weight, 1000 - 500); // Original weight + add_wt
    }

    #[test]
    fn test_hint_keep_test() {
        let symbols = SymbolTable::new();

        // Create hint and clause where clause subsumes hint
        let p_sym = symbols.intern("P", 1, SymbolKind::Predicate);
        let a_sym = symbols.intern("a", 0, SymbolKind::Constant);

        let hint_lit = Literal::new(
            true,
            Term::application(p_sym, vec![Term::application(a_sym, vec![])]),
        );
        let hint = Clause::new(vec![hint_lit]);

        let clause_lit = Literal::new(
            true,
            Term::application(p_sym, vec![Term::variable(VariableId::new(0))]),
        );
        let clause = Clause::new(vec![clause_lit]);

        let hint_data = HintData::default();
        let mut hints_list = HintsList::new();
        hints_list.add_hint(hint, hint_data);

        // Should keep if keep_subsumers is true
        assert!(hint_keep_test(&clause, &hints_list, true, false));

        // Should not keep if keep_subsumers is false
        assert!(!hint_keep_test(&clause, &hints_list, false, false));
    }
}
