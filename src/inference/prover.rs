//! Basic resolution-based theorem prover skeleton.
//!
//! This module provides a simple saturation-based prover that uses binary
//! resolution to search for contradictions (empty clauses).

use crate::data::{Clause, ClauseArena, ClauseId, ClauseList, SymbolId, WeightTable};
use crate::inference::{
    all_resolvents, demodulate_clause, extract_demodulator, factor_clause, hyperresolve_units,
    paramodulate_into, ur_resolve, Demodulator,
};

/// Result of a proof search.
#[derive(Clone, Debug)]
pub enum ProofResult {
    /// A proof was found (empty clause derived)
    Proof {
        /// The empty clause that was derived
        empty_clause_id: ClauseId,
        /// Total clauses generated during search
        clauses_generated: usize,
        /// Clauses kept after filtering
        clauses_kept: usize,
    },
    /// Search exhausted without finding proof
    Saturated {
        clauses_generated: usize,
        clauses_kept: usize,
    },
    /// Search exceeded resource limits
    ResourceLimit {
        clauses_generated: usize,
        clauses_kept: usize,
        limit_type: String,
    },
}

/// Configuration for the prover.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// Maximum number of clauses to generate
    pub max_clauses: usize,
    /// Maximum number of given clauses to process
    pub max_given: usize,
    /// Ratio of clauses selected by weight vs FIFO (pick_given_ratio)
    /// For every N clauses selected by weight, select 1 by FIFO
    pub pick_given_ratio: usize,
    /// Maximum proof search time in seconds (0 = unlimited)
    pub max_seconds: u64,
    /// Auto mode enabled
    pub auto_mode: bool,
    /// Use hyperresolution
    pub use_hyper_res: bool,
    /// Use binary resolution
    pub use_binary_res: bool,
    /// Use paramodulation (para_into)
    pub use_para_into: bool,
    /// Use paramodulation (para_from)
    pub use_para_from: bool,
    /// Use demodulation for term rewriting
    pub use_demod: bool,
    /// Use factoring to simplify clauses
    pub use_factor: bool,
    /// Use UR-resolution (unit-resulting resolution)
    pub use_ur_res: bool,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self {
            max_clauses: 10000,
            max_given: 1000,
            pick_given_ratio: 4,
            max_seconds: 0,
            auto_mode: false,
            use_hyper_res: false,
            use_binary_res: true,
            use_para_into: false,
            use_para_from: false,
            use_demod: false,
            use_factor: false,
            use_ur_res: false,
        }
    }
}

/// Simple resolution-based theorem prover.
pub struct Prover {
    /// Configuration settings
    config: ProverConfig,
    /// Storage for all clauses
    arena: ClauseArena,
    /// Set of support (clauses to be selected as given)
    sos: ClauseList,
    /// Usable clauses (clauses to resolve against)
    usable: ClauseList,
    /// Equality symbol (if set)
    eq_symbol: Option<SymbolId>,
    /// Demodulators for term rewriting
    demodulators: Vec<Demodulator>,
    /// Symbol weight table for clause selection
    weight_table: WeightTable,
    /// Statistics
    clauses_generated: usize,
    clauses_kept: usize,
    given_count: usize,
    /// Counter for pick_given_ratio (tracks when to select by FIFO vs weight)
    pick_count: usize,
}

impl Prover {
    /// Create a new prover with default configuration.
    pub fn new() -> Self {
        Self::with_config(ProverConfig::default())
    }

    /// Create a new prover with custom configuration.
    pub fn with_config(config: ProverConfig) -> Self {
        Self {
            config,
            arena: ClauseArena::new(),
            sos: ClauseList::new("sos"),
            usable: ClauseList::new("usable"),
            eq_symbol: None,
            demodulators: Vec::new(),
            weight_table: WeightTable::new(),
            clauses_generated: 0,
            clauses_kept: 0,
            given_count: 0,
            pick_count: 0,
        }
    }

    /// Set symbol weight for clause selection.
    pub fn set_symbol_weight(&mut self, symbol: SymbolId, weight: i32) {
        self.weight_table.set_weight(symbol, weight);
    }

    /// Set default weight for unlisted symbols.
    pub fn set_default_weight(&mut self, weight: i32) {
        self.weight_table.set_default(weight);
    }

    /// Set the equality symbol for paramodulation.
    pub fn set_eq_symbol(&mut self, sym: SymbolId) {
        self.eq_symbol = Some(sym);
    }

    /// Process a new clause: apply factoring, demodulation, and check if it's a demodulator.
    ///
    /// Returns None if the clause should be discarded, or Some(processed_clause).
    fn process_new_clause(&mut self, mut clause: Clause) -> Option<Clause> {
        // Apply factoring if enabled (simplify before other processing)
        if self.config.use_factor {
            // Try to factor the clause once
            let factors = factor_clause(&clause, None);
            if !factors.is_empty() {
                // Use the first factor (in full Otter, might generate all factors)
                clause = factors[0].clause.clone();
            }
        }

        // Apply forward demodulation if enabled
        if self.config.use_demod && !self.demodulators.is_empty() {
            clause = demodulate_clause(&clause, &self.demodulators);
        }

        // Check if this clause is a demodulator
        if self.config.use_demod {
            if let Some(eq_sym) = self.eq_symbol {
                if let Some(demod) = extract_demodulator(&clause, eq_sym) {
                    // Note: In full Otter, we'd also do back-demodulation here
                    // (rewrite existing clauses with the new demodulator)
                    self.demodulators.push(demod);
                }
            }
        }

        Some(clause)
    }

    /// Add a clause to the set of support.
    pub fn add_sos(&mut self, mut clause: Clause) -> ClauseId {
        // Cache the weight for efficient clause selection
        clause.pick_weight = self.weight_table.weight_clause(&clause);

        let id = self.arena.insert(clause);
        self.sos.push(id);
        self.clauses_kept += 1;
        id
    }

    /// Add a clause to the usable set.
    pub fn add_usable(&mut self, mut clause: Clause) -> ClauseId {
        // Cache the weight (may be used if clause moves to SOS later)
        clause.pick_weight = self.weight_table.weight_clause(&clause);

        let id = self.arena.insert(clause);
        self.usable.push(id);
        self.clauses_kept += 1;
        id
    }

    /// Select and remove the lightest clause from SOS based on weight.
    ///
    /// This scans all clauses in SOS, finds the one with minimum weight,
    /// removes it from the list, and returns it.
    ///
    /// Note: Uses cached pick_weight from clause for O(n) selection instead of O(n*m).
    fn select_lightest_clause(&mut self) -> Option<ClauseId> {
        if self.sos.is_empty() {
            return None;
        }

        // Find the clause with minimum weight
        let mut min_weight = i32::MAX;
        let mut min_index = 0;

        for (index, clause_id) in self.sos.iter().enumerate() {
            if let Some(clause) = self.arena.get(*clause_id) {
                // Use cached weight instead of recalculating!
                // This changes complexity from O(n*m) to O(n) where m = avg clause size
                if clause.pick_weight < min_weight {
                    min_weight = clause.pick_weight;
                    min_index = index;
                }
            }
        }

        // Remove and return the lightest clause
        self.sos.remove(min_index)
    }

    /// Pre-process initial clauses to extract demodulators.
    fn preprocess_initial_clauses(&mut self) {
        if !self.config.use_demod {
            return;
        }

        let eq_sym = match self.eq_symbol {
            Some(sym) => sym,
            None => return,
        };

        // Extract demodulators from usable clauses
        for clause_id in self.usable.iter() {
            if let Some(clause) = self.arena.get(*clause_id) {
                if let Some(demod) = extract_demodulator(clause, eq_sym) {
                    self.demodulators.push(demod);
                }
            }
        }
    }

    /// Run the proof search.
    pub fn search(&mut self) -> ProofResult {
        // Pre-process to extract initial demodulators
        self.preprocess_initial_clauses();

        while !self.sos.is_empty() {
            // Check resource limits
            if self.given_count >= self.config.max_given {
                return ProofResult::ResourceLimit {
                    clauses_generated: self.clauses_generated,
                    clauses_kept: self.clauses_kept,
                    limit_type: "max_given".to_string(),
                };
            }

            if self.clauses_kept >= self.config.max_clauses {
                return ProofResult::ResourceLimit {
                    clauses_generated: self.clauses_generated,
                    clauses_kept: self.clauses_kept,
                    limit_type: "max_clauses".to_string(),
                };
            }

            // Select given clause using pick_given_ratio strategy
            // Pick by weight for first N clauses, then by FIFO for 1 clause, repeat
            let select_by_weight = self.pick_count < self.config.pick_given_ratio;
            self.pick_count = (self.pick_count + 1) % (self.config.pick_given_ratio + 1);

            let given_id = if select_by_weight {
                self.select_lightest_clause()
            } else {
                self.sos.pop() // FIFO
            };

            let given_id = match given_id {
                Some(id) => id,
                None => break,
            };

            self.given_count += 1;

            // Get the given clause
            let given_clause = match self.arena.get(given_id) {
                Some(c) => c.clone(),
                None => continue,
            };

            // Collect usable clauses for inference
            let usable_ids: Vec<_> = self.usable.iter().cloned().collect();
            let usable_clauses: Vec<Clause> = usable_ids
                .iter()
                .filter_map(|id| self.arena.get(*id).cloned())
                .collect();
            let usable_id_opts: Vec<Option<ClauseId>> = usable_ids.iter().map(|id| Some(*id)).collect();

            // Perform hyperresolution if enabled
            // In hyperresolution, the given clause (positive satellite) is resolved
            // against usable clauses (nuclei with negative literals)
            if self.config.use_hyper_res {
                // Try hyperresolving each usable clause (nucleus) with given + other usable (satellites)
                for (nucleus_idx, nucleus_id) in usable_ids.iter().enumerate() {
                    let nucleus = &usable_clauses[nucleus_idx];

                    // Check if nucleus has negative literals
                    if !nucleus.literals.iter().any(|lit| !lit.sign) {
                        continue;
                    }

                    // Build list of satellites: given clause + other positive units from usable
                    let mut satellites = vec![];
                    let mut satellite_ids = vec![];

                    // Add given clause if it's a positive unit
                    if given_clause.literals.len() == 1 && given_clause.literals[0].sign {
                        satellites.push(given_clause.clone());
                        satellite_ids.push(Some(given_id));
                    }

                    for (sat_idx, sat_id) in usable_ids.iter().enumerate() {
                        if sat_idx != nucleus_idx {
                            let sat = &usable_clauses[sat_idx];
                            // Add positive units as potential satellites
                            if sat.literals.len() == 1 && sat.literals[0].sign {
                                satellites.push(sat.clone());
                                satellite_ids.push(Some(*sat_id));
                            }
                        }
                    }

                    if satellites.is_empty() {
                        continue;
                    }

                    let hyper_resolvents = hyperresolve_units(
                        nucleus,
                        Some(*nucleus_id),
                        &satellites,
                        &satellite_ids,
                    );

                    for resolvent in hyper_resolvents {
                        self.clauses_generated += 1;

                        // Process the clause (demodulate, extract demodulators)
                        let processed = match self.process_new_clause(resolvent.clause) {
                            Some(c) => c,
                            None => continue,
                        };

                        // Check for empty clause (proof found)
                        if processed.literals.is_empty() {
                            let empty_id = self.arena.insert(processed);
                            self.clauses_kept += 1;
                            return ProofResult::Proof {
                                empty_clause_id: empty_id,
                                clauses_generated: self.clauses_generated,
                                clauses_kept: self.clauses_kept,
                            };
                        }

                        // Add to sos for further processing
                        let new_id = self.arena.insert(processed);
                        self.sos.push(new_id);
                        self.clauses_kept += 1;
                    }
                }
            }

            // Perform binary resolution if enabled
            if self.config.use_binary_res {
                for (i, usable_id) in usable_ids.iter().enumerate() {
                    let usable_clause = &usable_clauses[i];

                    let resolvents = all_resolvents(
                        &given_clause,
                        usable_clause,
                        Some(given_id),
                        Some(*usable_id),
                    );

                    for resolvent in resolvents {
                        self.clauses_generated += 1;

                        // Process the clause (demodulate, extract demodulators)
                        let processed = match self.process_new_clause(resolvent.clause) {
                            Some(c) => c,
                            None => continue,
                        };

                        // Check for empty clause (proof found)
                        if processed.literals.is_empty() {
                            let empty_id = self.arena.insert(processed);
                            self.clauses_kept += 1;
                            return ProofResult::Proof {
                                empty_clause_id: empty_id,
                                clauses_generated: self.clauses_generated,
                                clauses_kept: self.clauses_kept,
                            };
                        }

                        // Add to sos for further processing
                        let new_id = self.arena.insert(processed);
                        self.sos.push(new_id);
                        self.clauses_kept += 1;
                    }
                }
            }

            // Perform UR-resolution if enabled
            if self.config.use_ur_res {
                // Collect usable clauses for UR-resolution
                let ur_resolvents = ur_resolve(
                    &given_clause,
                    Some(given_id),
                    &usable_clauses,
                    &usable_id_opts,
                );

                for resolvent in ur_resolvents {
                    self.clauses_generated += 1;

                    // Process the clause
                    let processed = match self.process_new_clause(resolvent.clause) {
                        Some(c) => c,
                        None => continue,
                    };

                    // Check for empty clause
                    if processed.literals.is_empty() {
                        let empty_id = self.arena.insert(processed);
                        self.clauses_kept += 1;
                        return ProofResult::Proof {
                            empty_clause_id: empty_id,
                            clauses_generated: self.clauses_generated,
                            clauses_kept: self.clauses_kept,
                        };
                    }

                    // Add to sos
                    let new_id = self.arena.insert(processed);
                    self.sos.push(new_id);
                    self.clauses_kept += 1;
                }
            }

            // Perform paramodulation if enabled and we have an equality symbol
            if (self.config.use_para_into || self.config.use_para_from) && self.eq_symbol.is_some() {
                let eq_sym = self.eq_symbol.unwrap();

                for (i, usable_id) in usable_ids.iter().enumerate() {
                    let usable_clause = &usable_clauses[i];

                    // Para into: given contains equality, paramodulate into usable
                    if self.config.use_para_into {
                        let paramodulants = paramodulate_into(
                            &given_clause,
                            Some(given_id),
                            usable_clause,
                            Some(*usable_id),
                            eq_sym,
                        );

                        for paramodulant in paramodulants {
                            self.clauses_generated += 1;

                            // Process the clause (demodulate, extract demodulators)
                            let processed = match self.process_new_clause(paramodulant.clause) {
                                Some(c) => c,
                                None => continue,
                            };

                            if processed.literals.is_empty() {
                                let empty_id = self.arena.insert(processed);
                                self.clauses_kept += 1;
                                return ProofResult::Proof {
                                    empty_clause_id: empty_id,
                                    clauses_generated: self.clauses_generated,
                                    clauses_kept: self.clauses_kept,
                                };
                            }

                            let new_id = self.arena.insert(processed);
                            self.sos.push(new_id);
                            self.clauses_kept += 1;
                        }
                    }

                    // Para from: usable contains equality, paramodulate into given
                    if self.config.use_para_from {
                        let paramodulants = paramodulate_into(
                            usable_clause,
                            Some(*usable_id),
                            &given_clause,
                            Some(given_id),
                            eq_sym,
                        );

                        for paramodulant in paramodulants {
                            self.clauses_generated += 1;

                            // Process the clause (demodulate, extract demodulators)
                            let processed = match self.process_new_clause(paramodulant.clause) {
                                Some(c) => c,
                                None => continue,
                            };

                            if processed.literals.is_empty() {
                                let empty_id = self.arena.insert(processed);
                                self.clauses_kept += 1;
                                return ProofResult::Proof {
                                    empty_clause_id: empty_id,
                                    clauses_generated: self.clauses_generated,
                                    clauses_kept: self.clauses_kept,
                                };
                            }

                            let new_id = self.arena.insert(processed);
                            self.sos.push(new_id);
                            self.clauses_kept += 1;
                        }
                    }
                }
            }

            // Move given clause to usable
            self.usable.push(given_id);
        }

        ProofResult::Saturated {
            clauses_generated: self.clauses_generated,
            clauses_kept: self.clauses_kept,
        }
    }

    /// Get the clause arena for inspection.
    pub fn arena(&self) -> &ClauseArena {
        &self.arena
    }

    /// Get statistics about the search.
    pub fn stats(&self) -> (usize, usize, usize) {
        (self.clauses_generated, self.clauses_kept, self.given_count)
    }

    /// Get the prover configuration.
    pub fn config(&self) -> &ProverConfig {
        &self.config
    }

    /// Get a mutable reference to the prover configuration.
    pub fn config_mut(&mut self) -> &mut ProverConfig {
        &mut self.config
    }
}

impl Default for Prover {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::symbol::{SymbolKind, SymbolTable};
    use crate::data::{Literal, Term, VariableId};

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
    fn prove_simple_contradiction() {
        // P(a) and -P(x) should derive empty clause
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);

        let p_a = make_pred(&table, "P", vec![a]);
        let p_x = make_pred(&table, "P", vec![x]);

        let clause1 = Clause::new(vec![Literal::new(true, p_a)]);
        let clause2 = Clause::new(vec![Literal::new(false, p_x)]);

        let mut prover = Prover::new();
        prover.add_sos(clause1);
        prover.add_usable(clause2);

        let result = prover.search();
        assert!(matches!(result, ProofResult::Proof { .. }));
    }

    #[test]
    fn saturates_without_proof() {
        // P(a) and Q(b) cannot derive contradiction
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        let p_a = make_pred(&table, "P", vec![a]);
        let q_b = make_pred(&table, "Q", vec![b]);

        let clause1 = Clause::new(vec![Literal::new(true, p_a)]);
        let clause2 = Clause::new(vec![Literal::new(true, q_b)]);

        let mut prover = Prover::new();
        prover.add_sos(clause1);
        prover.add_usable(clause2);

        let result = prover.search();
        assert!(matches!(result, ProofResult::Saturated { .. }));
    }

    #[test]
    fn prove_chain_resolution() {
        // P(a), P(x) -> Q(x), -Q(a) should derive empty clause
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let x = make_var(0);
        let y = make_var(1);

        let p_a = make_pred(&table, "P", vec![a.clone()]);
        let p_x = make_pred(&table, "P", vec![x.clone()]);
        let q_x = make_pred(&table, "Q", vec![x]);
        let q_a = make_pred(&table, "Q", vec![a]);

        // P(a)
        let clause1 = Clause::new(vec![Literal::new(true, p_a)]);
        // -P(y) | Q(y)
        let p_y = make_pred(&table, "P", vec![y.clone()]);
        let q_y = make_pred(&table, "Q", vec![y]);
        let clause2 = Clause::new(vec![
            Literal::new(false, p_y),
            Literal::new(true, q_y),
        ]);
        // -Q(a)
        let clause3 = Clause::new(vec![Literal::new(false, q_a)]);

        let mut prover = Prover::new();
        prover.add_sos(clause1);
        prover.add_usable(clause2);
        prover.add_usable(clause3);

        let result = prover.search();
        assert!(matches!(result, ProofResult::Proof { .. }));
    }

    #[test]
    fn respects_max_given_limit() {
        let table = SymbolTable::new();
        let x = make_var(0);

        // Create clauses that can generate resolvents indefinitely
        let mut prover = Prover::with_config(ProverConfig {
            max_clauses: 10000,
            max_given: 5,
            pick_given_ratio: 4,
            max_seconds: 0,
            auto_mode: false,
            use_hyper_res: false,
            use_binary_res: true,
            use_para_into: false,
            use_para_from: false,
            use_demod: false,
            use_factor: false,
            use_ur_res: false,
        });

        // Add multiple clauses to sos so we hit the given limit
        for i in 0..10 {
            let a = make_const(&table, &format!("a{}", i));
            let pred = make_pred(&table, "P", vec![a.clone()]);
            let neg_pred = make_pred(&table, "Q", vec![a]);
            prover.add_sos(Clause::new(vec![
                Literal::new(true, pred),
                Literal::new(true, neg_pred),
            ]));
        }

        let result = prover.search();
        // With max_given=5 and 10 clauses in sos, should hit limit
        match result {
            ProofResult::ResourceLimit { limit_type, .. } => {
                assert_eq!(limit_type, "max_given");
            }
            ProofResult::Saturated { .. } => {
                // Also acceptable - saturated before limit
            }
            _ => panic!("expected ResourceLimit or Saturated"),
        }
    }

    #[test]
    fn weight_based_clause_selection() {
        // Test that weight-based selection picks lighter clauses first
        let table = SymbolTable::new();

        // Create predicates with different weights
        let p_sym = table.intern("P", 1, SymbolKind::Predicate);
        let q_sym = table.intern("Q", 1, SymbolKind::Predicate);
        let a = make_const(&table, "a");

        let mut config = ProverConfig::default();
        config.pick_given_ratio = 100; // Always select by weight for this test

        let mut prover = Prover::with_config(config);

        // Set Q to have much higher weight than P
        prover.set_symbol_weight(p_sym, 1);
        prover.set_symbol_weight(q_sym, 100);

        // Add Q(a) first (heavy), then P(a) (light)
        let q_a = make_pred(&table, "Q", vec![a.clone()]);
        let p_a = make_pred(&table, "P", vec![a]);

        prover.add_sos(Clause::new(vec![Literal::new(true, q_a)]));
        prover.add_sos(Clause::new(vec![Literal::new(true, p_a)]));

        // Select first clause - should be P(a) (lighter) not Q(a) (heavier)
        let first_id = prover.select_lightest_clause().unwrap();
        let first_clause = prover.arena.get(first_id).unwrap();

        // Check that the selected clause is P(a) by verifying its predicate symbol
        if let Term::Application { symbol, .. } = &first_clause.literals[0].atom {
            assert_eq!(*symbol, p_sym, "Should select P(a) with weight 2, not Q(a) with weight 101");
        } else {
            panic!("Expected Application term");
        }
    }
}
