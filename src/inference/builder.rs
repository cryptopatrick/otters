//! Builder to construct a prover from parsed Otter input.

use crate::data::{Clause, ClauseArena, SymbolId, SymbolTable, Term};
use crate::data::symbol::SymbolKind;
use crate::inference::{Prover, ProverConfig};
use crate::parser::{ListSection, OtterCommand, OtterFile};

/// Problem type characteristics detected from input clauses.
#[derive(Debug)]
struct ProblemType {
    has_equality: bool,
    max_literals: usize,
    is_horn: bool,
}

/// Check if a clause contains an equality literal.
fn clause_has_equality(clause: &Clause, eq_symbol: SymbolId) -> bool {
    clause.literals.iter().any(|lit| {
        if let Term::Application { symbol, args } = &lit.atom {
            *symbol == eq_symbol && args.len() == 2
        } else {
            false
        }
    })
}

/// Check if a clause is a Horn clause (at most one positive literal).
fn is_horn_clause(clause: &Clause) -> bool {
    clause.literals.iter().filter(|lit| lit.sign).count() <= 1
}

/// Check if a clause is entirely positive (all literals positive).
fn is_positive_clause(clause: &Clause) -> bool {
    clause.literals.iter().all(|lit| lit.sign)
}

/// Detect problem type characteristics from clauses.
fn detect_problem_type(clauses: &[Clause], eq_symbol: SymbolId) -> ProblemType {
    let has_equality = clauses.iter().any(|c| clause_has_equality(c, eq_symbol));
    let max_literals = clauses.iter().map(|c| c.literals.len()).max().unwrap_or(0);
    let is_horn = clauses.iter().all(|c| is_horn_clause(c));

    ProblemType {
        has_equality,
        max_literals,
        is_horn,
    }
}

/// Build a prover from parsed Otter input.
pub struct ProverBuilder {
    config: ProverConfig,
    symbols: SymbolTable,
}

impl ProverBuilder {
    /// Create a new builder with default configuration.
    pub fn new() -> Self {
        Self {
            config: ProverConfig::default(),
            symbols: SymbolTable::new(),
        }
    }

    /// Set the prover configuration.
    pub fn with_config(mut self, config: ProverConfig) -> Self {
        self.config = config;
        self
    }

    /// Apply configuration from parsed commands.
    pub fn apply_commands(&mut self, commands: &[OtterCommand]) {
        for command in commands {
            match command {
                OtterCommand::Set(flag) => {
                    self.apply_set_flag(flag);
                }
                OtterCommand::Clear(flag) => {
                    self.apply_clear_flag(flag);
                }
                OtterCommand::Assign { name, value } => {
                    self.apply_assign(name, value);
                }
                _ => {}
            }
        }
    }

    fn apply_set_flag(&mut self, flag: &str) {
        match flag {
            "auto" => {
                // Auto mode sets various defaults
                self.config.pick_given_ratio = 4;
                self.config.max_seconds = 10800; // 3 hours
                self.config.auto_mode = true;
                // In original Otter, auto mode enables these inference rules by default
                self.config.use_hyper_res = true;
                self.config.use_ur_res = true;
                self.config.use_binary_res = true;
                // EXPERIMENTAL: Enable linked UR to test if it helps (may have bugs)
                self.config.use_linked_ur_res = true;
                // Enable subsumption (always on in C Otter)
                self.config.use_subsumption = true;
            }
            "hyper_res" => {
                self.config.use_hyper_res = true;
            }
            "binary_res" => {
                self.config.use_binary_res = true;
            }
            "para_into" => {
                self.config.use_para_into = true;
            }
            "para_from" => {
                self.config.use_para_from = true;
            }
            "demod_inf" => {
                self.config.use_demod = true;
            }
            "back_demod" => {
                self.config.use_back_demod = true;
            }
            "factor" => {
                self.config.use_factor = true;
            }
            "ur_res" => {
                self.config.use_ur_res = true;
            }
            "linked_ur_res" => {
                self.config.use_linked_ur_res = true;
            }
            "unit_deletion" => {
                self.config.use_unit_deletion = true;
            }
            "keep_hint_subsumers" => {
                self.config.keep_hint_subsumers = true;
            }
            "keep_hint_equivalents" => {
                self.config.keep_hint_equivalents = true;
            }
            _ => {}
        }
    }

    fn apply_clear_flag(&mut self, flag: &str) {
        match flag {
            "back_demod" => {
                self.config.use_back_demod = false;
            }
            "demod_inf" => {
                self.config.use_demod = false;
            }
            _ => {}
        }
    }

    fn apply_assign(&mut self, name: &str, value: &str) {
        match name {
            "max_seconds" => {
                if let Ok(secs) = value.parse::<u64>() {
                    self.config.max_seconds = secs;
                }
            }
            "max_given" => {
                if let Ok(n) = value.parse::<usize>() {
                    self.config.max_given = n;
                }
            }
            "pick_given_ratio" => {
                if let Ok(n) = value.parse::<usize>() {
                    self.config.pick_given_ratio = n;
                }
            }
            "max_mem" => {
                // Memory limit - convert KB to clause limit approximation
                if let Ok(kb) = value.parse::<usize>() {
                    // Rough estimate: 100 bytes per clause
                    self.config.max_clauses = (kb * 1024) / 100;
                }
            }
            "max_weight" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.max_weight = w;
                }
            }
            "fsub_hint_wt" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.fsub_hint_wt = w;
                }
            }
            "bsub_hint_wt" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.bsub_hint_wt = w;
                }
            }
            "equiv_hint_wt" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.equiv_hint_wt = w;
                }
            }
            "fsub_hint_add_wt" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.fsub_hint_add_wt = w;
                }
            }
            "bsub_hint_add_wt" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.bsub_hint_add_wt = w;
                }
            }
            "equiv_hint_add_wt" => {
                if let Ok(w) = value.parse::<i32>() {
                    self.config.equiv_hint_add_wt = w;
                }
            }
            _ => {}
        }
    }

    /// Build a prover from parsed Otter file.
    pub fn build(mut self, file: &OtterFile) -> Result<Prover, String> {
        // Apply commands first
        self.apply_commands(&file.commands);

        let mut prover = Prover::with_config(self.config.clone());
        let mut arena = ClauseArena::new();

        // Collect clauses from all lists
        let mut usable_clauses = Vec::new();
        let mut sos_clauses = Vec::new();
        let mut hint_clauses = Vec::new();

        // Process each list section
        for list in &file.lists {
            match list.name.as_str() {
                "usable" => {
                    // Handle both clause and formula lists
                    let clause_list = match list.kind {
                        crate::parser::ListKind::Formula => {
                            list.to_clause_list_from_formulas(&mut arena, &self.symbols)
                                .map_err(|e| e.to_string())?
                        }
                        _ => {
                            list.to_clause_list(&mut arena, &self.symbols, &file.operators)
                                .map_err(|e| e.to_string())?
                        }
                    };
                    for id in clause_list.iter() {
                        if let Some(clause) = arena.get(*id) {
                            usable_clauses.push(clause.clone());
                        }
                    }
                }
                "sos" => {
                    // Handle both clause and formula lists
                    let clause_list = match list.kind {
                        crate::parser::ListKind::Formula => {
                            list.to_clause_list_from_formulas(&mut arena, &self.symbols)
                                .map_err(|e| e.to_string())?
                        }
                        _ => {
                            list.to_clause_list(&mut arena, &self.symbols, &file.operators)
                                .map_err(|e| e.to_string())?
                        }
                    };
                    for id in clause_list.iter() {
                        if let Some(clause) = arena.get(*id) {
                            sos_clauses.push(clause.clone());
                        }
                    }
                }
                "hints" => {
                    // Process hints list
                    let clause_list = match list.kind {
                        crate::parser::ListKind::Formula => {
                            list.to_clause_list_from_formulas(&mut arena, &self.symbols)
                                .map_err(|e| e.to_string())?
                        }
                        _ => {
                            list.to_clause_list(&mut arena, &self.symbols, &file.operators)
                                .map_err(|e| e.to_string())?
                        }
                    };
                    for id in clause_list.iter() {
                        if let Some(clause) = arena.get(*id) {
                            hint_clauses.push(clause.clone());
                        }
                    }
                }
                "passive" | "demodulators" => {
                    // These lists are recognized but not yet implemented
                }
                _ => {
                    // Unknown list type - could warn or ignore
                }
            }
        }

        // Get equality symbol for detection
        let eq_symbol = self.symbols.intern("=", 2, SymbolKind::Function);

        // In auto mode, detect problem type and apply appropriate strategy
        if self.config.auto_mode {
            // Combine all clauses for analysis
            let all_clauses: Vec<_> = usable_clauses.iter().chain(sos_clauses.iter()).cloned().collect();
            let problem_type = detect_problem_type(&all_clauses, eq_symbol);

            eprintln!(
                "AUTO MODE: equality={}, max_lits={}, horn={}",
                problem_type.has_equality, problem_type.max_literals, problem_type.is_horn
            );

            // Apply strategy based on problem type (mirrors C Otter automatic_1_settings)
            if problem_type.has_equality && problem_type.max_literals == 1 {
                // Pure equational (all units with equality) - KNUTH_BENDIX strategy
                eprintln!("STRATEGY: Pure equational (Knuth-Bendix)");
                self.config.use_para_from = true;
                self.config.use_para_into = true;
                self.config.use_demod = true;
                self.config.use_back_demod = false; // DISABLED: causes severe performance issues
                // Directional paramodulation (only left-to-right)
                self.config.para_from_left = true;
                self.config.para_from_right = false;
                self.config.para_into_left = true;
                self.config.para_into_right = false;
                // Disable resolution for pure equality
                self.config.use_binary_res = false;
                self.config.use_hyper_res = false;
                self.config.use_ur_res = false;
            } else if problem_type.has_equality && !problem_type.is_horn {
                // Non-Horn with equality
                eprintln!("STRATEGY: Non-Horn with equality");
                self.config.use_para_from = true;
                self.config.use_para_into = true;
                self.config.use_demod = true;
                self.config.use_back_demod = false; // DISABLED: causes severe performance issues
                // Directional paramodulation (only left-to-right)
                self.config.para_from_left = true;
                self.config.para_from_right = false;
                self.config.para_into_left = true;
                self.config.para_into_right = false;
                self.config.use_hyper_res = true;
                self.config.use_factor = true;
                self.config.use_unit_deletion = true;  // Critical for non-Horn problems
            } else if problem_type.has_equality && problem_type.is_horn {
                // Horn with equality
                eprintln!("STRATEGY: Horn with equality");
                self.config.use_para_from = true;
                self.config.use_para_into = true;
                self.config.use_demod = true;
                self.config.use_back_demod = false; // DISABLED: causes severe performance issues
                // Directional paramodulation (only left-to-right)
                self.config.para_from_left = true;
                self.config.para_from_right = false;
                self.config.para_into_left = true;
                self.config.para_into_right = false;
                self.config.use_hyper_res = true;
            } else if !problem_type.is_horn {
                // Non-Horn without equality
                eprintln!("STRATEGY: Non-Horn without equality");
                self.config.use_hyper_res = true;
                self.config.use_factor = true;
                self.config.use_unit_deletion = true;  // Critical for non-Horn problems
            } else {
                // Horn without equality
                eprintln!("STRATEGY: Horn without equality");
                self.config.use_hyper_res = true;
            }

            // In auto mode with equality, move positive clauses to SOS (like C Otter)
            if problem_type.has_equality && sos_clauses.is_empty() && !usable_clauses.is_empty() {
                let mut remaining_usable = Vec::new();
                for clause in usable_clauses {
                    if is_positive_clause(&clause) {
                        sos_clauses.push(clause);
                    } else {
                        remaining_usable.push(clause);
                    }
                }
                usable_clauses = remaining_usable;
            } else if sos_clauses.is_empty() && !usable_clauses.is_empty() {
                // Non-equality: move negative clauses to SOS
                let mut remaining_usable = Vec::new();
                for clause in usable_clauses {
                    let has_negative = clause.literals.iter().any(|lit| !lit.sign);
                    if has_negative {
                        sos_clauses.push(clause);
                    } else {
                        remaining_usable.push(clause);
                    }
                }
                usable_clauses = remaining_usable;
            }
        }

        // Rebuild prover with updated config
        prover = Prover::with_config(self.config.clone());

        // Add clauses to prover
        for clause in usable_clauses {
            prover.add_usable(clause);
        }
        for clause in sos_clauses {
            prover.add_sos(clause);
        }

        // Add hints to prover
        for clause in hint_clauses {
            prover.add_hint(clause);
        }

        // Set equality symbol for paramodulation
        prover.set_eq_symbol(eq_symbol);

        Ok(prover)
    }

    /// Get the symbol table.
    pub fn symbols(&self) -> &SymbolTable {
        &self.symbols
    }
}

impl Default for ProverBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn build_from_simple_input() {
        let input = r#"
list(usable).
P(a) | -Q(x).
end_of_list.

list(sos).
Q(b).
-P(x).
end_of_list.
"#;

        let parser = Parser::new();
        let file = parser.parse_str(input).expect("parse");

        let prover = ProverBuilder::new()
            .build(&file)
            .expect("build prover");

        // Check that clauses were added
        let (_, kept, _) = prover.stats();
        assert!(kept > 0);
    }

    #[test]
    fn apply_auto_mode() {
        let input = r#"
set(auto).
assign(max_seconds, 60).

list(sos).
P(a).
end_of_list.
"#;

        let parser = Parser::new();
        let file = parser.parse_str(input).expect("parse");

        let prover = ProverBuilder::new()
            .build(&file)
            .expect("build prover");

        // Prover should have config applied
        let (_, kept, _) = prover.stats();
        assert!(kept > 0);
    }

    #[test]
    fn handle_empty_input() {
        let input = "";
        let parser = Parser::new();
        let file = parser.parse_str(input).expect("parse");

        let prover = ProverBuilder::new()
            .build(&file)
            .expect("build prover");

        let (_, kept, _) = prover.stats();
        assert_eq!(kept, 0);
    }
}
