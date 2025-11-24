//! Builder to construct a prover from parsed Otter input.

use crate::data::{ClauseArena, SymbolTable};
use crate::data::symbol::SymbolKind;
use crate::inference::{Prover, ProverConfig};
use crate::parser::{ListSection, OtterCommand, OtterFile};

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
            "factor" => {
                self.config.use_factor = true;
            }
            "ur_res" => {
                self.config.use_ur_res = true;
            }
            _ => {}
        }
    }

    fn apply_clear_flag(&mut self, _flag: &str) {
        // Handle clear flags
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
                            list.to_clause_list(&mut arena, &self.symbols)
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
                            list.to_clause_list(&mut arena, &self.symbols)
                                .map_err(|e| e.to_string())?
                        }
                    };
                    for id in clause_list.iter() {
                        if let Some(clause) = arena.get(*id) {
                            sos_clauses.push(clause.clone());
                        }
                    }
                }
                "passive" | "demodulators" | "hints" => {
                    // These lists are recognized but not yet implemented
                }
                _ => {
                    // Unknown list type - could warn or ignore
                }
            }
        }

        // In auto mode, if sos is empty but usable has clauses, move negative clauses to sos
        if self.config.auto_mode && sos_clauses.is_empty() && !usable_clauses.is_empty() {
            // Check for negative/goal clauses in usable
            let mut remaining_usable = Vec::new();
            for clause in usable_clauses {
                // A clause with all negative literals, or containing a negative literal, is a goal
                let has_negative = clause.literals.iter().any(|lit| !lit.sign);
                if has_negative {
                    sos_clauses.push(clause);
                } else {
                    remaining_usable.push(clause);
                }
            }
            usable_clauses = remaining_usable;
        }

        // Add clauses to prover
        for clause in usable_clauses {
            prover.add_usable(clause);
        }
        for clause in sos_clauses {
            prover.add_sos(clause);
        }

        // Set equality symbol for paramodulation
        let eq_symbol = self.symbols.intern("=", 2, SymbolKind::Function);
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
