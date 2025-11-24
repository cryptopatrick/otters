//! Output formatting for prover results.
//!
//! Generates output in Otter's format to enable parity testing.

use crate::inference::{ProofResult, ProverConfig};
use std::fmt::Write;
use std::time::Duration;

/// Statistics from a prover run.
#[derive(Clone, Debug, Default)]
pub struct ProverStats {
    pub clauses_given: usize,
    pub clauses_generated: usize,
    pub clauses_kept: usize,
    pub clauses_forward_subsumed: usize,
    pub clauses_back_subsumed: usize,
    pub user_cpu_time: Duration,
    pub system_cpu_time: Duration,
    pub wall_clock_time: Duration,
    pub kbytes_malloced: usize,
}

/// Format prover output in Otter style.
pub struct OutputFormatter {
    /// Buffer for output
    output: String,
}

impl OutputFormatter {
    /// Create a new formatter.
    pub fn new() -> Self {
        Self {
            output: String::new(),
        }
    }

    /// Get the formatted output.
    pub fn output(&self) -> &str {
        &self.output
    }

    /// Consume the formatter and return the output.
    pub fn into_output(self) -> String {
        self.output
    }

    /// Write the banner.
    pub fn write_banner(&mut self) {
        writeln!(
            &mut self.output,
            "----- Otter 3.3 (Rust port), {} -----",
            env!("CARGO_PKG_VERSION")
        )
        .unwrap();
    }

    /// Write configuration settings.
    pub fn write_config(&mut self, config: &ProverConfig) {
        if config.pick_given_ratio != 4 {
            writeln!(
                &mut self.output,
                "assign(pick_given_ratio, {}).",
                config.pick_given_ratio
            )
            .unwrap();
        }
        if config.max_seconds > 0 {
            writeln!(
                &mut self.output,
                "assign(max_seconds, {}).",
                config.max_seconds
            )
            .unwrap();
        }
    }

    /// Write the result of proof search.
    pub fn write_result(&mut self, result: &ProofResult) {
        match result {
            ProofResult::Proof { .. } => {
                writeln!(&mut self.output).unwrap();
                writeln!(&mut self.output, "------------ end of proof -------------")
                    .unwrap();
                writeln!(&mut self.output).unwrap();
                writeln!(&mut self.output).unwrap();
                writeln!(
                    &mut self.output,
                    "Search stopped by max_proofs option."
                )
                .unwrap();
            }
            ProofResult::Saturated { .. } => {
                writeln!(&mut self.output).unwrap();
                writeln!(&mut self.output, "============ end of search ============")
                    .unwrap();
                writeln!(&mut self.output).unwrap();
                writeln!(&mut self.output, "Search stopped because sos is empty.")
                    .unwrap();
            }
            ProofResult::ResourceLimit { limit_type, .. } => {
                writeln!(&mut self.output).unwrap();
                writeln!(&mut self.output, "============ end of search ============")
                    .unwrap();
                writeln!(&mut self.output).unwrap();
                writeln!(
                    &mut self.output,
                    "Search stopped by {} limit.",
                    limit_type
                )
                .unwrap();
            }
        }
    }

    /// Write statistics section.
    pub fn write_statistics(&mut self, stats: &ProverStats) {
        writeln!(&mut self.output).unwrap();
        writeln!(&mut self.output, "-------------- statistics -------------")
            .unwrap();
        writeln!(
            &mut self.output,
            "clauses given              {:>8}",
            stats.clauses_given
        )
        .unwrap();
        writeln!(
            &mut self.output,
            "clauses generated          {:>8}",
            stats.clauses_generated
        )
        .unwrap();
        writeln!(
            &mut self.output,
            "clauses kept               {:>8}",
            stats.clauses_kept
        )
        .unwrap();
        writeln!(
            &mut self.output,
            "clauses forward subsumed   {:>8}",
            stats.clauses_forward_subsumed
        )
        .unwrap();
        writeln!(
            &mut self.output,
            "clauses back subsumed      {:>8}",
            stats.clauses_back_subsumed
        )
        .unwrap();
        writeln!(
            &mut self.output,
            "Kbytes malloced            {:>8}",
            stats.kbytes_malloced
        )
        .unwrap();
    }

    /// Write times section.
    pub fn write_times(&mut self, stats: &ProverStats) {
        writeln!(&mut self.output).unwrap();
        writeln!(&mut self.output, "----------- times (seconds) -----------")
            .unwrap();

        let user_secs = stats.user_cpu_time.as_secs_f64();
        let (user_h, user_m, user_s) = format_time(stats.user_cpu_time);
        writeln!(
            &mut self.output,
            "user CPU time          {:.2}          ({} hr, {} min, {} sec)",
            user_secs, user_h, user_m, user_s
        )
        .unwrap();

        let sys_secs = stats.system_cpu_time.as_secs_f64();
        let (sys_h, sys_m, sys_s) = format_time(stats.system_cpu_time);
        writeln!(
            &mut self.output,
            "system CPU time        {:.2}          ({} hr, {} min, {} sec)",
            sys_secs, sys_h, sys_m, sys_s
        )
        .unwrap();

        let wall_secs = stats.wall_clock_time.as_secs();
        let (wall_h, wall_m, wall_s) = format_time(stats.wall_clock_time);
        writeln!(
            &mut self.output,
            "wall-clock time        {}             ({} hr, {} min, {} sec)",
            wall_secs, wall_h, wall_m, wall_s
        )
        .unwrap();
    }

    /// Write completion message.
    pub fn write_completion(&mut self, proof_found: bool) {
        writeln!(&mut self.output).unwrap();
        if proof_found {
            writeln!(&mut self.output, "That finishes the proof of the theorem.")
                .unwrap();
        } else {
            writeln!(&mut self.output, "Search failed.").unwrap();
        }
    }
}

impl Default for OutputFormatter {
    fn default() -> Self {
        Self::new()
    }
}

/// Format a duration as (hours, minutes, seconds).
fn format_time(d: Duration) -> (u64, u64, u64) {
    let total_secs = d.as_secs();
    let hours = total_secs / 3600;
    let minutes = (total_secs % 3600) / 60;
    let seconds = total_secs % 60;
    (hours, minutes, seconds)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn format_statistics() {
        let mut formatter = OutputFormatter::new();
        let stats = ProverStats {
            clauses_given: 89,
            clauses_generated: 4909,
            clauses_kept: 1423,
            clauses_forward_subsumed: 3491,
            clauses_back_subsumed: 27,
            kbytes_malloced: 3906,
            ..Default::default()
        };

        formatter.write_statistics(&stats);
        let output = formatter.output();

        assert!(output.contains("clauses given"));
        assert!(output.contains("89"));
        assert!(output.contains("clauses generated"));
        assert!(output.contains("4909"));
    }

    #[test]
    fn format_times() {
        let mut formatter = OutputFormatter::new();
        let stats = ProverStats {
            user_cpu_time: Duration::from_millis(90),
            system_cpu_time: Duration::from_millis(10),
            wall_clock_time: Duration::from_secs(0),
            ..Default::default()
        };

        formatter.write_times(&stats);
        let output = formatter.output();

        assert!(output.contains("user CPU time"));
        assert!(output.contains("system CPU time"));
        assert!(output.contains("wall-clock time"));
    }

    #[test]
    fn format_proof_result() {
        let mut formatter = OutputFormatter::new();
        let result = ProofResult::Proof {
            empty_clause_id: crate::data::ClauseId(1),
            clauses_generated: 100,
            clauses_kept: 50,
        };

        formatter.write_result(&result);
        let output = formatter.output();

        assert!(output.contains("end of proof"));
    }
}
