use super::{ExampleCase, ExampleSuite};
use crate::inference::{ProofResult, ProverBuilder, ProverConfig};
use crate::parser::Parser;
use std::collections::HashMap;

/// Key statistics extracted from an Otter output file.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProverMetrics {
    pub clauses_given: Option<u64>,
    pub clauses_generated: Option<u64>,
    pub clauses_kept: Option<u64>,
    pub clauses_forward_subsumed: Option<u64>,
    pub clauses_back_subsumed: Option<u64>,
    pub kbytes_malloced: Option<u64>,
    pub user_cpu_time: Option<f64>,
    pub proof_found: Option<bool>,
    pub proof_length: Option<usize>,
}

impl ProverMetrics {
    /// Parse statistics from Otter output text.
    pub fn from_output(output: &str) -> Self {
        let mut metrics = Self::default();

        for line in output.lines() {
            let trimmed = line.trim();

            // Parse statistics section values
            if let Some(value) = extract_stat(trimmed, "clauses given") {
                metrics.clauses_given = value.parse().ok();
            } else if let Some(value) = extract_stat(trimmed, "clauses generated") {
                metrics.clauses_generated = value.parse().ok();
            } else if let Some(value) = extract_stat(trimmed, "clauses kept") {
                metrics.clauses_kept = value.parse().ok();
            } else if let Some(value) = extract_stat(trimmed, "clauses forward subsumed") {
                metrics.clauses_forward_subsumed = value.parse().ok();
            } else if let Some(value) = extract_stat(trimmed, "clauses back subsumed") {
                metrics.clauses_back_subsumed = value.parse().ok();
            } else if let Some(value) = extract_stat(trimmed, "Kbytes malloced") {
                metrics.kbytes_malloced = value.parse().ok();
            } else if trimmed.starts_with("user CPU time") {
                // Format: "user CPU time          0.09          (0 hr, 0 min, 0 sec)"
                if let Some(time_str) = trimmed.split_whitespace().nth(3) {
                    metrics.user_cpu_time = time_str.parse().ok();
                }
            }

            // Check for proof markers
            if trimmed.contains("$Ans(") || trimmed.contains("end of proof") {
                metrics.proof_found = Some(true);
            }

            // Count proof length from numbered clauses in proof
            if trimmed.starts_with('[') && trimmed.contains("hyper,")
                || trimmed.contains("binary,")
                || trimmed.contains("para_into,")
            {
                *metrics.proof_length.get_or_insert(0) += 1;
            }
        }

        // If we never found proof markers, set to false
        if metrics.proof_found.is_none() && metrics.clauses_generated.is_some() {
            metrics.proof_found = Some(false);
        }

        metrics
    }

    /// Compare two metrics and return a list of differences.
    pub fn compare(&self, other: &ProverMetrics) -> Vec<String> {
        let mut diffs = Vec::new();

        if self.clauses_generated != other.clauses_generated {
            diffs.push(format!(
                "clauses_generated: {:?} vs {:?}",
                self.clauses_generated, other.clauses_generated
            ));
        }
        if self.clauses_kept != other.clauses_kept {
            diffs.push(format!(
                "clauses_kept: {:?} vs {:?}",
                self.clauses_kept, other.clauses_kept
            ));
        }
        if self.clauses_given != other.clauses_given {
            diffs.push(format!(
                "clauses_given: {:?} vs {:?}",
                self.clauses_given, other.clauses_given
            ));
        }
        if self.proof_found != other.proof_found {
            diffs.push(format!(
                "proof_found: {:?} vs {:?}",
                self.proof_found, other.proof_found
            ));
        }

        diffs
    }
}

/// Extract the numeric value from a statistics line.
fn extract_stat<'a>(line: &'a str, prefix: &str) -> Option<&'a str> {
    if line.starts_with(prefix) {
        line[prefix.len()..].split_whitespace().next()
    } else {
        None
    }
}

/// Result of running a regression case.
#[derive(Clone, Debug, PartialEq)]
pub struct RegressionResult {
    pub case: ExampleCase,
    pub success: bool,
    pub differences: Vec<String>,
    pub error: Option<String>,
    pub expected_metrics: Option<ProverMetrics>,
    pub actual_metrics: Option<ProverMetrics>,
}

/// Aggregated summary describing the outcome of a regression run.
#[derive(Clone, Debug, PartialEq)]
pub struct RegressionSummary {
    pub results: Vec<RegressionResult>,
    pub successes: usize,
    pub failures: usize,
    pub parse_failures: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegressionGroupSummary {
    pub group: String,
    pub successes: usize,
    pub failures: usize,
}

impl RegressionSummary {
    pub fn from_results(results: Vec<RegressionResult>) -> Self {
        let mut successes = 0usize;
        let mut failures = 0usize;
        let mut parse_failures = 0usize;
        for result in &results {
            if result.success {
                successes += 1;
            } else {
                failures += 1;
                if result.error.is_some() {
                    parse_failures += 1;
                }
            }
        }
        Self { results, successes, failures, parse_failures }
    }

    pub fn total(&self) -> usize {
        self.results.len()
    }

    pub fn iter_failures(&self) -> impl Iterator<Item = &RegressionResult> {
        self.results.iter().filter(|result| !result.success)
    }

    pub fn by_group(&self) -> Vec<RegressionGroupSummary> {
        let mut grouped: HashMap<String, RegressionGroupSummary> =
            HashMap::new();
        for result in &self.results {
            let group = result
                .case
                .input
                .parent()
                .and_then(|p| p.file_name())
                .and_then(|os| os.to_str())
                .unwrap_or("root")
                .to_string();
            let entry = grouped.entry(group.clone()).or_insert(
                RegressionGroupSummary { group, successes: 0, failures: 0 },
            );
            if result.success {
                entry.successes += 1;
            } else {
                entry.failures += 1;
            }
        }
        let mut summaries: Vec<_> = grouped.into_values().collect();
        summaries.sort_by(|a, b| a.group.cmp(&b.group));
        summaries
    }

    pub fn render_table(&self) -> String {
        let groups = self.by_group();
        if groups.is_empty() {
            return String::from("(no regression cases)");
        }
        let mut lines = Vec::new();
        lines.push(format!(
            "{:<20} {:>7} {:>7}",
            "Group", "Success", "Failure"
        ));
        for summary in groups {
            lines.push(format!(
                "{:<20} {:>7} {:>7}",
                summary.group, summary.successes, summary.failures
            ));
        }
        lines.join("\n")
    }
}

/// Skeleton executor that will orchestrate example-driven tests.
#[derive(Clone, Debug)]
pub struct RegressionExecutor {
    suite: ExampleSuite,
    parser: Parser,
}

impl RegressionExecutor {
    pub fn new(suite: ExampleSuite) -> Self {
        Self { suite, parser: Parser::new() }
    }

    pub fn suite(&self) -> &ExampleSuite {
        &self.suite
    }

    /// Run a dry comparison that currently only validates that each input file
    /// can be parsed by the Rust parser.
    pub fn run_dry(&self) -> RegressionSummary {
        let mut results = Vec::new();
        if let Ok(cases) = self.suite.available_cases() {
            for case in cases {
                let input = match case.load_input() {
                    Ok(content) => content,
                    Err(err) => {
                        results.push(RegressionResult {
                            case,
                            success: false,
                            differences: Vec::new(),
                            error: Some(format!(
                                "failed to load input: {}",
                                err
                            )),
                            expected_metrics: None,
                            actual_metrics: None,
                        });
                        continue;
                    }
                };
                let outcome = match self.parser.parse_str(&input) {
                    Ok(_) => RegressionResult {
                        case,
                        success: true,
                        differences: Vec::new(),
                        error: None,
                        expected_metrics: None,
                        actual_metrics: None,
                    },
                    Err(err) => RegressionResult {
                        case,
                        success: false,
                        differences: Vec::new(),
                        error: Some(err.to_string()),
                        expected_metrics: None,
                        actual_metrics: None,
                    },
                };
                results.push(outcome);
            }
        }
        RegressionSummary::from_results(results)
    }

    /// Run a statistics-based comparison.
    ///
    /// This method parses golden outputs and validates that expected metrics
    /// can be extracted. When the prover is fully implemented, this will
    /// compare actual vs expected metrics.
    pub fn run_with_statistics(&self) -> RegressionSummary {
        let mut results = Vec::new();
        if let Ok(cases) = self.suite.available_cases() {
            for case in cases {
                // Load and parse input
                let input = match case.load_input() {
                    Ok(content) => content,
                    Err(err) => {
                        results.push(RegressionResult {
                            case,
                            success: false,
                            differences: Vec::new(),
                            error: Some(format!("failed to load input: {}", err)),
                            expected_metrics: None,
                            actual_metrics: None,
                        });
                        continue;
                    }
                };

                // Check parsing
                if let Err(err) = self.parser.parse_str(&input) {
                    results.push(RegressionResult {
                        case,
                        success: false,
                        differences: Vec::new(),
                        error: Some(err.to_string()),
                        expected_metrics: None,
                        actual_metrics: None,
                    });
                    continue;
                }

                // Load expected output and extract metrics
                let expected_metrics = match case.load_expected_output() {
                    Ok(Some(output)) => Some(ProverMetrics::from_output(&output)),
                    Ok(None) => None,
                    Err(err) => {
                        results.push(RegressionResult {
                            case,
                            success: false,
                            differences: Vec::new(),
                            error: Some(format!("failed to load expected output: {}", err)),
                            expected_metrics: None,
                            actual_metrics: None,
                        });
                        continue;
                    }
                };

                // Build and run the prover
                let file = match self.parser.parse_str(&input) {
                    Ok(f) => f,
                    Err(err) => {
                        results.push(RegressionResult {
                            case,
                            success: false,
                            differences: Vec::new(),
                            error: Some(err.to_string()),
                            expected_metrics,
                            actual_metrics: None,
                        });
                        continue;
                    }
                };

                let mut prover = match ProverBuilder::new().build(&file) {
                    Ok(mut p) => {
                        // Use reasonable limits for regression testing
                        // If the input file didn't specify limits, use generous defaults
                        // to allow proofs to be found (matching original Otter behavior)
                        let config = p.config();
                        if config.max_given == 1000 { // default value
                            // Use moderate limits: enough to find many proofs, fast enough for CI
                            *p.config_mut() = ProverConfig {
                                max_given: 500,       // Moderate: 5x original, but reasonable
                                max_clauses: 5000,    // 5x original
                                max_seconds: 10,      // Time limit to prevent hangs
                                ..config.clone()
                            };
                        }
                        p
                    }
                    Err(err) => {
                        results.push(RegressionResult {
                            case,
                            success: false,
                            differences: Vec::new(),
                            error: Some(err),
                            expected_metrics,
                            actual_metrics: None,
                        });
                        continue;
                    }
                };

                // Run the prover with timeout (5 seconds per example)
                // Note: Rust doesn't have built-in timeout for sync code,
                // so we rely on the prover's max_seconds limit
                let proof_result = prover.search();
                let (generated, kept, given) = prover.stats();

                // Build actual metrics
                let actual_metrics = Some(ProverMetrics {
                    clauses_given: Some(given as u64),
                    clauses_generated: Some(generated as u64),
                    clauses_kept: Some(kept as u64),
                    proof_found: Some(matches!(proof_result, ProofResult::Proof { .. })),
                    ..Default::default()
                });

                // Compare metrics
                let (success, differences) = if let Some(ref expected) = expected_metrics {
                    let diffs = expected.compare(actual_metrics.as_ref().unwrap());
                    (diffs.is_empty(), diffs)
                } else {
                    // No expected output to compare against
                    (true, Vec::new())
                };

                results.push(RegressionResult {
                    case,
                    success,
                    differences,
                    error: None,
                    expected_metrics,
                    actual_metrics,
                });
            }
        }
        RegressionSummary::from_results(results)
    }

    /// Normalise output strings before diffing.
    pub fn normalise_output(&self, output: &str) -> String {
        output
            .lines()
            .map(str::trim_end)
            .filter(|line| !line.trim().is_empty())
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Compare outputs and return per-line differences.
    pub fn diff_outputs(&self, expected: &str, actual: &str) -> Vec<String> {
        let normal_expected = self.normalise_output(expected);
        let normal_actual = self.normalise_output(actual);
        let expected_lines: Vec<_> = normal_expected.lines().collect();
        let actual_lines: Vec<_> = normal_actual.lines().collect();
        let mut diff = Vec::new();
        let max_len = expected_lines.len().max(actual_lines.len());
        for idx in 0..max_len {
            let left = expected_lines.get(idx).copied().unwrap_or("");
            let right = actual_lines.get(idx).copied().unwrap_or("");
            if left != right {
                diff.push(format!(
                    "line {}: '{}' != '{}'",
                    idx + 1,
                    left,
                    right
                ));
            }
        }
        diff
    }

    /// Group cases by directory to emulate the legacy `Run_group` script.
    pub fn group_cases(&self) -> HashMap<String, Vec<ExampleCase>> {
        let mut groups: HashMap<String, Vec<ExampleCase>> = HashMap::new();
        if let Ok(cases) = self.suite.available_cases() {
            for case in cases {
                let group = case
                    .input
                    .parent()
                    .and_then(|path| path.file_name())
                    .and_then(|os| os.to_str())
                    .unwrap_or("root")
                    .to_string();
                groups.entry(group).or_default().push(case);
            }
        }
        groups
    }
}

#[cfg(test)]
mod tests {
    use super::{ProverMetrics, RegressionExecutor};
    use crate::regression::ExampleSuite;

    #[test]
    fn dry_run_parses_inputs() {
        let executor = RegressionExecutor::new(ExampleSuite::default());
        let summary = executor.run_dry();
        assert!(summary.total() > 0, "expected regression cases");
        assert_eq!(summary.successes + summary.failures, summary.total());
    }

    #[test]
    fn diff_outputs_detects_changes() {
        let executor = RegressionExecutor::new(ExampleSuite::default());
        let diffs = executor.diff_outputs("a\n", "b\n");
        assert_eq!(diffs.len(), 1);
    }

    #[test]
    fn group_cases_by_directory() {
        let executor = RegressionExecutor::new(ExampleSuite::default());
        let groups = executor.group_cases();
        assert!(!groups.is_empty());
    }

    #[test]
    fn summary_renders_table() {
        let executor = RegressionExecutor::new(ExampleSuite::default());
        let summary = executor.run_dry();
        let table = summary.render_table();
        assert!(table.contains("Group"));
    }

    #[test]
    fn prover_metrics_parses_statistics() {
        let output = r#"
-------------- statistics -------------
clauses given                 89
clauses generated           4909
clauses kept                1423
clauses forward subsumed    3491
clauses back subsumed         27
Kbytes malloced             3906

----------- times (seconds) -----------
user CPU time          0.09          (0 hr, 0 min, 0 sec)
system CPU time        0.01          (0 hr, 0 min, 0 sec)

1424 [binary,1423.1,2.1] $Ans(CN_19).
------------ end of proof -------------
"#;
        let metrics = ProverMetrics::from_output(output);
        assert_eq!(metrics.clauses_given, Some(89));
        assert_eq!(metrics.clauses_generated, Some(4909));
        assert_eq!(metrics.clauses_kept, Some(1423));
        assert_eq!(metrics.clauses_forward_subsumed, Some(3491));
        assert_eq!(metrics.clauses_back_subsumed, Some(27));
        assert_eq!(metrics.kbytes_malloced, Some(3906));
        assert_eq!(metrics.user_cpu_time, Some(0.09));
        assert_eq!(metrics.proof_found, Some(true));
    }

    #[test]
    fn prover_metrics_compare_detects_differences() {
        let mut m1 = ProverMetrics::default();
        m1.clauses_generated = Some(100);
        m1.clauses_kept = Some(50);

        let mut m2 = ProverMetrics::default();
        m2.clauses_generated = Some(100);
        m2.clauses_kept = Some(60);

        let diffs = m1.compare(&m2);
        assert_eq!(diffs.len(), 1);
        assert!(diffs[0].contains("clauses_kept"));
    }

    #[test]
    fn prover_metrics_from_real_golden_output() {
        let suite = ExampleSuite::default();
        let cases = suite.available_cases().expect("load cases");
        // Find a case with expected output
        let case_with_output = cases.iter().find(|c| c.expected_output.is_some());
        if let Some(case) = case_with_output {
            let output = case
                .load_expected_output()
                .expect("load output")
                .expect("has output");
            let metrics = ProverMetrics::from_output(&output);
            // All golden outputs should have at least clauses_generated
            assert!(
                metrics.clauses_generated.is_some(),
                "expected clauses_generated in golden output"
            );
        }
    }

    #[test]
    fn run_with_statistics_extracts_metrics() {
        let executor = RegressionExecutor::new(ExampleSuite::default());
        let summary = executor.run_with_statistics();
        // Should have same total as dry run
        assert!(summary.total() > 0);
        // Most cases should have extractable metrics
        assert!(summary.successes > 0, "expected some cases with metrics");
    }
}
