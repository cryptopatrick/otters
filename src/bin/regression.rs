///! Run regression tests and report results
use otters::regression::{ExampleSuite, RegressionExecutor};

fn main() {
    println!("=== Otter Rust Port - Regression Test Suite ===\n");

    let suite = ExampleSuite::default();

    // Quick validation
    let inputs = suite.available_inputs().expect("Failed to find example inputs");
    println!("Found {} example input files", inputs.len());

    let executor = RegressionExecutor::new(suite);

    println!("\nRunning regression tests...");
    println!("(Default limits: 500 given clauses, 5000 max clauses, 10 second timeout)\n");

    let start = std::time::Instant::now();
    let summary = executor.run_with_statistics();
    let elapsed = start.elapsed();

    println!("\n=== RESULTS ===");
    println!("Total examples: {}", summary.total());
    println!("Successes: {}", summary.successes);
    println!("Failures: {}", summary.failures);
    println!("Parse failures: {}", summary.parse_failures);
    println!("Time elapsed: {:.2}s", elapsed.as_secs_f64());
    println!("\nSuccess rate: {:.1}%",
             (summary.successes as f64 / summary.total() as f64) * 100.0);

    if summary.failures > 0 {
        println!("\n=== FAILURES (first 20) ===");
        let mut count = 0;
        for result in &summary.results {
            if !result.success && count < 20 {
                count += 1;
                if let Some(name) = result.case.name() {
                    println!("\n{}. {:?}:", count, name);
                    if let Some(err) = &result.error {
                        println!("   Error: {}", err);
                    }
                    if !result.differences.is_empty() {
                        println!("   Differences from expected:");
                        for diff in &result.differences {
                            println!("     - {}", diff);
                        }
                    }
                }
            }
        }
        if summary.failures > 20 {
            println!("\n... and {} more failures", summary.failures - 20);
        }
    }

    // Print all parse failures
    if summary.parse_failures > 0 {
        println!("\n=== PARSE FAILURES ({}) ===", summary.parse_failures);
        let mut count = 0;
        for result in &summary.results {
            if let Some(err) = &result.error {
                count += 1;
                if let Some(name) = result.case.name() {
                    println!("\n{}. {:?}", count, name);
                    println!("   Error: {}", err);
                }
            }
        }
    }

    println!("\n=== Complete ===");

    // Exit with error code if there were failures
    if summary.failures > 0 {
        std::process::exit(1);
    }
}
