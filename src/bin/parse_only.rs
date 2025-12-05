///! Test parsing only, without running the prover
use otters::regression::{ExampleSuite, RegressionExecutor};

fn main() {
    println!("=== Parse-Only Test ===\n");

    let suite = ExampleSuite::default();
    let inputs = suite.available_inputs().expect("Failed to find example inputs");
    println!("Found {} example input files", inputs.len());

    let executor = RegressionExecutor::new(suite);

    println!("\nRunning parse-only tests (no prover execution)...\n");

    let summary = executor.run_dry();

    println!("\n=== RESULTS ===");
    println!("Total examples: {}", summary.total());
    println!("Parse successes: {}", summary.successes);
    println!("Parse failures: {}", summary.parse_failures);
    println!("\nParse success rate: {:.1}%",
             (summary.successes as f64 / summary.total() as f64) * 100.0);

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
}
