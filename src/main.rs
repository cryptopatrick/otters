//! Otter theorem prover - Rust implementation.
//!
//! This is the main CLI entry point that mirrors the original Otter 3.3
//! command-line interface while using the Rust-based prover engine.
#![forbid(unsafe_code)]
use otters::{ExampleSuite, Parser, ProverBuilder, RegressionExecutor};
use std::env;
use std::fs;
use std::io::{self, Read};
use std::process;

const VERSION: &str = env!("CARGO_PKG_VERSION");
const OTTER_VERSION: &str = "3.3 (Rust port)";

fn print_banner() {
    println!("OTTER {} (version {})", OTTER_VERSION, VERSION);
    println!("Built with Rust - First-Order Logic Theorem Prover");
    println!();
}

fn print_usage(program: &str) {
    eprintln!("Usage: {} [options] [input-file]", program);
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -h, --help       Show this help message");
    eprintln!("  -v, --version    Show version information");
    eprintln!("  --regression     Run regression tests");
    eprintln!();
    eprintln!("If no input file is provided, reads from stdin.");
}

fn run_regression() -> io::Result<()> {
    println!("Running regression suite...\n");
    let suite = ExampleSuite::default();
    let executor = RegressionExecutor::new(suite);
    let summary = executor.run_dry();

    println!("{}", summary.render_table());
    println!();
    println!("Total: {} cases", summary.total());
    println!("Success: {} ({}%)",
             summary.successes,
             (summary.successes * 100) / summary.total().max(1));
    println!("Failures: {}", summary.failures);

    if summary.parse_failures > 0 {
        println!("Parse failures: {}", summary.parse_failures);
    }

    if summary.failures > 0 {
        println!("\nFailed cases:");
        for result in summary.iter_failures() {
            if let Some(name) = result.case.name() {
                println!("  - {}: {}",
                         name.to_string_lossy(),
                         result.error.as_deref().unwrap_or("output mismatch"));
            }
        }
        process::exit(1);
    }

    Ok(())
}

fn run_prover(input_path: Option<&str>) -> io::Result<()> {
    let parser = Parser::new();

    let input = if let Some(path) = input_path {
        fs::read_to_string(path)?
    } else {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer)?;
        buffer
    };

    match parser.parse_str(&input) {
        Ok(otter_file) => {
            println!("Parsed successfully:");
            println!("  Lists: {}", otter_file.lists.len());
            println!("  Commands: {}", otter_file.commands.len());
            println!();

            // Build and run the prover
            match ProverBuilder::new().build(&otter_file) {
                Ok(mut prover) => {
                    println!("Running prover...");
                    let result = prover.search();
                    println!();

                    match result {
                        otters::ProofResult::Proof { clauses_generated, clauses_kept, .. } => {
                            println!("PROOF FOUND");
                            println!("  Given: {}", prover.stats().2);
                            println!("  Generated: {}", clauses_generated);
                            println!("  Kept: {}", clauses_kept);
                            process::exit(0);
                        }
                        otters::ProofResult::ResourceLimit { clauses_generated, clauses_kept, limit_type } => {
                            println!("RESOURCE LIMIT REACHED: {}", limit_type);
                            println!("  Given: {}", prover.stats().2);
                            println!("  Generated: {}", clauses_generated);
                            println!("  Kept: {}", clauses_kept);
                            process::exit(3);
                        }
                        otters::ProofResult::Saturated { clauses_generated, clauses_kept } => {
                            println!("SEARCH SATURATED (no proof found)");
                            println!("  Given: {}", prover.stats().2);
                            println!("  Generated: {}", clauses_generated);
                            println!("  Kept: {}", clauses_kept);
                            process::exit(4);
                        }
                    }
                }
                Err(err) => {
                    eprintln!("Build error: {}", err);
                    process::exit(2);
                }
            }
        }
        Err(err) => {
            eprintln!("Parse error: {}", err);
            process::exit(2);
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let program = args[0].as_str();

    if args.len() > 1 {
        match args[1].as_str() {
            "-h" | "--help" => {
                print_usage(program);
                return;
            }
            "-v" | "--version" => {
                println!("{}", OTTER_VERSION);
                return;
            }
            "--regression" => {
                if let Err(err) = run_regression() {
                    eprintln!("Regression error: {}", err);
                    process::exit(1);
                }
                return;
            }
            _ => {}
        }
    }

    print_banner();

    let input_file = if args.len() > 1 && !args[1].starts_with('-') {
        Some(args[1].as_str())
    } else {
        None
    };

    if let Err(err) = run_prover(input_file) {
        eprintln!("Error: {}", err);
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn version_string_is_valid() {
        assert!(!OTTER_VERSION.is_empty());
        assert!(!VERSION.is_empty());
    }
}
