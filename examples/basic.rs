extern crate otters;
use otters::inference::{ProofResult, ProverBuilder};
use otters::parser::Parser;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <input-file>", args[0]);
        std::process::exit(1);
    }

    let input = fs::read_to_string(&args[1]).expect("failed to read input file");
    let parser = Parser::default();
    let file = parser.parse_str(&input).expect("failed to parse input");

    println!("Parsed {} commands, {} lists", file.commands.len(), file.lists.len());
    for list in &file.lists {
        println!("  List {:?} ({:?}): {} entries", list.name, list.kind, list.raw_entries.len());
    }

    let mut prover = ProverBuilder::new().build(&file).expect("failed to build prover");
    println!("\nConfiguration:");
    println!("  use_hyper_res: {}", prover.config().use_hyper_res);
    println!("  use_binary_res: {}", prover.config().use_binary_res);
    println!("\nStarting search...\n");

    let result = prover.search();
    let (generated, kept, given) = prover.stats();

    match result {
        ProofResult::Proof { empty_clause_id, .. } => {
            println!("PROOF FOUND! Empty clause id: {:?}", empty_clause_id);
        }
        ProofResult::Saturated { .. } => {
            println!("Search saturated (sos empty)");
        }
        ProofResult::ResourceLimit { limit_type, .. } => {
            println!("Resource limit: {}", limit_type);
        }
    }

    println!("\nStatistics:");
    println!("  clauses given:     {:>8}", given);
    println!("  clauses generated: {:>8}", generated);
    println!("  clauses kept:      {:>8}", kept);
}
