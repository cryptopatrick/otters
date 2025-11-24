//! Rust re-implementation scaffolding for the Otter theorem prover.
//!
//! The crate is organized into foundational modules that mirror the original
//! Otter C layout while embracing Rust's type system.  Each module will grow to
//! encapsulate a cohesive portion of the prover as we port more logic.

pub mod config;
pub mod data;
pub mod inference;
pub mod parser;
pub mod regression;

pub use config::{Flag, FlagSet, ParameterSet, ParameterValue, Statistics};
pub use data::{
    Clause, ClauseArena, ClauseAttribute, ClauseAttributeValue, ClauseId,
    ClauseList, Context, ContextStatus, ImdBfs, ImdNode, ImdNodeKind, IsNode,
    Literal, MAX_VARS, ParentList, Symbol, SymbolId, SymbolKind, SymbolTable,
    Term, TermKind, VariableId,
};
pub use parser::{ListSection, OtterFile, ParseError, Parser};
pub use inference::{
    all_resolvents, apply_to_clause, apply_to_literal, binary_resolve,
    rename_variables, ProofResult, Prover, ProverBuilder, Resolvent, Substitution,
    UnificationError, Unifier,
};
pub use regression::{
    ExampleCase, ExampleSuite, ProverMetrics, RegressionExecutor,
    RegressionGroupSummary, RegressionResult, RegressionSummary,
};

#[cfg(test)]
mod tests {
    use super::regression::ExampleSuite;

    #[test]
    fn default_example_suite_exists() {
        let suite = ExampleSuite::default();
        assert!(suite.root().exists(), "example root must be present");
    }
}
