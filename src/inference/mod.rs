//! Inference engine components for the theorem prover.
//!
//! This module contains unification, resolution, and other inference rules
//! that form the core of the Otter prover.

mod builder;
mod demod;
mod factor;
mod hints;
mod hyper;
mod linked_ur;
mod output;
mod para;
mod prover;
mod resolution;
mod subsume;
mod unify;
mod unit_del;
mod ur;

pub use builder::ProverBuilder;
pub use demod::{
    demodulate_clause, demodulate_literal, demodulate_term, extract_demodulator,
    Demodulator,
};
pub use factor::{factor_clause, Factor};
pub use hints::{adjust_weight_with_hints, hint_keep_test, HintData, HintsList, MAX_WEIGHT};
pub use hyper::{
    hyperresolve, hyperresolve_units, neg_hyperresolve, neg_hyperresolve_units, HyperResolvent,
};
pub use linked_ur::{linked_ur_resolve, LinkedURConfig, LinkedURResolvent};
pub use output::{OutputFormatter, ProverStats};
pub use para::{paramodulate_into, Paramodulant};
pub use prover::{ProofResult, Prover, ProverConfig};
pub use resolution::{
    all_resolvents, apply_to_clause, apply_to_literal, binary_resolve,
    rename_variables, Resolvent,
};
pub use subsume::{back_subsumed, forward_subsumed, subsumes};
pub use unify::{unify, Substitution, UnificationError, Unifier};
pub use unit_del::{forward_unit_deletion, unit_delete, UnitDeleted};
pub use ur::{ur_resolve, URResolvent};
