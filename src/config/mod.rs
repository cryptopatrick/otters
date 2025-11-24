//! Configuration types describing flags, parameters, statistics, and related state.
//!
//! The original C implementation relies on large global arrays defined in
//! `header.h`.  The Rust port exposes structured containers that we can evolve
//! as functionality migrates.

mod flags;
mod params;
mod stats;

pub use flags::{Flag, FlagSet};
pub use params::{ParameterSet, ParameterValue};
pub use stats::Statistics;
