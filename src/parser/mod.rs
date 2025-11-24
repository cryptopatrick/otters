//! Simplified parser for Otter input files.
//!
//! This module currently handles a subset of the Otter syntax—list declarations,
//! commands, and atomic clauses—providing a scaffolding that can be expanded as
//! more functionality is ported from the original `io.c` implementation.

mod syntax;
mod formula;
mod operator;

pub use syntax::{
    ListKind, ListSection, OtterCommand, OtterFile, ParseError, Parser,
    WeightEntry,
};
pub use formula::{Formula, parse_formula};
pub use operator::{Fixity, Operator, OperatorTable};
