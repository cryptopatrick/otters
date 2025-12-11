//! Core data structures used throughout the prover.
//!
//! These types will eventually replace the structs defined in `types.h` from
//! the legacy implementation.  The definitions here are intentionally minimal
//! scaffolding that we can evolve as individual C modules are ported.

pub mod attribute;
pub mod clause;
pub mod clause_store;
pub mod context;
pub mod indexing;
pub mod list;
pub mod literal;
pub mod ordering;
pub mod parent;
pub mod symbol;
pub mod term;
pub mod weight;

pub use attribute::{ClauseAttribute, ClauseAttributeValue};
pub use clause::{Clause, ClauseId};
pub use clause_store::ClauseArena;
pub use context::{Context, ContextStatus, MAX_VARS, Trail};
pub use indexing::{ImdBfs, ImdNode, ImdNodeKind, IsNode, term_to_imd_kind};
pub use list::ClauseList;
pub use literal::Literal;
pub use ordering::LRPO;
pub use parent::ParentList;
pub use symbol::{Symbol, SymbolId, SymbolKind, SymbolTable};
pub use term::{Term, TermKind, VariableId};
pub use weight::WeightTable;
