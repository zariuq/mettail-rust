//! Runtime support for MeTTaIL-generated code
//!
//! This crate provides:
//! - Variable binding support (via moniker wrappers)
//! - Collection types (HashBag for associative-commutative operations)
//! - Language metadata types for REPL introspection
//! - Core language traits (Term, AscentResults)
//! - Utility functions for parsing and variable management

// Variable binding support
mod binding;
pub use binding::*;

// Canonical float types for Float category (Eq/Hash/Ord)
mod canonical_float;
pub use canonical_float::{CanonicalFloat32, CanonicalFloat64};

// Collection types
mod hashbag;
pub use hashbag::HashBag;

// Language metadata for REPL introspection
mod metadata;
pub use metadata::*;

// Core language traits and types
mod language;
pub use language::*;

// Shared runtime execution policy types
mod policy;
pub use policy::*;

// Lean-generated optimization contract manifest types
pub mod manifest;
pub use manifest::OptManifest;

// Shared runtime diagnostics payloads
mod diagnostics;
pub use diagnostics::*;

// Generic frontier rewrite/search utilities
mod rewrite_search;
pub use rewrite_search::*;

// Generic re-entrant memoization helper
mod memo;
pub use memo::*;

// Shared immutable vector wrapper with lazy-cloning iteration
mod shared_vec;
pub use shared_vec::*;

// Generic rule candidate index
mod rule_index;
pub use rule_index::*;

// Generic mixed exact/pattern lookup-family index
mod lookup_family;
pub use lookup_family::*;

// Shared MeTTa-family matcher/substitution primitives
mod metta_family;
pub use metta_family::*;

// Shared MeTTa-family space index orchestration
mod metta_space_index;
pub use metta_space_index::*;

// Collision-safe hash/equality cache used by generated language helpers
mod hash_eq_cache;
pub use hash_eq_cache::*;

// Oracle query contract for external services/FFI-style integrations
mod oracle;
pub use oracle::*;

// Matchings enumeration for zip+map correlated search (used by generated rewrite clauses)
mod matchings;
pub use matchings::*;

// Shared bounded transition-graph runner for native backends.
mod transition_runner;
pub use transition_runner::*;

/// Wrapper that provides `Display` for slices/Vecs of `Display` items.
///
/// Renders as a comma-separated list, e.g. `a, b, c`.
/// Used by generated extraction code so `Vec<T>` columns get pretty-printed
/// via `T`'s `Display` impl rather than falling back to `Debug`.
pub struct DisplaySlice<'a, T>(pub &'a [T]);

impl<T: std::fmt::Display> std::fmt::Display for DisplaySlice<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, item) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}
