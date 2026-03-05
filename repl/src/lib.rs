pub mod examples;
pub mod grammar_spec;
pub mod lookup_plan;
pub mod metta_surface;
pub mod metta_surface_he;
pub mod pretty;
pub mod registry;
pub mod repl;
pub mod run_metta_file;
pub mod state;
pub mod syntax_spec;

// Re-export eqrel for the generated Ascent code
pub use ascent_byods_rels::eqrel;

#[cfg(test)]
pub(crate) mod test_env;

pub use examples::Example;
pub use pretty::format_term_pretty;
pub use registry::{build_registry, LanguageRegistry};
pub use repl::Repl;
pub use state::{HistoryEntry, ReplState};

// Re-export language types from runtime
pub use mettail_runtime::{
    AscentResults, EquivClass, Language, LanguageMetadata, Rewrite, Term, TermInfo,
};
