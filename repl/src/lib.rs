pub mod examples;
pub mod metta_surface;
pub mod pretty;
pub mod registry;
pub mod repl;
pub mod state;

// Re-export eqrel for the generated Ascent code
pub use ascent_byods_rels::eqrel;

pub use examples::Example;
pub use metta_surface::{normalize_input_for_language, prettify_output_for_language};
pub use pretty::format_term_pretty;
pub use registry::{build_registry, LanguageRegistry};
pub use repl::Repl;
pub use state::{HistoryEntry, ReplState};

// Re-export language types from runtime
pub use mettail_runtime::{
    AscentResults, EquivClass, Language, LanguageMetadata, Rewrite, Term, TermInfo,
};
