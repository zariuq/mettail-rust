// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated parser code may include unused imports
)]

#[cfg(feature = "lang-ambient")]
pub mod ambient;
pub mod artifact_contract;
pub mod compat_head_boundary;
// DELETED: artifact_runtime.rs was built on native_transition_contract (hand-written PathMap).
// pub mod artifact_runtime;
#[cfg(feature = "lang-calculator")]
pub mod calculator;
pub mod execution_contract;
#[cfg(feature = "lang-imp")]
pub mod imp_artifacts;
#[cfg(feature = "lang-imp")]
pub mod imp_from_lean;
#[cfg(feature = "lang-imp")]
pub mod imp_surface;
#[cfg(feature = "lang-lambda")]
pub mod lambda;
pub mod metta_file;
#[cfg(feature = "lang-mettafull-legacy")]
pub mod mettafull_legacy;
#[cfg(feature = "lang-he")]
pub mod mettahe_artifacts;
#[cfg(feature = "lang-he")]
pub mod mettahe_from_lean;
#[cfg(feature = "lang-he")]
pub mod mettahe_surface;
#[cfg(feature = "lang-minskylite")]
pub mod minskylite_artifacts;
#[cfg(feature = "lang-minskylite")]
pub mod minskylite_from_lean;
#[cfg(feature = "lang-mm0lite")]
pub mod mm0lite_artifacts;
#[cfg(feature = "lang-mm0lite")]
pub mod mm0lite_from_lean;
// DELETED: native_transition_contract.rs was a hand-written MM2 rule dispatcher.
// All execution must go through mork::space::Space::metta_calculus() via MM2.
// pub mod native_transition_contract;
#[cfg(feature = "lang-petta")]
pub mod petta_artifacts;
#[cfg(feature = "lang-petta")]
pub mod petta_from_lean;
#[cfg(feature = "lang-pyashcore")]
pub mod pyashcore_from_lean;
pub mod rewrite_template;
pub mod scope_contract;
#[cfg(feature = "lang-rhocalc")]
pub mod rhocalc;
pub mod sexpr;
pub mod tree_sitter_parser;

#[cfg(feature = "mork-backend")]
pub mod mork_backend;

/// Register native core backend adapters exported by this language bundle.
///
/// This keeps backend wiring language-agnostic at runtime: dispatch resolves by
/// `(language_name, backend)` registration, not REPL-level special cases.
// Re-register only language backends that execute through real MM2 ->
// mork::space::Space::metta_calculus(). The deleted native-transition path
// must not be reintroduced here.
#[cfg(feature = "mork-backend")]
pub fn register_default_core_backends() -> Result<(), String> {
    #[cfg(feature = "lang-petta")]
    mettail_runtime::register_mork_backend_runner(
        "PeTTa",
        petta_from_lean::run_petta_mork_backend,
        true,
    )?;

    Ok(())
}

#[cfg(not(feature = "mork-backend"))]
pub fn register_default_core_backends() -> Result<(), String> {
    Ok(())
}

// Re-export eqrel only when macro-generated Ascent languages are enabled.
// The generated code uses `#[ds(crate::eqrel)]` which expects eqrel at crate root.
#[cfg(feature = "ascent-support")]
pub use ascent_byods_rels::eqrel;

// Re-export the aliased macro names from the modules
#[cfg(feature = "lang-ambient")]
pub use ambient::ambient_source;
#[cfg(feature = "lang-calculator")]
pub use calculator::calculator_source;
#[cfg(feature = "lang-lambda")]
pub use lambda::lambda_source;
#[cfg(feature = "lang-pyashcore")]
pub use pyashcore_from_lean::{
    pyashcore_classify_state_display, pyashcore_predict_terminal_class_from_display,
    pyashcore_project_trace, pyashcore_select_single_trace, pyashcore_smoke_case,
    PyashCoreLanguage, PyashStructuralOutcomeClass, PyashTraceMode, PYASHCORE_SMOKE_EXPECTED,
    PYASHCORE_SMOKE_INPUT,
};
#[cfg(feature = "lang-rhocalc")]
pub use rhocalc::rhocalc_source;

// Note: Different languages may export types with the same names (e.g., Proc, Term)
// Users should import from specific modules to avoid ambiguity:
//   use mettail_languages::rhocalc::*;
//   use mettail_languages::ambient::*;
//   use mettail_languages::lambda::*;
