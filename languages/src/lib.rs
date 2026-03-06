// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated parser code may include unused imports
)]

pub mod ambient;
pub mod artifact_contract;
pub mod calculator;
pub mod imp_artifacts;
pub mod imp_from_lean;
pub mod lambda;
pub mod mettafull_legacy;
pub mod mettahe_artifacts;
pub mod mettahe_from_lean;
pub mod minskylite_artifacts;
pub mod minskylite_from_lean;
pub mod mm0lite_artifacts;
pub mod mm0lite_from_lean;
pub mod native_transition_contract;
pub mod pyashcore_from_lean;
pub mod rhocalc;

#[cfg(feature = "mork-backend")]
pub mod mork_backend;

/// Register native core backend adapters exported by this language bundle.
///
/// This keeps backend wiring language-agnostic at runtime: dispatch resolves by
/// `(language_name, backend)` registration, not REPL-level special cases.
#[cfg(feature = "mork-backend")]
pub fn register_default_core_backends() -> Result<(), String> {
    mettail_runtime::register_mork_backend_runner(
        "IMP",
        imp_from_lean::run_imp_mork_backend,
        true,
    )?;
    mettail_runtime::register_mork_backend_runner(
        "MeTTaHE",
        mettahe_from_lean::run_mettahe_mork_backend,
        true,
    )?;
    mettail_runtime::register_mork_backend_runner(
        "MM0Lite",
        mm0lite_from_lean::run_mm0lite_mork_backend,
        true,
    )?;
    mettail_runtime::register_mork_backend_runner(
        "MinskyLite",
        minskylite_from_lean::run_minskylite_mork_backend,
        true,
    )?;
    Ok(())
}

#[cfg(not(feature = "mork-backend"))]
pub fn register_default_core_backends() -> Result<(), String> {
    Ok(())
}

// Re-export eqrel for the generated Ascent code
// The generated code uses `#[ds(crate::eqrel)]` which expects eqrel at crate root
pub use ascent_byods_rels::eqrel;

// Re-export the aliased macro names from the modules
pub use ambient::ambient_source;
pub use calculator::calculator_source;
pub use lambda::lambda_source;
pub use pyashcore_from_lean::{
    pyashcore_classify_state_display, pyashcore_predict_terminal_class_from_display,
    pyashcore_project_trace, pyashcore_select_single_trace, pyashcore_smoke_case,
    PyashCoreLanguage, PyashStructuralOutcomeClass, PyashTraceMode, PYASHCORE_SMOKE_EXPECTED,
    PYASHCORE_SMOKE_INPUT,
};
pub use rhocalc::rhocalc_source;

// Note: Different languages may export types with the same names (e.g., Proc, Term)
// Users should import from specific modules to avoid ambiguity:
//   use mettail_languages::rhocalc::*;
//   use mettail_languages::ambient::*;
//   use mettail_languages::lambda::*;
