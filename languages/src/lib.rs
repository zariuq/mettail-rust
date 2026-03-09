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
#[cfg(feature = "lang-calculator")]
pub mod calculator;
#[cfg(feature = "lang-imp")]
pub mod imp_artifacts;
#[cfg(feature = "lang-imp")]
pub mod imp_from_lean;
#[cfg(feature = "lang-imp")]
pub mod imp_surface;
#[cfg(feature = "lang-lambda")]
pub mod lambda;
#[cfg(feature = "lang-mettafull-legacy")]
pub mod mettafull_legacy;
#[cfg(feature = "lang-he")]
pub mod mettahe_artifacts;
#[cfg(feature = "lang-he")]
pub mod mettahe_from_lean;
#[cfg(feature = "lang-minskylite")]
pub mod minskylite_artifacts;
#[cfg(feature = "lang-minskylite")]
pub mod minskylite_from_lean;
#[cfg(feature = "lang-mm0lite")]
pub mod mm0lite_artifacts;
#[cfg(feature = "lang-mm0lite")]
pub mod mm0lite_from_lean;
pub mod native_transition_contract;
#[cfg(feature = "lang-petta")]
pub mod petta_artifacts;
#[cfg(feature = "lang-petta")]
pub mod petta_from_lean;
#[cfg(feature = "lang-pyashcore")]
pub mod pyashcore_from_lean;
pub mod rewrite_template;
#[cfg(feature = "lang-rhocalc")]
pub mod rhocalc;

#[cfg(feature = "mork-backend")]
pub mod mork_backend;

/// Register native core backend adapters exported by this language bundle.
///
/// This keeps backend wiring language-agnostic at runtime: dispatch resolves by
/// `(language_name, backend)` registration, not REPL-level special cases.
#[cfg(feature = "mork-backend")]
pub fn register_default_core_backends() -> Result<(), String> {
    #[cfg(feature = "lang-imp")]
    mettail_runtime::register_mork_backend_runner(
        "IMP",
        imp_from_lean::run_imp_mork_backend,
        true,
    )?;
    #[cfg(feature = "lang-he")]
    mettail_runtime::register_mork_backend_runner(
        "MeTTaHE",
        mettahe_from_lean::run_mettahe_mork_backend,
        true,
    )?;
    #[cfg(feature = "lang-mm0lite")]
    mettail_runtime::register_mork_backend_runner(
        "MM0Lite",
        mm0lite_from_lean::run_mm0lite_mork_backend,
        true,
    )?;
    #[cfg(feature = "lang-minskylite")]
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
