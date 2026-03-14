#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr,
    clippy::type_complexity,
    non_camel_case_types,
    non_local_definitions,
    non_snake_case,
    unused_imports
)]

pub use ascent_byods_rels::eqrel;

#[path = "../../languages/src/artifact_contract.rs"]
pub mod artifact_contract;
#[path = "../../languages/src/mettahe_artifacts.rs"]
pub mod mettahe_artifacts;
// DELETED: native_transition_contract.rs was a hand-written PathMap reimplementation.
// #[path = "../../languages/src/native_transition_contract.rs"]
// pub mod native_transition_contract;
#[path = "../../languages/src/rewrite_template.rs"]
pub mod rewrite_template;
#[path = "../../languages/src/mork_backend.rs"]
pub mod mork_backend;
#[path = "../../languages/src/mettahe_from_lean.rs"]
pub mod mettahe_from_lean;
