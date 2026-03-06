#![allow(
    non_local_definitions,
    non_camel_case_types,
    non_snake_case,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

include!("generated/minskylite_language_working.rs");

#[cfg(feature = "mork-backend")]
use crate::minskylite_artifacts::{
    load_minskylite_lookup_artifact, load_minskylite_rewrite_ir_artifact,
    load_minskylite_transition_artifact, minskylite_artifact_dir,
};
#[cfg(feature = "mork-backend")]
use crate::native_transition_contract::{
    build_native_transition_contract, NativeTransitionContract, NativeTransitionRuleMeta,
};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{
    dispatch_ordered_rules, run_transition_graph, AscentResults, MorkExecutionLimits, Term,
};
#[cfg(feature = "mork-backend")]
use std::sync::OnceLock;
#[cfg(feature = "mork-backend")]
use std::time::Instant;

#[cfg(feature = "mork-backend")]
fn minskylite_rewrite_contract() -> Result<&'static NativeTransitionContract, String> {
    static CONTRACT: OnceLock<Result<NativeTransitionContract, String>> = OnceLock::new();
    match CONTRACT.get_or_init(|| {
        let dir = minskylite_artifact_dir();
        let transition = load_minskylite_transition_artifact(&dir)?;
        let lookup = load_minskylite_lookup_artifact(&dir)?;
        let rewrite_ir = load_minskylite_rewrite_ir_artifact(&dir)?;
        build_native_transition_contract("MinskyLite", transition, lookup, rewrite_ir, |lookup| {
            if lookup.families.is_empty() {
                Ok(())
            } else {
                Err("MinskyLite lookup-plan should be empty for current core semantics".to_string())
            }
        })
    }) {
        Ok(contract) => Ok(contract),
        Err(err) => Err(err.clone()),
    }
}

#[cfg(feature = "mork-backend")]
fn minsky_source_instr(ctrl: &Control) -> Option<&'static str> {
    match ctrl {
        Control::C_IncA(_) => Some("C_IncA"),
        Control::C_IncB(_) => Some("C_IncB"),
        Control::C_DecA(_, _) => Some("C_DecA"),
        Control::C_DecB(_, _) => Some("C_DecB"),
        Control::C_Halt => Some("C_Halt"),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn running_status() -> Box<Status> {
    Box::new(Status::C_Running)
}

#[cfg(feature = "mork-backend")]
fn done_status() -> Box<Status> {
    Box::new(Status::C_Done)
}

#[cfg(feature = "mork-backend")]
fn succ_nat(n: &Nat) -> Box<Nat> {
    Box::new(Nat::C_Succ(Box::new(n.clone())))
}

#[cfg(feature = "mork-backend")]
fn minsky_apply_rule(
    meta: &NativeTransitionRuleMeta,
    ctrl: &Control,
    reg_a: &Nat,
    reg_b: &Nat,
) -> Result<Vec<Machine>, String> {
    let next_machine = match meta.transition_kind.as_str() {
        "increment" => {
            if meta.guard_family != "none" || meta.effect_kind != "advance_machine" {
                return Err(format!(
                    "MinskyLite increment contract mismatch for rule '{}' (logical id '{}'): guard='{}', effect='{}'",
                    meta.rule_id, meta.logical_transition_id, meta.guard_family, meta.effect_kind
                ));
            }
            match ctrl {
                Control::C_IncA(next) => Some(Machine::C_Machine(
                    next.clone(),
                    succ_nat(reg_a),
                    Box::new(reg_b.clone()),
                    running_status(),
                )),
                Control::C_IncB(next) => Some(Machine::C_Machine(
                    next.clone(),
                    Box::new(reg_a.clone()),
                    succ_nat(reg_b),
                    running_status(),
                )),
                _ => None,
            }
        },
        "branch_zero" => {
            if meta.guard_family != "zero" || meta.effect_kind != "advance_machine" {
                return Err(format!(
                    "MinskyLite zero-branch contract mismatch for rule '{}' (logical id '{}'): guard='{}', effect='{}'",
                    meta.rule_id, meta.logical_transition_id, meta.guard_family, meta.effect_kind
                ));
            }
            match ctrl {
                Control::C_DecA(zero_next, _) if matches!(reg_a, Nat::C_Zero) => {
                    Some(Machine::C_Machine(
                        zero_next.clone(),
                        Box::new(Nat::C_Zero),
                        Box::new(reg_b.clone()),
                        running_status(),
                    ))
                },
                Control::C_DecB(zero_next, _) if matches!(reg_b, Nat::C_Zero) => {
                    Some(Machine::C_Machine(
                        zero_next.clone(),
                        Box::new(reg_a.clone()),
                        Box::new(Nat::C_Zero),
                        running_status(),
                    ))
                },
                _ => None,
            }
        },
        "branch_positive" => {
            if meta.guard_family != "positive" || meta.effect_kind != "advance_machine" {
                return Err(format!(
                    "MinskyLite positive-branch contract mismatch for rule '{}' (logical id '{}'): guard='{}', effect='{}'",
                    meta.rule_id, meta.logical_transition_id, meta.guard_family, meta.effect_kind
                ));
            }
            match ctrl {
                Control::C_DecA(_, succ_next) => {
                    if let Nat::C_Succ(prev_a) = reg_a {
                        Some(Machine::C_Machine(
                            succ_next.clone(),
                            prev_a.clone(),
                            Box::new(reg_b.clone()),
                            running_status(),
                        ))
                    } else {
                        None
                    }
                },
                Control::C_DecB(_, succ_next) => {
                    if let Nat::C_Succ(prev_b) = reg_b {
                        Some(Machine::C_Machine(
                            succ_next.clone(),
                            Box::new(reg_a.clone()),
                            prev_b.clone(),
                            running_status(),
                        ))
                    } else {
                        None
                    }
                },
                _ => None,
            }
        },
        "halt" => {
            if meta.guard_family != "none" || meta.effect_kind != "set_done" {
                return Err(format!(
                    "MinskyLite halt contract mismatch for rule '{}' (logical id '{}'): guard='{}', effect='{}'",
                    meta.rule_id, meta.logical_transition_id, meta.guard_family, meta.effect_kind
                ));
            }
            match ctrl {
                Control::C_Halt => Some(Machine::C_Machine(
                    Box::new(Control::C_Halt),
                    Box::new(reg_a.clone()),
                    Box::new(reg_b.clone()),
                    done_status(),
                )),
                _ => None,
            }
        },
        _ => {
            return Err(format!(
                "MinskyLite MORK backend has no semantic handler for transition_kind '{}' (rule_id '{}', rule '{}', logical id '{}', source '{}', guard '{}', effect '{}')",
                meta.transition_kind,
                meta.rule_id,
                meta.rule_name,
                meta.logical_transition_id,
                meta.source_instr,
                meta.guard_family,
                meta.effect_kind
            ));
        },
    };
    Ok(next_machine.into_iter().collect())
}

#[cfg(feature = "mork-backend")]
fn minsky_native_step_state(state: &Machine) -> Result<Vec<(String, Machine)>, String> {
    let Machine::C_Machine(ctrl, reg_a, reg_b, status) = state else {
        return Err(format!("MinskyLite native backend expects C_Machine(...), got {}", state));
    };
    if !matches!(status.as_ref(), Status::C_Running) {
        return Ok(Vec::new());
    }

    let source_instr = minsky_source_instr(ctrl.as_ref()).ok_or_else(|| {
        format!("MinskyLite native backend does not support control shape '{}'", ctrl)
    })?;
    let contract = minskylite_rewrite_contract()?;
    let ordered = contract.ordered_rules_for(source_instr).ok_or_else(|| {
        format!("MinskyLite transition artifact missing source instruction '{}'", source_instr)
    })?;

    dispatch_ordered_rules(
        ordered,
        |rule| {
            let meta = contract.rule(rule).cloned().ok_or_else(|| {
                format!(
                    "MinskyLite rewrite contract missing metadata for rule '{}' listed under source '{}'",
                    rule, source_instr
                )
            })?;
            if meta.source_instr != source_instr {
                return Err(format!(
                    "MinskyLite rewrite contract mismatch: rule '{}' expected source '{}', got '{}'",
                    rule, source_instr, meta.source_instr
                ));
            }
            Ok(meta)
        },
        |_rule, meta| minsky_apply_rule(meta, ctrl.as_ref(), reg_a.as_ref(), reg_b.as_ref()),
    )
}

#[cfg(feature = "mork-backend")]
fn run_minskylite_native_state_graph(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let wrapped = term
        .as_any()
        .downcast_ref::<MinskyLiteTerm>()
        .ok_or_else(|| {
            "MinskyLite MORK backend expects MinskyLite parsed core term wrapper (MinskyLiteTerm)"
                .to_string()
        })?;
    let start_state = match &wrapped.0 {
        MinskyLiteTermInner::Machine(st) => st.clone(),
        _ => {
            return Err(format!(
                "MinskyLite MORK backend expects top-level Machine term, got wrapper variant: {}",
                wrapped
            ));
        },
    };

    let start_display = format!("{}", term);
    let start_id = term.term_id();
    run_transition_graph(start_state, &start_display, start_id, limits, |state| {
        minsky_native_step_state(state)
    })
}

#[cfg(feature = "mork-backend")]
pub fn run_minskylite_mork_backend(term: &dyn Term) -> Result<AscentResults, String> {
    run_minskylite_mork_backend_with_limits(term, MorkExecutionLimits::default())
}

#[cfg(feature = "mork-backend")]
pub fn run_minskylite_mork_backend_with_limits(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let started = Instant::now();
    let mut results = run_minskylite_native_state_graph(term, limits)?;
    results
        .phase_timings_ms
        .insert("mork_native_state_ms".to_string(), started.elapsed().as_secs_f64() * 1000.0);
    Ok(results)
}
