#![allow(
    non_local_definitions,
    non_camel_case_types,
    non_snake_case,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

include!("generated/mm0lite_language_working.rs");

#[derive(Debug, Clone, PartialEq, Eq)]
enum MM0FormulaToken {
    LParen,
    RParen,
    Arrow,
    Ident(String),
}

fn mm0_is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn mm0_is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn tokenize_mm0_formula(src: &str) -> Result<Vec<MM0FormulaToken>, String> {
    let mut out = Vec::new();
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '(' {
            out.push(MM0FormulaToken::LParen);
            i += 1;
            continue;
        }
        if c == ')' {
            out.push(MM0FormulaToken::RParen);
            i += 1;
            continue;
        }
        if c == '-' && i + 1 < chars.len() && chars[i + 1] == '>' {
            out.push(MM0FormulaToken::Arrow);
            i += 2;
            continue;
        }
        if mm0_is_ident_start(c) {
            let start = i;
            i += 1;
            while i < chars.len() && mm0_is_ident_continue(chars[i]) {
                i += 1;
            }
            out.push(MM0FormulaToken::Ident(chars[start..i].iter().collect()));
            continue;
        }
        return Err(format!("unsupported formula token '{}' in '{}'", c, src));
    }
    Ok(out)
}

struct MM0FormulaParser<'a> {
    toks: &'a [MM0FormulaToken],
    i: usize,
}

impl<'a> MM0FormulaParser<'a> {
    fn peek(&self) -> Option<&'a MM0FormulaToken> {
        self.toks.get(self.i)
    }

    fn bump(&mut self) -> Option<&'a MM0FormulaToken> {
        let tok = self.toks.get(self.i);
        if tok.is_some() {
            self.i += 1;
        }
        tok
    }

    fn parse_formula(&mut self) -> Result<Formula, String> {
        self.parse_implication()
    }

    fn parse_implication(&mut self) -> Result<Formula, String> {
        let lhs = self.parse_atom()?;
        if matches!(self.peek(), Some(MM0FormulaToken::Arrow)) {
            let _ = self.bump();
            let rhs = self.parse_implication()?;
            return Ok(Formula::C_Implies(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn parse_atom(&mut self) -> Result<Formula, String> {
        match self.bump() {
            Some(MM0FormulaToken::Ident(name)) => match name.as_str() {
                "P" | "p" | "a" => Ok(Formula::C_AtomP),
                "Q" | "q" | "b" => Ok(Formula::C_AtomQ),
                "R" | "r" | "c" => Ok(Formula::C_AtomR),
                _ => Err(format!(
                    "unsupported MM0Lite atom '{}': expected one of P|Q|R (or aliases a|b|c, p|q|r)",
                    name
                )),
            },
            Some(MM0FormulaToken::LParen) => {
                let inner = self.parse_formula()?;
                match self.bump() {
                    Some(MM0FormulaToken::RParen) => Ok(inner),
                    _ => Err("missing ')' in formula".to_string()),
                }
            },
            Some(tok) => Err(format!("unexpected token in formula: {:?}", tok)),
            None => Err("unexpected end of formula".to_string()),
        }
    }
}

pub fn parse_mm0_formula(src: &str) -> Result<Formula, String> {
    let toks = tokenize_mm0_formula(src)?;
    if toks.is_empty() {
        return Err("empty MM0 formula".to_string());
    }
    let mut parser = MM0FormulaParser { toks: &toks, i: 0 };
    let f = parser.parse_formula()?;
    if parser.i != toks.len() {
        return Err(format!("extra tokens after formula at token index {} in '{}'", parser.i, src));
    }
    Ok(f)
}

fn strip_mm0_line_comments(src: &str) -> String {
    src.lines()
        .map(|line| line.split("--").next().unwrap_or_default())
        .collect::<Vec<_>>()
        .join("\n")
}

fn match_keyword_at(hay: &str, i: usize, kw: &str) -> bool {
    let bytes = hay.as_bytes();
    let kwb = kw.as_bytes();
    if i + kwb.len() > bytes.len() || &bytes[i..i + kwb.len()] != kwb {
        return false;
    }
    let left_ok = i == 0 || !mm0_is_ident_continue(char::from(bytes[i - 1]));
    let right_ok =
        i + kwb.len() == bytes.len() || !mm0_is_ident_continue(char::from(bytes[i + kwb.len()]));
    left_ok && right_ok
}

fn parse_ident_from(hay: &str, mut i: usize) -> Option<(String, usize)> {
    let chars: Vec<char> = hay.chars().collect();
    while i < chars.len() && chars[i].is_whitespace() {
        i += 1;
    }
    if i >= chars.len() || !mm0_is_ident_start(chars[i]) {
        return None;
    }
    let start = i;
    i += 1;
    while i < chars.len() && mm0_is_ident_continue(chars[i]) {
        i += 1;
    }
    Some((chars[start..i].iter().collect(), i))
}

pub fn parse_mm0_theorem_facts(src: &str) -> Result<Vec<(String, Formula)>, String> {
    let clean = strip_mm0_line_comments(src);
    let mut i = 0usize;
    let mut facts = Vec::new();
    while i < clean.len() {
        let kw_len = if match_keyword_at(&clean, i, "axiom") {
            Some(5usize)
        } else if match_keyword_at(&clean, i, "theorem") {
            Some(7usize)
        } else {
            None
        };
        let Some(kw_len) = kw_len else {
            i += 1;
            continue;
        };

        let Some((name, after_name)) = parse_ident_from(&clean, i + kw_len) else {
            i += kw_len;
            continue;
        };

        let rest = &clean[after_name..];
        let Some(open_rel) = rest.find('$') else {
            i = after_name;
            continue;
        };
        let open = after_name + open_rel;
        let Some(close_rel) = clean[open + 1..].find('$') else {
            i = open + 1;
            continue;
        };
        let close = open + 1 + close_rel;
        let formula_src = clean[open + 1..close].trim();
        if let Ok(formula) = parse_mm0_formula(formula_src) {
            facts.push((name, formula));
        }

        let after = &clean[close + 1..];
        if let Some(semi_rel) = after.find(';') {
            i = close + 2 + semi_rel;
        } else {
            i = close + 1;
        }
    }
    if facts.is_empty() {
        return Err("no parseable MM0 theorem/axiom formulas found".to_string());
    }
    Ok(facts)
}

#[cfg(feature = "mork-backend")]
use crate::mm0lite_artifacts::{
    load_mm0lite_lookup_artifact, load_mm0lite_rewrite_ir_artifact,
    load_mm0lite_transition_artifact, mm0lite_artifact_dir,
};
#[cfg(feature = "mork-backend")]
use crate::native_transition_contract::{
    build_native_transition_contract, cached_contract_result, dispatch_active_source_step,
    NativeTransitionContract, NativeTransitionRuleMeta,
};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{
    run_native_term_graph_with_timing, AscentResults, LookupFamilyIndex, MorkExecutionLimits, Term,
};
#[cfg(feature = "mork-backend")]
use std::cell::RefCell;
#[cfg(feature = "mork-backend")]
use std::collections::HashMap;
#[cfg(feature = "mork-backend")]
use std::sync::OnceLock;

#[cfg(feature = "mork-backend")]
type MM0ThmLookup = LookupFamilyIndex<String, Formula, ()>;

#[cfg(feature = "mork-backend")]
fn mm0_thm_lookup() -> &'static MM0ThmLookup {
    static LOOKUP: OnceLock<MM0ThmLookup> = OnceLock::new();
    LOOKUP.get_or_init(|| {
        let mut exact = HashMap::new();
        exact.insert(
            "thm_imp_p_q".to_string(),
            vec![Formula::C_Implies(Box::new(Formula::C_AtomP), Box::new(Formula::C_AtomQ))],
        );
        exact.insert(
            "thm_imp_q_r".to_string(),
            vec![Formula::C_Implies(Box::new(Formula::C_AtomQ), Box::new(Formula::C_AtomR))],
        );
        MM0ThmLookup::from_parts(exact, Vec::new())
    })
}

#[cfg(feature = "mork-backend")]
thread_local! {
    static MM0_THM_LOOKUP_OVERRIDE: RefCell<Option<MM0ThmLookup>> = const { RefCell::new(None) };
}

#[cfg(feature = "mork-backend")]
pub fn with_mm0_theorem_facts<T>(facts: &[(String, Formula)], f: impl FnOnce() -> T) -> T {
    let mut exact: HashMap<String, Vec<Formula>> = HashMap::new();
    for (name, formula) in facts {
        exact.entry(name.clone()).or_default().push(formula.clone());
    }
    let override_lookup = MM0ThmLookup::from_parts(exact, Vec::new());
    MM0_THM_LOOKUP_OVERRIDE.with(|cell| {
        let prev = cell.replace(Some(override_lookup));
        let out = f();
        cell.replace(prev);
        out
    })
}

#[cfg(feature = "mork-backend")]
fn mm0_rewrite_contract() -> Result<&'static NativeTransitionContract, String> {
    static CONTRACT: OnceLock<Result<NativeTransitionContract, String>> = OnceLock::new();
    cached_contract_result(&CONTRACT, || {
        let dir = mm0lite_artifact_dir();
        let transition = load_mm0lite_transition_artifact(&dir)?;
        let lookup = load_mm0lite_lookup_artifact(&dir)?;
        let rewrite_ir = load_mm0lite_rewrite_ir_artifact(&dir)?;
        build_native_transition_contract("MM0Lite", transition, lookup, rewrite_ir, |lookup| {
            if lookup.families.iter().any(|f| f.family == "thmConcl") {
                Ok(())
            } else {
                Err("MM0Lite lookup-plan missing required thmConcl family".to_string())
            }
        })
    })
}

#[cfg(feature = "mork-backend")]
fn mm0_source_instr(prog: &Program) -> Option<&'static str> {
    match prog {
        Program::C_ICons(instr, _) => match instr.as_ref() {
            Instr::C_IPush(_) => Some("C_IPush"),
            Instr::C_IUse(_) => Some("C_IUse"),
            Instr::C_IMP => Some("C_IMP"),
            _ => None,
        },
        Program::C_INil => Some("C_INil"),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn mm0_thm_concl(th: &Thm) -> Option<Formula> {
    let key = format!("{}", th);
    if let Some(found) = MM0_THM_LOOKUP_OVERRIDE.with(|cell| {
        let borrowed = cell.borrow();
        borrowed
            .as_ref()
            .and_then(|lookup| lookup.exact_values(&key))
            .and_then(|vals| vals.first().cloned())
    }) {
        return Some(found);
    }
    mm0_thm_lookup()
        .exact_values(&key)
        .and_then(|vals| vals.first().cloned())
}

#[cfg(feature = "mork-backend")]
fn mm0_apply_rule_by_transition_kind(
    meta: &NativeTransitionRuleMeta,
    prog: &Program,
    goal: &Formula,
    stack: &Stack,
) -> Result<Vec<ProofState>, String> {
    let mut out_states = Vec::new();
    match (meta.transition_kind.as_str(), prog, stack) {
        ("push", Program::C_ICons(instr, tail), st) => {
            if let Instr::C_IPush(f) = instr.as_ref() {
                out_states.push(ProofState::C_MMState(
                    tail.clone(),
                    Box::new(goal.clone()),
                    Box::new(Stack::C_SCons(f.clone(), Box::new(st.clone()))),
                    Box::new(ProofResult::C_Pending),
                ));
            }
        },
        ("lookup_push", Program::C_ICons(instr, tail), st) => {
            if let Instr::C_IUse(th) = instr.as_ref() {
                if let Some(concl) = mm0_thm_concl(th.as_ref()) {
                    out_states.push(ProofState::C_MMState(
                        tail.clone(),
                        Box::new(goal.clone()),
                        Box::new(Stack::C_SCons(Box::new(concl), Box::new(st.clone()))),
                        Box::new(ProofResult::C_Pending),
                    ));
                }
            }
        },
        ("modus_ponens", Program::C_ICons(instr, tail), Stack::C_SCons(top1, rest1)) => {
            if matches!(instr.as_ref(), Instr::C_IMP) {
                if let Formula::C_Implies(a, b) = top1.as_ref() {
                    if let Stack::C_SCons(top2, st_rest) = rest1.as_ref() {
                        if top2.as_ref() == a.as_ref() {
                            out_states.push(ProofState::C_MMState(
                                tail.clone(),
                                Box::new(goal.clone()),
                                Box::new(Stack::C_SCons(b.clone(), st_rest.clone())),
                                Box::new(ProofResult::C_Pending),
                            ));
                        }
                    }
                }
            }
        },
        ("accept", Program::C_INil, Stack::C_SCons(top, rest)) => {
            if rest.as_ref() == &Stack::C_SNil && top.as_ref() == goal {
                out_states.push(ProofState::C_MMState(
                    Box::new(Program::C_INil),
                    Box::new(goal.clone()),
                    Box::new(Stack::C_SCons(top.clone(), rest.clone())),
                    Box::new(ProofResult::C_Verified),
                ));
            }
        },
        (kind, _, _) => {
            return Err(format!(
                "MM0Lite MORK backend has no semantic handler for transition_kind '{}' (rule_id '{}', rule '{}', logical id '{}', source '{}', guard '{}', effect '{}')",
                kind,
                meta.rule_id,
                meta.rule_name,
                meta.logical_transition_id,
                meta.source_instr,
                meta.guard_family,
                meta.effect_kind
            ));
        },
    }
    Ok(out_states)
}

#[cfg(feature = "mork-backend")]
fn mm0_native_step_state(state: &ProofState) -> Result<Vec<(String, ProofState)>, String> {
    let ProofState::C_MMState(prog, goal, stack, out) = state else {
        return Err(format!("MM0Lite native backend expects C_MMState(...), got {}", state));
    };

    let contract = mm0_rewrite_contract()?;
    let active_source = if out.as_ref() == &ProofResult::C_Pending {
        mm0_source_instr(prog.as_ref()).map(Some).ok_or_else(|| {
            format!("MM0Lite native backend does not support source program shape '{}'", prog)
        })
    } else {
        Ok(None)
    };
    dispatch_active_source_step("MM0Lite", contract, active_source, |_rule, meta| {
        mm0_apply_rule_by_transition_kind(meta, prog.as_ref(), goal.as_ref(), stack.as_ref())
    })
}

#[cfg(feature = "mork-backend")]
fn run_mm0lite_native_state_graph(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let wrapped = term.as_any().downcast_ref::<MM0LiteTerm>().ok_or_else(|| {
        "MM0Lite MORK backend expects MM0Lite parsed core term wrapper (MM0LiteTerm)".to_string()
    })?;
    let start_state = match &wrapped.0 {
        MM0LiteTermInner::ProofState(st) => st.clone(),
        _ => {
            return Err(format!(
                "MM0Lite MORK backend expects top-level ProofState term, got wrapper variant: {}",
                wrapped
            ));
        },
    };

    run_native_term_graph_with_timing(term, start_state, limits, |state| {
        mm0_native_step_state(state)
    })
}

#[cfg(feature = "mork-backend")]
pub fn run_mm0lite_mork_backend(term: &dyn Term) -> Result<AscentResults, String> {
    run_mm0lite_mork_backend_with_limits(term, MorkExecutionLimits::default())
}

#[cfg(feature = "mork-backend")]
pub fn run_mm0lite_mork_backend_with_limits(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    run_mm0lite_native_state_graph(term, limits)
}
