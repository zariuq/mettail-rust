use crate::artifact_contract::{PatternNode, PremiseNode, RewriteIRRule};
use std::collections::BTreeMap;

pub type TemplateBindings = BTreeMap<String, PatternNode>;

pub trait ConstructorCodec {
    fn artifact_to_runtime_ctor(&self, ctor: &str) -> String;
    fn runtime_to_artifact_ctor(&self, ctor: &str) -> String;
}

#[derive(Debug, Clone, Copy, Default)]
pub struct CPrefixConstructorCodec;

impl ConstructorCodec for CPrefixConstructorCodec {
    fn artifact_to_runtime_ctor(&self, ctor: &str) -> String {
        if ctor.starts_with("C_") {
            ctor.to_string()
        } else {
            format!("C_{ctor}")
        }
    }

    fn runtime_to_artifact_ctor(&self, ctor: &str) -> String {
        ctor.strip_prefix("C_").unwrap_or(ctor).to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedQueryArg {
    Ground(PatternNode),
    UnboundVar(String),
}

pub trait RewritePremiseEvaluator {
    fn eval_relation_query(
        &self,
        relation: &str,
        args: &[PatternNode],
        env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String>;

    fn eval_freshness(
        &self,
        var_name: &str,
        term: &PatternNode,
        _env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String> {
        Err(format!(
            "freshness premise not yet supported in generic rewrite executor: {} fresh in {}",
            var_name,
            render_pattern_debug(term)
        ))
    }

    fn eval_congruence(
        &self,
        lhs: &PatternNode,
        rhs: &PatternNode,
        env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String> {
        let lhs_inst = instantiate_pattern(lhs, env)?;
        let rhs_inst = instantiate_pattern(rhs, env)?;
        if lhs_inst == rhs_inst {
            Ok(vec![env.clone()])
        } else {
            Ok(Vec::new())
        }
    }
}

pub fn execute_rule_to_patterns(
    codec: &impl ConstructorCodec,
    current_runtime_display: &str,
    rule: &RewriteIRRule,
    evaluator: &impl RewritePremiseEvaluator,
) -> Result<Vec<PatternNode>, String> {
    let current = parse_runtime_term(codec, current_runtime_display)?;
    execute_rule_on_pattern(rule, &current, evaluator)
}

pub fn execute_rule_on_pattern(
    rule: &RewriteIRRule,
    current: &PatternNode,
    evaluator: &impl RewritePremiseEvaluator,
) -> Result<Vec<PatternNode>, String> {
    let lhs = rule
        .lhs
        .as_ref()
        .ok_or_else(|| format!("rule '{}' is missing structured lhs", rule.rule_id))?;
    let rhs = rule
        .rhs
        .as_ref()
        .ok_or_else(|| format!("rule '{}' is missing structured rhs", rule.rule_id))?;
    let Some(mut env) = match_pattern(lhs, current)? else {
        return Ok(Vec::new());
    };
    let mut envs = vec![std::mem::take(&mut env)];
    for premise in &rule.premises {
        let mut next_envs = Vec::new();
        for env in envs {
            let mut produced = eval_premise(evaluator, premise, &env)?;
            next_envs.append(&mut produced);
        }
        if next_envs.is_empty() {
            return Ok(Vec::new());
        }
        envs = next_envs;
    }
    envs.into_iter()
        .map(|env| instantiate_pattern(rhs, &env))
        .collect()
}

pub fn execute_rule_to_runtime_strings(
    codec: &impl ConstructorCodec,
    current_runtime_display: &str,
    rule: &RewriteIRRule,
    evaluator: &impl RewritePremiseEvaluator,
) -> Result<Vec<String>, String> {
    execute_rule_to_patterns(codec, current_runtime_display, rule, evaluator)?
        .into_iter()
        .map(|instantiated| render_runtime_term(codec, &instantiated))
        .collect()
}

pub fn bind_var(env: &mut TemplateBindings, name: &str, value: PatternNode) -> Result<(), String> {
    match env.get(name) {
        Some(existing) if existing == &value => Ok(()),
        Some(existing) => Err(format!(
            "variable '{}' bound inconsistently: existing={} new={}",
            name,
            render_pattern_debug(existing),
            render_pattern_debug(&value)
        )),
        None => {
            env.insert(name.to_string(), value);
            Ok(())
        },
    }
}

pub fn resolve_query_arg(
    node: &PatternNode,
    env: &TemplateBindings,
) -> Result<ResolvedQueryArg, String> {
    match node {
        PatternNode::Fvar { name } => match env.get(name) {
            Some(value) => Ok(ResolvedQueryArg::Ground(value.clone())),
            None => Ok(ResolvedQueryArg::UnboundVar(name.clone())),
        },
        _ => Ok(ResolvedQueryArg::Ground(instantiate_pattern(node, env)?)),
    }
}

pub fn parse_runtime_term(
    codec: &impl ConstructorCodec,
    text: &str,
) -> Result<PatternNode, String> {
    let mut parser = RuntimeTermParser { codec, text, pos: 0 };
    let term = parser.parse_term()?;
    parser.skip_ws();
    if parser.pos != parser.text.len() {
        return Err(format!(
            "unexpected trailing text while parsing runtime term at offset {}: '{}'",
            parser.pos,
            &parser.text[parser.pos..]
        ));
    }
    Ok(term)
}

pub fn render_runtime_term(
    codec: &impl ConstructorCodec,
    node: &PatternNode,
) -> Result<String, String> {
    match node {
        PatternNode::Apply { ctor, args } => {
            let ctor = codec.artifact_to_runtime_ctor(ctor);
            if args.is_empty() {
                Ok(ctor)
            } else {
                let rendered_args: Result<Vec<_>, _> = args
                    .iter()
                    .map(|arg| render_runtime_term(codec, arg))
                    .collect();
                Ok(format!("{}({})", ctor, rendered_args?.join(", ")))
            }
        },
        PatternNode::Fvar { name } => {
            Err(format!("cannot render runtime term with unresolved free variable '{}'", name))
        },
        PatternNode::Bvar { index } => {
            Err(format!("cannot render runtime term with bound variable index {}", index))
        },
        PatternNode::Collection { collection_type, elements, rest } => {
            if rest.is_some() {
                return Err(format!(
                    "collection rest not yet supported in runtime rendering for {}",
                    collection_type
                ));
            }
            let rendered: Result<Vec<_>, _> = elements
                .iter()
                .map(|element| render_runtime_term(codec, element))
                .collect();
            Ok(format!("[{}]", rendered?.join(", ")))
        },
        PatternNode::Lambda { .. }
        | PatternNode::MultiLambda { .. }
        | PatternNode::Subst { .. } => Err(format!(
            "runtime rendering does not yet support higher-order pattern node {}",
            render_pattern_debug(node)
        )),
    }
}

pub fn instantiate_pattern(
    node: &PatternNode,
    env: &TemplateBindings,
) -> Result<PatternNode, String> {
    match node {
        PatternNode::Fvar { name } => env
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unbound variable '{}' during rhs instantiation", name)),
        PatternNode::Apply { ctor, args } => Ok(PatternNode::Apply {
            ctor: ctor.clone(),
            args: args
                .iter()
                .map(|arg| instantiate_pattern(arg, env))
                .collect::<Result<_, _>>()?,
        }),
        PatternNode::Collection { collection_type, elements, rest } => {
            if rest.is_some() {
                return Err(format!(
                    "collection rest not yet supported in rhs instantiation for {}",
                    collection_type
                ));
            }
            Ok(PatternNode::Collection {
                collection_type: collection_type.clone(),
                elements: elements
                    .iter()
                    .map(|el| instantiate_pattern(el, env))
                    .collect::<Result<_, _>>()?,
                rest: None,
            })
        },
        PatternNode::Bvar { index } => {
            Err(format!("bound variables are not yet supported in rhs instantiation: {}", index))
        },
        PatternNode::Lambda { .. }
        | PatternNode::MultiLambda { .. }
        | PatternNode::Subst { .. } => Err(format!(
            "higher-order pattern nodes are not yet supported in rhs instantiation: {}",
            render_pattern_debug(node)
        )),
    }
}

pub fn match_pattern(
    pattern: &PatternNode,
    term: &PatternNode,
) -> Result<Option<TemplateBindings>, String> {
    let mut env = TemplateBindings::new();
    if match_pattern_into(pattern, term, &mut env)? {
        Ok(Some(env))
    } else {
        Ok(None)
    }
}

fn match_pattern_into(
    pattern: &PatternNode,
    term: &PatternNode,
    env: &mut TemplateBindings,
) -> Result<bool, String> {
    match pattern {
        PatternNode::Fvar { name } => {
            bind_var(env, name, term.clone())?;
            Ok(true)
        },
        PatternNode::Apply { ctor, args } => match term {
            PatternNode::Apply { ctor: term_ctor, args: term_args } => {
                if ctor != term_ctor || args.len() != term_args.len() {
                    return Ok(false);
                }
                for (lhs_arg, rhs_arg) in args.iter().zip(term_args.iter()) {
                    if !match_pattern_into(lhs_arg, rhs_arg, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            _ => Ok(false),
        },
        PatternNode::Collection { collection_type, elements, rest } => match term {
            PatternNode::Collection {
                collection_type: term_ty,
                elements: term_elements,
                rest: term_rest,
            } => {
                if collection_type != term_ty
                    || rest != term_rest
                    || elements.len() != term_elements.len()
                {
                    return Ok(false);
                }
                for (lhs_el, rhs_el) in elements.iter().zip(term_elements.iter()) {
                    if !match_pattern_into(lhs_el, rhs_el, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            _ => Ok(false),
        },
        PatternNode::Bvar { .. }
        | PatternNode::Lambda { .. }
        | PatternNode::MultiLambda { .. }
        | PatternNode::Subst { .. } => Err(format!(
            "matching does not yet support pattern node {}",
            render_pattern_debug(pattern)
        )),
    }
}

fn eval_premise(
    evaluator: &impl RewritePremiseEvaluator,
    premise: &PremiseNode,
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    match premise {
        PremiseNode::RelationQuery { relation, args } => {
            evaluator.eval_relation_query(relation, args, env)
        },
        PremiseNode::Freshness { var_name, term } => evaluator.eval_freshness(var_name, term, env),
        PremiseNode::Congruence { lhs, rhs } => evaluator.eval_congruence(lhs, rhs, env),
    }
}

fn render_pattern_debug(node: &PatternNode) -> String {
    match node {
        PatternNode::Bvar { index } => format!("BVar({index})"),
        PatternNode::Fvar { name } => format!("FVar({name})"),
        PatternNode::Apply { ctor, args } => {
            if args.is_empty() {
                ctor.clone()
            } else {
                format!(
                    "{}({})",
                    ctor,
                    args.iter()
                        .map(render_pattern_debug)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        },
        PatternNode::Lambda { body } => format!("Lambda({})", render_pattern_debug(body)),
        PatternNode::MultiLambda { arity, body } => {
            format!("MultiLambda({arity}; {})", render_pattern_debug(body))
        },
        PatternNode::Subst { body, repl } => {
            format!("Subst({}, {})", render_pattern_debug(body), render_pattern_debug(repl))
        },
        PatternNode::Collection { collection_type, elements, rest } => {
            let mut parts = elements
                .iter()
                .map(render_pattern_debug)
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                parts.push(format!("..{rest}"));
            }
            format!("{}[{}]", collection_type, parts.join(", "))
        },
    }
}

struct RuntimeTermParser<'a, C> {
    codec: &'a C,
    text: &'a str,
    pos: usize,
}

impl<C: ConstructorCodec> RuntimeTermParser<'_, C> {
    fn parse_term(&mut self) -> Result<PatternNode, String> {
        self.skip_ws();
        let ident = self.parse_ident()?;
        let ctor = self.codec.runtime_to_artifact_ctor(&ident);
        self.skip_ws();
        if self.consume('(') {
            let mut args = Vec::new();
            self.skip_ws();
            if !self.consume(')') {
                loop {
                    args.push(self.parse_term()?);
                    self.skip_ws();
                    if self.consume(')') {
                        break;
                    }
                    self.expect(',')?;
                }
            }
            Ok(PatternNode::Apply { ctor, args })
        } else {
            Ok(PatternNode::Apply { ctor, args: Vec::new() })
        }
    }

    fn parse_ident(&mut self) -> Result<String, String> {
        self.skip_ws();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                self.pos += ch.len_utf8();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(format!(
                "expected constructor identifier at offset {} in '{}'",
                self.pos, self.text
            ));
        }
        Ok(self.text[start..self.pos].to_string())
    }

    fn expect(&mut self, ch: char) -> Result<(), String> {
        if self.consume(ch) {
            Ok(())
        } else {
            Err(format!("expected '{}' at offset {} in '{}'", ch, self.pos, self.text))
        }
    }

    fn consume(&mut self, ch: char) -> bool {
        self.skip_ws();
        if self.peek_char() == Some(ch) {
            self.pos += ch.len_utf8();
            true
        } else {
            false
        }
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() {
                self.pos += ch.len_utf8();
            } else {
                break;
            }
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.text[self.pos..].chars().next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_match_and_render_roundtrip_on_constructor_terms() {
        let codec = CPrefixConstructorCodec;
        let text =
            "C_ImpState(C_RetUnit, C_Store(C_Zero, C_Succ(C_Zero), C_Zero), C_KDone, C_Running)";
        let term = parse_runtime_term(&codec, text).expect("term should parse");
        let lhs = PatternNode::Apply {
            ctor: "ImpState".to_string(),
            args: vec![
                PatternNode::Apply {
                    ctor: "RetUnit".to_string(),
                    args: vec![],
                },
                PatternNode::Fvar { name: "store".to_string() },
                PatternNode::Apply { ctor: "KDone".to_string(), args: vec![] },
                PatternNode::Apply {
                    ctor: "Running".to_string(),
                    args: vec![],
                },
            ],
        };
        let env = match_pattern(&lhs, &term)
            .expect("matching should succeed")
            .expect("pattern should match");
        let store = env.get("store").expect("store should be bound");
        assert_eq!(
            render_runtime_term(&codec, store).expect("store render should succeed"),
            "C_Store(C_Zero, C_Succ(C_Zero), C_Zero)"
        );
        assert_eq!(render_runtime_term(&codec, &term).expect("render should succeed"), text);
    }
}
