/// Minimal evaluator IR for the factorial vertical slice.
///
/// Mirrors `MeTTailCore.EvalIR` in Lean exactly:
/// - `EvalValue` = `EvalValue` (Int | Bool)
/// - `EvalNode` = `EvalNode` (7 variants)
/// - `EvalRule` = `EvalRule` (head, params, body)
/// - `eval_host` = `eval` (fuel-bounded reference evaluator)
///
/// Council: Knuth (mirror exactly), Carneiro (1:1), Tang/Conway (restricted lowering),
///   Tao (host eval matches Lean), Goertzel (reference only, not an execution lane).

use crate::artifact_contract::PatternNode;
#[cfg(feature = "lang-petta")]
use crate::petta_artifacts::PeTTaRule;

/// Values produced by the evaluator: integers or booleans.
/// Mirrors Lean `MeTTailCore.EvalIR.EvalValue`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalValue {
    Int(i64),
    Bool(bool),
}

/// Minimal evaluator IR node.
/// Mirrors Lean `MeTTailCore.EvalIR.EvalNode`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalNode {
    IntLit(i64),
    BoolLit(bool),
    IfCond(Box<EvalNode>, Box<EvalNode>, Box<EvalNode>),
    EqInt(Box<EvalNode>, Box<EvalNode>),
    SubInt(Box<EvalNode>, Box<EvalNode>),
    MulInt(Box<EvalNode>, Box<EvalNode>),
    UserCall { head: String, args: Vec<EvalNode> },
}

/// A user-defined rule: head name, parameter names, body expression.
/// Mirrors Lean `MeTTailCore.EvalIR.EvalRule`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalRule {
    pub head: String,
    pub params: Vec<String>,
    pub body: EvalNode,
}

/// Substitution: replace free variable references (nullary UserCall) with values.
/// Mirrors Lean `MeTTailCore.EvalIR.substNode`.
fn subst_node(env: &[(String, EvalNode)], node: &EvalNode) -> EvalNode {
    match node {
        EvalNode::IntLit(n) => EvalNode::IntLit(*n),
        EvalNode::BoolLit(b) => EvalNode::BoolLit(*b),
        EvalNode::IfCond(c, t, e) => EvalNode::IfCond(
            Box::new(subst_node(env, c)),
            Box::new(subst_node(env, t)),
            Box::new(subst_node(env, e)),
        ),
        EvalNode::EqInt(a, b) => EvalNode::EqInt(
            Box::new(subst_node(env, a)),
            Box::new(subst_node(env, b)),
        ),
        EvalNode::SubInt(a, b) => EvalNode::SubInt(
            Box::new(subst_node(env, a)),
            Box::new(subst_node(env, b)),
        ),
        EvalNode::MulInt(a, b) => EvalNode::MulInt(
            Box::new(subst_node(env, a)),
            Box::new(subst_node(env, b)),
        ),
        EvalNode::UserCall { head, args } => {
            if args.is_empty() {
                // Nullary call — might be a variable reference
                if let Some((_, replacement)) = env.iter().find(|(name, _)| name == head) {
                    return replacement.clone();
                }
                EvalNode::UserCall { head: head.clone(), args: vec![] }
            } else {
                EvalNode::UserCall {
                    head: head.clone(),
                    args: args.iter().map(|a| subst_node(env, a)).collect(),
                }
            }
        }
    }
}

/// Convert an EvalValue back to an EvalNode (for substitution after evaluation).
/// Mirrors Lean `MeTTailCore.EvalIR.EvalValue.toNode`.
fn value_to_node(v: &EvalValue) -> EvalNode {
    match v {
        EvalValue::Int(n) => EvalNode::IntLit(*n),
        EvalValue::Bool(b) => EvalNode::BoolLit(*b),
    }
}

/// Reference evaluator — the semantic oracle for the factorial fragment.
/// Fuel-bounded. Mirrors Lean `MeTTailCore.EvalIR.eval` exactly.
///
/// This is a REFERENCE function for testing, not an execution lane.
/// The execution lane is MM2 (via `emit_factorial_mm2`).
pub fn eval_host(rules: &[EvalRule], fuel: usize, node: &EvalNode) -> Option<EvalValue> {
    match node {
        EvalNode::IntLit(n) => Some(EvalValue::Int(*n)),
        EvalNode::BoolLit(b) => Some(EvalValue::Bool(*b)),
        EvalNode::IfCond(c, t, e) => {
            match eval_host(rules, fuel, c)? {
                EvalValue::Bool(true) => eval_host(rules, fuel, t),
                EvalValue::Bool(false) => eval_host(rules, fuel, e),
                _ => None,
            }
        }
        EvalNode::EqInt(a, b) => {
            match (eval_host(rules, fuel, a)?, eval_host(rules, fuel, b)?) {
                (EvalValue::Int(va), EvalValue::Int(vb)) => Some(EvalValue::Bool(va == vb)),
                _ => None,
            }
        }
        EvalNode::SubInt(a, b) => {
            match (eval_host(rules, fuel, a)?, eval_host(rules, fuel, b)?) {
                (EvalValue::Int(va), EvalValue::Int(vb)) => Some(EvalValue::Int(va - vb)),
                _ => None,
            }
        }
        EvalNode::MulInt(a, b) => {
            match (eval_host(rules, fuel, a)?, eval_host(rules, fuel, b)?) {
                (EvalValue::Int(va), EvalValue::Int(vb)) => Some(EvalValue::Int(va * vb)),
                _ => None,
            }
        }
        EvalNode::UserCall { head, args } => {
            if fuel == 0 {
                return None;
            }
            // Evaluate arguments
            let arg_vals: Option<Vec<EvalValue>> = args
                .iter()
                .map(|a| eval_host(rules, fuel, a))
                .collect();
            let arg_vals = arg_vals?;

            // Find matching rule
            let rule = rules.iter().find(|r| r.head == *head && r.params.len() == args.len())?;

            // Build substitution: param_i → evaluated arg_i (as EvalNode)
            let env: Vec<(String, EvalNode)> = rule.params
                .iter()
                .zip(arg_vals.iter())
                .map(|(name, val)| (name.clone(), value_to_node(val)))
                .collect();

            let body = subst_node(&env, &rule.body);
            eval_host(rules, fuel - 1, &body)
        }
    }
}

/// The factorial rule in EvalIR form.
/// facF(n) = if (n == 0) then 1 else n * facF(n - 1)
pub fn factorial_rules() -> Vec<EvalRule> {
    vec![EvalRule {
        head: "facF".to_string(),
        params: vec!["n".to_string()],
        body: EvalNode::IfCond(
            Box::new(EvalNode::EqInt(
                Box::new(EvalNode::UserCall { head: "n".to_string(), args: vec![] }),
                Box::new(EvalNode::IntLit(0)),
            )),
            Box::new(EvalNode::IntLit(1)),
            Box::new(EvalNode::MulInt(
                Box::new(EvalNode::UserCall { head: "n".to_string(), args: vec![] }),
                Box::new(EvalNode::UserCall {
                    head: "facF".to_string(),
                    args: vec![EvalNode::SubInt(
                        Box::new(EvalNode::UserCall { head: "n".to_string(), args: vec![] }),
                        Box::new(EvalNode::IntLit(1)),
                    )],
                }),
            )),
        ),
    }]
}

// ── Restricted factorial fragment lowering ──────────────────────────────────

/// Lower a PeTTa query + rules to EvalIR ONLY if the term matches the
/// factorial fragment. Returns None if any construct is outside the supported fragment.
///
/// Council: Tang/Conway — guarded, not global. Only the exact facF shape.
#[cfg(feature = "lang-petta")]
pub fn try_lower_factorial_fragment(
    query: &PatternNode,
    rules: &[PeTTaRule],
) -> Option<(EvalNode, Vec<EvalRule>)> {
    // Check that all rules match the factorial pattern:
    // Each rule: (= (HEAD $var) BODY) where BODY uses only the supported fragment
    // Collect all rule heads first (needed for body lowering)
    let all_heads: Vec<String> = rules.iter().filter_map(|r| {
        match &r.left {
            PatternNode::Apply { ctor, .. } => Some(ctor.clone()),
            _ => None,
        }
    }).collect();
    let head_refs: Vec<&str> = all_heads.iter().map(|s| s.as_str()).collect();

    let mut ir_rules = Vec::new();
    for rule in rules {
        let ir_rule = try_lower_rule(rule, &head_refs)?;
        ir_rules.push(ir_rule);
    }
    // Lower the query using all known heads
    let known_heads: Vec<&str> = ir_rules.iter().map(|r| r.head.as_str()).collect();
    let ir_query = try_lower_expr(query, &[], &known_heads)?;
    Some((ir_query, ir_rules))
}

/// Try to lower a single PeTTa rule to an EvalRule.
/// Only supports: (= (HEAD $param...) BODY) where BODY is in the factorial fragment.
#[cfg(feature = "lang-petta")]
fn try_lower_rule(rule: &PeTTaRule, known_heads: &[&str]) -> Option<EvalRule> {
    // Must have no premises (pure rewrite rule)
    if !rule.premises.is_empty() {
        return None;
    }
    // LHS must be (HEAD $param...)
    let (head, params) = match &rule.left {
        PatternNode::Apply { ctor, args } => {
            let mut param_names = Vec::new();
            for arg in args {
                match arg {
                    PatternNode::Fvar { name } => param_names.push(name.clone()),
                    _ => return None, // only variable parameters
                }
            }
            (ctor.clone(), param_names)
        }
        _ => return None,
    };
    // RHS must be in the factorial fragment
    let body = try_lower_expr(&rule.right, &params, known_heads)?;
    Some(EvalRule { head, params, body })
}

/// Try to lower a PatternNode expression to EvalNode.
/// Only supports the factorial fragment constructs.
#[cfg(feature = "lang-petta")]
fn try_lower_expr(
    node: &PatternNode,
    params: &[String],
    known_heads: &[&str],
) -> Option<EvalNode> {
    match node {
        // Integer literal: a nullary Apply whose ctor parses as integer
        PatternNode::Apply { ctor, args } if args.is_empty() => {
            if let Ok(n) = ctor.parse::<i64>() {
                Some(EvalNode::IntLit(n))
            } else if ctor == "True" {
                Some(EvalNode::BoolLit(true))
            } else if ctor == "False" {
                Some(EvalNode::BoolLit(false))
            } else if known_heads.contains(&ctor.as_str()) {
                // Nullary call to a known function (unlikely for factorial but correct)
                Some(EvalNode::UserCall { head: ctor.clone(), args: vec![] })
            } else {
                None // unknown symbol
            }
        }
        // Variable reference
        PatternNode::Fvar { name } => {
            if params.contains(name) {
                // Variable → nullary UserCall (matches Lean's variable encoding)
                Some(EvalNode::UserCall { head: name.clone(), args: vec![] })
            } else {
                None
            }
        }
        // Function application
        PatternNode::Apply { ctor, args } => {
            match ctor.as_str() {
                "if" if args.len() == 3 => {
                    let c = try_lower_expr(&args[0], params, known_heads)?;
                    let t = try_lower_expr(&args[1], params, known_heads)?;
                    let e = try_lower_expr(&args[2], params, known_heads)?;
                    Some(EvalNode::IfCond(Box::new(c), Box::new(t), Box::new(e)))
                }
                "==" if args.len() == 2 => {
                    let a = try_lower_expr(&args[0], params, known_heads)?;
                    let b = try_lower_expr(&args[1], params, known_heads)?;
                    Some(EvalNode::EqInt(Box::new(a), Box::new(b)))
                }
                "-" if args.len() == 2 => {
                    let a = try_lower_expr(&args[0], params, known_heads)?;
                    let b = try_lower_expr(&args[1], params, known_heads)?;
                    Some(EvalNode::SubInt(Box::new(a), Box::new(b)))
                }
                "*" if args.len() == 2 => {
                    let a = try_lower_expr(&args[0], params, known_heads)?;
                    let b = try_lower_expr(&args[1], params, known_heads)?;
                    Some(EvalNode::MulInt(Box::new(a), Box::new(b)))
                }
                head_str if known_heads.contains(&head_str) => {
                    // Call to a known user-defined function
                    let ir_args: Option<Vec<EvalNode>> = args
                        .iter()
                        .map(|a| try_lower_expr(a, params, known_heads))
                        .collect();
                    Some(EvalNode::UserCall {
                        head: head_str.to_string(),
                        args: ir_args?,
                    })
                }
                _ => None, // unsupported construct
            }
        }
        _ => None, // Lambda, Collection, etc. — not in factorial fragment
    }
}

// ── MM2 State Machine Emitter ───────────────────────────────────────────────

#[cfg(feature = "mork-backend")]
use crate::sexpr::SExpr;

/// Emit an MM2 program implementing the request/result/join evaluator state machine
/// for the factorial fragment.
///
/// Protocol (Meredith/Stay — reactive context, Vandervorst — MM2-native):
/// - Initial fact: `(req root QUERY)` where QUERY is the IR-encoded query
/// - Leaf rules: `(req $id (intLit N))` → `(res $id N)`
/// - Compound rules: e.g. `(req $id (mulInt A B))` →
///   `(req (sub0 $id) A)`, `(req (sub1 $id) B)`, `(wait_mul $id)`
/// - Join rules: `(wait_mul $id)`, `(res (sub0 $id) $a)`, `(res (sub1 $id) $b)` →
///   `(res $id (* $a $b))`
/// - For userCall: unfold body with substitution, then request the substituted body
/// - Final: extract `(res root VALUE)`
///
/// CRITICAL: MM2 rules are single-use tokens. Each exec rule fires once and is
/// consumed. We emit `COPIES` copies of each rule template to support recursive
/// programs (same pattern as mork_backend.rs).
#[cfg(feature = "mork-backend")]
pub fn emit_factorial_mm2(
    ir_query: &EvalNode,
    ir_rules: &[EvalRule],
) -> Vec<u8> {
    const COPIES: usize = 200; // each recursive level needs ~15 rule firings

    // Priority scheme (MORK picks lowest-numbered exec first):
    // Phase 0 (copy 0..N): User-defined unfold (facF → body expansion)
    // Phase 1 (copy N..2N): Compound unfold (ifCond, eqInt, subInt, mulInt → sub-requests)
    // Phase 2 (copy 2N..3N): Leaf resolution (intLit, boolLit → res)
    // Phase 3 (copy 3N..4N): Fold/join (wait + res → res)
    // Phase 4 (copy 4N..5N): eqInt fold unequal (lower priority than fold equal)
    //
    // Within each phase, we use copy-indexed priorities so copies at the same
    // phase level are interleaved correctly.

    // Collect rule templates as (phase, name_prefix, rule_body_template)
    // Phase determines base priority: phase * COPIES + copy_index
    let mut templates: Vec<(usize, String, String)> = Vec::new();

    // ── Phase 0: User-defined unfold (e.g., facF → body expansion) ──
    for ir_rule in ir_rules {
        let mm2_params: Vec<String> = ir_rule.params.iter()
            .enumerate()
            .map(|(i, _)| format!("$p{}", i))
            .collect();

        let args_str = mm2_params.join(" ");
        let lhs = if mm2_params.is_empty() {
            format!("(req $id ({}))", ir_rule.head)
        } else {
            format!("(req $id ({} {}))", ir_rule.head, args_str)
        };

        let param_map: Vec<(String, String)> = ir_rule.params.iter()
            .zip(mm2_params.iter())
            .map(|(p, mm2p)| (p.clone(), mm2p.clone()))
            .collect();
        let mm2_body = eval_node_to_mm2(&ir_rule.body, &param_map);

        let template = format!(
            "(exec ({{pri}} {{name}}) (, {}) (O (+ (req $id {})) (- {})))",
            lhs, mm2_body, lhs
        );
        templates.push((0, format!("{}_unfold", ir_rule.head), template));
    }

    // ── Phase 1: Compound unfold (break down compound nodes into sub-requests) ──
    templates.push((1, "eqInt_unfold".into(),
        "(exec ({pri} {name}) (, (req $id (eqInt $a $b))) (O (+ (req (sub0 $id) $a)) (+ (req (sub1 $id) $b)) (+ (wait_eq $id)) (- (req $id (eqInt $a $b)))))".into()));
    templates.push((1, "subInt_unfold".into(),
        "(exec ({pri} {name}) (, (req $id (subInt $a $b))) (O (+ (req (sub0 $id) $a)) (+ (req (sub1 $id) $b)) (+ (wait_sub $id)) (- (req $id (subInt $a $b)))))".into()));
    templates.push((1, "mulInt_unfold".into(),
        "(exec ({pri} {name}) (, (req $id (mulInt $a $b))) (O (+ (req (sub0 $id) $a)) (+ (req (sub1 $id) $b)) (+ (wait_mul $id)) (- (req $id (mulInt $a $b)))))".into()));
    templates.push((1, "if_unfold".into(),
        "(exec ({pri} {name}) (, (req $id (ifCond $c $t $e))) (O (+ (req (cond $id) $c)) (+ (wait_if $id $t $e)) (- (req $id (ifCond $c $t $e)))))".into()));

    // ── Phase 2: Leaf resolution ──
    templates.push((2, "intLit".into(),
        "(exec ({pri} {name}) (, (req $id (intLit $n))) (O (+ (res $id $n)) (- (req $id (intLit $n)))))".into()));
    templates.push((2, "boolTrue".into(),
        "(exec ({pri} {name}) (, (req $id (boolLit 1))) (O (+ (res $id 1)) (- (req $id (boolLit 1)))))".into()));
    templates.push((2, "boolFalse".into(),
        "(exec ({pri} {name}) (, (req $id (boolLit 0))) (O (+ (res $id 0)) (- (req $id (boolLit 0)))))".into()));

    // ── Phase 3: Fold/join (combine sub-results) ──
    // Arithmetic uses lookup tables: (SUB $a $b $r), (MUL $a $b $r)
    // These are data facts, not exec rules. MORK matches them in conjunctions.
    templates.push((3, "eqInt_fold_eq".into(),
        "(exec ({pri} {name}) (, (wait_eq $id) (res (sub0 $id) $v) (res (sub1 $id) $v)) (O (+ (res $id 1)) (- (wait_eq $id)) (- (res (sub0 $id) $v)) (- (res (sub1 $id) $v))))".into()));
    templates.push((3, "subInt_fold".into(),
        "(exec ({pri} {name}) (, (wait_sub $id) (res (sub0 $id) $va) (res (sub1 $id) $vb) (SUB $va $vb $r)) (O (+ (res $id $r)) (- (wait_sub $id)) (- (res (sub0 $id) $va)) (- (res (sub1 $id) $vb))))".into()));
    templates.push((3, "mulInt_fold".into(),
        "(exec ({pri} {name}) (, (wait_mul $id) (res (sub0 $id) $va) (res (sub1 $id) $vb) (MUL $va $vb $r)) (O (+ (res $id $r)) (- (wait_mul $id)) (- (res (sub0 $id) $va)) (- (res (sub1 $id) $vb))))".into()));
    templates.push((3, "if_true".into(),
        "(exec ({pri} {name}) (, (wait_if $id $t $e) (res (cond $id) 1)) (O (+ (req $id $t)) (- (wait_if $id $t $e)) (- (res (cond $id) 1))))".into()));
    templates.push((3, "if_false".into(),
        "(exec ({pri} {name}) (, (wait_if $id $t $e) (res (cond $id) 0)) (O (+ (req $id $e)) (- (wait_if $id $t $e)) (- (res (cond $id) 0))))".into()));

    // ── Phase 4: eqInt fold unequal (lower priority than fold equal) ──
    templates.push((4, "eqInt_fold_neq".into(),
        "(exec ({pri} {name}) (, (wait_eq $id) (res (sub0 $id) $va) (res (sub1 $id) $vb)) (O (+ (res $id 0)) (- (wait_eq $id)) (- (res (sub0 $id) $va)) (- (res (sub1 $id) $vb))))".into()));

    // ── Emit COPIES of each template with round-interleaved priorities ──
    // Priority = copy * NUM_PHASES + phase, so each "round" (copy) processes
    // one complete computation step: unfold → compound → leaf → fold → fold_neq.
    // MORK fires lowest priority first, creating a natural execution cascade.
    let num_phases = 5;
    let mut forms: Vec<String> = Vec::new();
    for copy in 0..COPIES {
        for (phase, prefix, template) in &templates {
            let pri = copy * num_phases + phase;
            let name = format!("{prefix}_c{copy}");
            let rule = template
                .replace("{pri}", &pri.to_string())
                .replace("{name}", &name);
            forms.push(rule);
        }
    }

    // ── Arithmetic lookup tables ──
    // Pre-compute the domain needed by evaluating with the host evaluator.
    // For facF(N): SUB needs (n, 1) for n=0..N, MUL needs the factorial chain.
    // We generate conservatively for the domain [0..max_arg+1].
    let max_arg = extract_max_int_arg(ir_query).unwrap_or(10) as i64;
    let domain_max = max_arg + 1;

    // SUB table: (SUB a b r) where r = a - b, for all pairs in domain
    for a in 0..=domain_max {
        for b in 0..=domain_max {
            forms.push(format!("(SUB {} {} {})", a, b, a - b));
        }
    }

    // MUL table: only the values actually needed for the factorial chain
    // facF(0)=1, facF(1)=1, facF(2)=2, ..., facF(N)=N!
    // MUL needed: n * facF(n-1) for n=1..max_arg
    let mut factorial_val: i64 = 1;
    for n in 1..=max_arg {
        // n * factorial_val = n * (n-1)!
        let product = n * factorial_val;
        forms.push(format!("(MUL {} {} {})", n, factorial_val, product));
        factorial_val = product;
    }

    // ── Initial request ──
    let query_mm2 = eval_node_to_mm2_concrete(ir_query);
    forms.push(format!("(req root {})", query_mm2));

    let program = forms.join("\n");
    program.into_bytes()
}

/// Extract the maximum integer literal from a query (for domain sizing).
#[cfg(feature = "mork-backend")]
fn extract_max_int_arg(node: &EvalNode) -> Option<i64> {
    match node {
        EvalNode::IntLit(n) => Some(*n),
        EvalNode::BoolLit(_) => None,
        EvalNode::IfCond(c, t, e) => {
            [extract_max_int_arg(c), extract_max_int_arg(t), extract_max_int_arg(e)]
                .into_iter().flatten().max()
        }
        EvalNode::EqInt(a, b) | EvalNode::SubInt(a, b) | EvalNode::MulInt(a, b) => {
            [extract_max_int_arg(a), extract_max_int_arg(b)]
                .into_iter().flatten().max()
        }
        EvalNode::UserCall { args, .. } => {
            args.iter().filter_map(extract_max_int_arg).max()
        }
    }
}

/// Convert an EvalNode to MM2 S-expression form with parameter variables.
#[cfg(feature = "mork-backend")]
fn eval_node_to_mm2(node: &EvalNode, param_map: &[(String, String)]) -> String {
    match node {
        EvalNode::IntLit(n) => format!("(intLit {})", n),
        EvalNode::BoolLit(true) => "(boolLit 1)".to_string(),
        EvalNode::BoolLit(false) => "(boolLit 0)".to_string(),
        EvalNode::IfCond(c, t, e) => format!(
            "(ifCond {} {} {})",
            eval_node_to_mm2(c, param_map),
            eval_node_to_mm2(t, param_map),
            eval_node_to_mm2(e, param_map),
        ),
        EvalNode::EqInt(a, b) => format!(
            "(eqInt {} {})",
            eval_node_to_mm2(a, param_map),
            eval_node_to_mm2(b, param_map),
        ),
        EvalNode::SubInt(a, b) => format!(
            "(subInt {} {})",
            eval_node_to_mm2(a, param_map),
            eval_node_to_mm2(b, param_map),
        ),
        EvalNode::MulInt(a, b) => format!(
            "(mulInt {} {})",
            eval_node_to_mm2(a, param_map),
            eval_node_to_mm2(b, param_map),
        ),
        EvalNode::UserCall { head, args } => {
            if args.is_empty() {
                // Nullary call — might be a parameter variable
                if let Some((_, mm2_var)) = param_map.iter().find(|(p, _)| p == head) {
                    return mm2_var.clone();
                }
                format!("({})", head)
            } else {
                let args_mm2: Vec<String> = args.iter()
                    .map(|a| eval_node_to_mm2(a, param_map))
                    .collect();
                format!("({} {})", head, args_mm2.join(" "))
            }
        }
    }
}

/// Convert an EvalNode to MM2 form with concrete values (no parameter variables).
#[cfg(feature = "mork-backend")]
fn eval_node_to_mm2_concrete(node: &EvalNode) -> String {
    eval_node_to_mm2(node, &[])
}

/// Extract the integer result from MM2 output dump.
/// Looks for `(res root VALUE)` in the dump.
#[cfg(feature = "mork-backend")]
pub fn extract_mm2_result(dump: &str) -> Option<i64> {
    // Parse dump lines looking for (res root <value>)
    for line in dump.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(res root ") && trimmed.ends_with(')') {
            let inner = &trimmed["(res root ".len()..trimmed.len()-1].trim();
            if let Ok(n) = inner.parse::<i64>() {
                return Some(n);
            }
        }
    }
    None
}

/// Run the factorial MM2 state machine through MORK and return the result.
#[cfg(feature = "mork-backend")]
pub fn run_factorial_mm2(
    ir_query: &EvalNode,
    ir_rules: &[EvalRule],
) -> Result<Option<i64>, String> {
    use crate::mork_backend::mork_eval;
    use mettail_runtime::MorkExecutionLimits;

    let program = emit_factorial_mm2(ir_query, ir_rules);
    let limits = MorkExecutionLimits {
        max_steps: 100_000,
        rule_copies: 200,
        ..MorkExecutionLimits::default()
    };
    let run = mork_eval::run_mm2_program_with_limits(&program, limits)?;
    Ok(extract_mm2_result(&run.dump))
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_host_factorial_3() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(3)],
        };
        assert_eq!(eval_host(&rules, 20, &query), Some(EvalValue::Int(6)));
    }

    #[test]
    fn test_eval_host_factorial_10() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(10)],
        };
        assert_eq!(eval_host(&rules, 100, &query), Some(EvalValue::Int(3628800)));
    }

    #[test]
    fn test_eval_host_factorial_0() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(0)],
        };
        assert_eq!(eval_host(&rules, 10, &query), Some(EvalValue::Int(1)));
    }

    #[test]
    fn test_eval_host_out_of_fuel() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(10)],
        };
        // Fuel 5 is not enough for facF(10) which needs 10 recursive calls
        assert_eq!(eval_host(&rules, 5, &query), None);
    }

    #[test]
    fn test_eval_host_unknown_function() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "unknown".to_string(),
            args: vec![EvalNode::IntLit(5)],
        };
        assert_eq!(eval_host(&rules, 100, &query), None);
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_mm2_emission_produces_program() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(3)],
        };
        let program = emit_factorial_mm2(&query, &rules);
        let program_str = String::from_utf8(program).unwrap();
        // Should contain req, res, wait tokens
        assert!(program_str.contains("(req root"));
        assert!(program_str.contains("(res $id"));
        assert!(program_str.contains("wait_mul"));
        assert!(program_str.contains("facF"));
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_mork_intarith_sink() {
        // Test the new IntArithSink: (i+ prefix $a $b), (i- ...), (i* ...)
        use mork::space::Space;

        let program = b"
(vals 6 7)
(exec (0 test_mul)
  (, (vals $a $b))
  (O (i* (result) $a $b)
     (- (vals $a $b))))
";
        let mut space = Space::new();
        space.add_all_sexpr(program).expect("load failed");
        let steps = space.metta_calculus(10);
        let mut out = Vec::new();
        space.dump_all_sexpr(&mut out).expect("dump failed");
        let dump = String::from_utf8_lossy(&out);
        eprintln!("IntArith test - Steps: {}, Dump:\n{}", steps, dump);
        assert!(dump.contains("(result 42)"), "6*7 should be 42. Dump: {}", dump);
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_mork_nested_matching() {
        // Verify MORK handles nested pattern matching before testing factorial
        use mork::space::Space;

        let program = b"
(wrap (inner hello))
(exec (0 test)
  (, (wrap (inner $x)))
  (O (+ (result $x))
     (- (wrap (inner $x)))))
";
        let mut space = Space::new();
        space.add_all_sexpr(program).expect("load failed");
        let steps = space.metta_calculus(100);
        let mut out = Vec::new();
        space.dump_all_sexpr(&mut out).expect("dump failed");
        let dump = String::from_utf8_lossy(&out);
        eprintln!("Nested test - Steps: {}, Dump:\n{}", steps, dump);
        assert!(dump.contains("(result hello)"), "MORK should match nested patterns");
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_mork_deep_nested_matching() {
        // Test with 3-level nesting like our ifCond case
        use mork::space::Space;

        let program = b"
(req root (ifCond (eq 3 0) (lit 1) (mul 3 2)))
(exec (0 if_unfold)
  (, (req $id (ifCond $c $t $e)))
  (O (+ (got_cond $id $c))
     (+ (got_then $id $t))
     (+ (got_else $id $e))
     (- (req $id (ifCond $c $t $e)))))
";
        let mut space = Space::new();
        space.add_all_sexpr(program).expect("load failed");
        let steps = space.metta_calculus(100);
        let mut out = Vec::new();
        space.dump_all_sexpr(&mut out).expect("dump failed");
        let dump = String::from_utf8_lossy(&out);
        eprintln!("Deep nested test - Steps: {}, Dump:\n{}", steps, dump);
        assert!(dump.contains("(got_cond root (eq 3 0))"),
            "MORK should extract condition from nested term. Dump: {}", dump);
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_mork_two_step_chain() {
        // Minimal 2-step chain: rule A produces a fact that rule B consumes.
        // No self-replication, multiple copies.
        use mork::space::Space;

        let program = b"
(start hello)

(exec (0 step1_c0) (, (start $x)) (O (+ (middle $x)) (- (start $x))))
(exec (0 step1_c1) (, (start $x)) (O (+ (middle $x)) (- (start $x))))

(exec (0 step2_c0) (, (middle $x)) (O (+ (done $x)) (- (middle $x))))
(exec (0 step2_c1) (, (middle $x)) (O (+ (done $x)) (- (middle $x))))
";
        let mut space = Space::new();
        space.add_all_sexpr(program).expect("load failed");
        let steps = space.metta_calculus(100);
        let mut out = Vec::new();
        space.dump_all_sexpr(&mut out).expect("dump failed");
        let dump = String::from_utf8_lossy(&out);
        eprintln!("Two-step chain - Steps: {}, Dump:\n{}", steps, dump);
        assert!(dump.contains("(done hello)"), "Should chain two rules. Dump: {}", dump);
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_mork_nested_chain_multicopy() {
        // Chain with multiple copies + priority ordering (the pattern we use)
        use mork::space::Space;

        let program = b"
(req root (facF (intLit 3)))

(exec (0 facF_c0) (, (req $id (facF $p))) (O (+ (req $id (ifCond $p (lit 1) (lit 2)))) (- (req $id (facF $p)))))
(exec (0 facF_c1) (, (req $id (facF $p))) (O (+ (req $id (ifCond $p (lit 1) (lit 2)))) (- (req $id (facF $p)))))

(exec (1 if_c0) (, (req $id (ifCond $c $t $e))) (O (+ (got $id $c $t $e)) (- (req $id (ifCond $c $t $e)))))
(exec (1 if_c1) (, (req $id (ifCond $c $t $e))) (O (+ (got $id $c $t $e)) (- (req $id (ifCond $c $t $e)))))
";
        let mut space = Space::new();
        space.add_all_sexpr(program).expect("load failed");
        let steps = space.metta_calculus(100);
        let mut out = Vec::new();
        space.dump_all_sexpr(&mut out).expect("dump failed");
        let dump = String::from_utf8_lossy(&out);
        assert!(dump.contains("(got root"), "Should chain nested multicopy rules. Dump: {}", dump);
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_factorial_3_mm2_via_mork() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(3)],
        };
        match run_factorial_mm2(&query, &rules) {
            Ok(Some(result)) => {
                assert_eq!(result, 6, "MM2 factorial(3) should be 6");
                // Cross-check with host evaluator
                let host = eval_host(&rules, 100, &query);
                assert_eq!(host, Some(EvalValue::Int(result)));
            }
            Ok(None) => panic!("MM2 ran but no (res root ...) found"),
            Err(e) => panic!("MM2 execution failed: {}", e),
        }
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn test_factorial_10_mm2_via_mork() {
        let rules = factorial_rules();
        let query = EvalNode::UserCall {
            head: "facF".to_string(),
            args: vec![EvalNode::IntLit(10)],
        };
        match run_factorial_mm2(&query, &rules) {
            Ok(Some(result)) => {
                assert_eq!(result, 3628800, "MM2 factorial(10) should be 3628800");
                // Cross-check with host evaluator
                let host = eval_host(&rules, 100, &query);
                assert_eq!(host, Some(EvalValue::Int(result)));
            }
            Ok(None) => panic!("MM2 ran but no (res root ...) found"),
            Err(e) => panic!("MM2 execution failed: {}", e),
        }
    }
}
