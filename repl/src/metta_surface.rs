use anyhow::{anyhow, bail, Result};
use mettail_runtime::{
    dedup_stable, explore_rewrite_frontier, expr_fragment_safe, is_core_fast_path_eligible,
    CoreFastPathEligibility, MemoComputeOutcome, MorkExecutionLimits, PatternIndexKey,
    QueryIndexKey, ReentrantMemo, RewriteEvalDiagnostics, RewriteLimits, RuleFragment,
    RuleFragmentSafety, RuleIndex,
};
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;
use std::time::Instant;
use tree_sitter::{Language as TSLanguage, Node as TSNode, Parser as TSParser};

use crate::lookup_plan::{
    relation_metadata_index, try_load_lookup_plan, LookupPlanArtifact, LookupRelationMetadata,
};
use crate::syntax_spec::{
    try_load_syntax_spec, CommandHead, DispatchPolicy, EvalPrefixPolicy, LexerSpec, LoweringHeads,
    SyntaxSpec,
};
use std::borrow::Cow;

const DEFAULT_SPACE_IDENT: &str = "&self";

/// Surface profile: determines how surface syntax maps to/from core terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SurfaceProfile {
    /// Legacy MeTTaFullState backend (default)
    Legacy,
    /// HE MeTTa backend
    HE,
}

/// Surface syntax policy for command-level parsing.
///
/// This is intentionally frontend-only: it governs how textual `.metta` lines
/// are normalized into `SurfaceStmt`, not core rewrite semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SurfaceSyntaxPolicy {
    /// Match Hyperon/HE behavior: tolerate standalone `!` as a no-op.
    HyperonCompat,
    /// Require a non-empty expression after `!`.
    Strict,
}

/// Selects which parser frontend is used before normalization/lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SurfaceParserBackend {
    /// Current in-process tokenizer/S-expression parser.
    LegacySExpr,
    /// Target backend: Tree-sitter parser driven by Lean-generated grammar artifacts.
    TreeSitter,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfaceStmt {
    Eval(SExpr),
    EvalIn { space: String, expr: SExpr },
    DefineEq(SExpr, SExpr),
    DefineType(SExpr, SExpr),
    DeclareMemoized { space: String, head: String },
    AllocSpace,
    AddAtom { space: String, atom_expr: SExpr },
    RemoveAtom { space: String, atom_expr: SExpr },
    NewSpace { space: String },
}

#[derive(Debug, Clone, Default)]
pub struct SurfaceSpaceState {
    pub eq_entries: Vec<(String, String)>,
    pub pattern_eq_entries: Vec<(String, String)>,
    pub eq_patterns: Vec<(SExpr, SExpr)>,
    pub type_entries: Vec<(String, String)>,
    pub memoized_heads: HashSet<String>,
}

struct MeTTaCoreFastPathHooks;

impl RuleFragmentSafety for MeTTaCoreFastPathHooks {
    type Expr = SExpr;
    type Rule = (SExpr, SExpr);

    fn expr_is_fragment_safe(expr: &Self::Expr, fragment: RuleFragment) -> bool {
        match fragment {
            RuleFragment::CoreGroundEval => is_core_lp_translatable_expr(expr),
        }
    }

    fn rule_is_fragment_safe(rule: &Self::Rule, fragment: RuleFragment) -> bool {
        match fragment {
            RuleFragment::CoreGroundEval => is_core_lp_translatable_rule(&rule.0, &rule.1),
        }
    }
}

impl CoreFastPathEligibility for MeTTaCoreFastPathHooks {
    fn is_ground_candidate(expr: &Self::Expr) -> bool {
        is_ground_call_expr(expr)
    }

    fn expr_head(expr: &Self::Expr) -> Option<&str> {
        expr_head_atom(expr)
    }

    fn rule_head(rule: &Self::Rule) -> Option<&str> {
        expr_head_atom(&rule.0)
    }
}

pub type SurfaceRewriteLimits = RewriteLimits;
pub type SurfaceEvalDiagnostics = RewriteEvalDiagnostics;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GroundCallMemoKey {
    space: String,
    revision: u64,
    expr: SExpr,
    limits: SurfaceRewriteLimits,
    exact_rules: bool,
}

#[derive(Debug, Clone)]
pub struct MeTTaSurfaceSession {
    profile: SurfaceProfile,
    syntax_policy: SurfaceSyntaxPolicy,
    parser_backend: SurfaceParserBackend,
    syntax_spec: Option<SyntaxSpec>,
    syntax_spec_required: bool,
    syntax_spec_error: Option<String>,
    lookup_plan: Option<LookupPlanArtifact>,
    lookup_relation_metadata: Option<HashMap<String, LookupRelationMetadata>>,
    lookup_plan_required: bool,
    lookup_plan_error: Option<String>,
    spaces: HashMap<String, SurfaceSpaceState>,
    space_revisions: HashMap<String, u64>,
    empty_space: SurfaceSpaceState,
    next_space_index: u64,
    rewrite_limits: SurfaceRewriteLimits,
    prefer_exact_rules: bool,
    core_ground_eval_enabled: bool,
    recursive_memo_enabled: bool,
    ground_call_memo: ReentrantMemo<GroundCallMemoKey, Vec<SExpr>>,
    last_surface_diagnostics: Option<SurfaceEvalDiagnostics>,
    /// Compatibility flag from legacy surface-mode wiring.
    ///
    /// Surface-level MORK execution is intentionally disabled; when this flag is
    /// set, evaluation must route through core `Language::run_backend`.
    use_mork_backend: bool,
    mork_limits: MorkExecutionLimits,
}

impl Default for MeTTaSurfaceSession {
    fn default() -> Self {
        Self::new()
    }
}

impl MeTTaSurfaceSession {
    pub fn new() -> Self {
        Self::with_profile(SurfaceProfile::Legacy)
    }

    pub fn with_profile(profile: SurfaceProfile) -> Self {
        let mut spaces = HashMap::new();
        let mut default_space = SurfaceSpaceState::default();
        let (syntax_policy, syntax_spec, syntax_spec_required, syntax_spec_error) =
            syntax_config_from_profile(profile);
        let (lookup_plan, lookup_relation_metadata, lookup_plan_required, lookup_plan_error) =
            lookup_plan_config_from_profile(profile);
        let parser_backend = parser_backend_from_profile(profile);

        // HE profile: bootstrap grounded operator type annotations
        if profile == SurfaceProfile::HE {
            default_space.type_entries = crate::metta_surface_he::he_bootstrap_type_entries();
        }

        spaces.insert(DEFAULT_SPACE_IDENT.to_string(), default_space);
        let mut space_revisions = HashMap::new();
        space_revisions.insert(DEFAULT_SPACE_IDENT.to_string(), 0);
        Self {
            profile,
            syntax_policy,
            parser_backend,
            syntax_spec,
            syntax_spec_required,
            syntax_spec_error,
            lookup_plan,
            lookup_relation_metadata,
            lookup_plan_required,
            lookup_plan_error,
            spaces,
            space_revisions,
            empty_space: SurfaceSpaceState::default(),
            next_space_index: 0,
            rewrite_limits: SurfaceRewriteLimits::default(),
            prefer_exact_rules: false,
            core_ground_eval_enabled: false,
            recursive_memo_enabled: true,
            ground_call_memo: ReentrantMemo::default(),
            last_surface_diagnostics: None,
            use_mork_backend: false,
            mork_limits: MorkExecutionLimits::default(),
        }
    }

    pub fn profile(&self) -> SurfaceProfile {
        self.profile
    }

    pub fn syntax_policy(&self) -> SurfaceSyntaxPolicy {
        self.syntax_policy
    }

    pub fn set_syntax_policy(&mut self, policy: SurfaceSyntaxPolicy) {
        self.syntax_policy = policy;
    }

    pub fn syntax_spec(&self) -> Option<&SyntaxSpec> {
        self.syntax_spec.as_ref()
    }

    pub fn lookup_plan(&self) -> Option<&LookupPlanArtifact> {
        self.lookup_plan.as_ref()
    }

    pub fn lookup_relation_metadata(&self) -> Option<&HashMap<String, LookupRelationMetadata>> {
        self.lookup_relation_metadata.as_ref()
    }

    pub fn parser_backend(&self) -> SurfaceParserBackend {
        self.parser_backend
    }

    pub fn set_parser_backend(&mut self, backend: SurfaceParserBackend) {
        self.parser_backend = backend;
    }

    pub fn rewrite_limits(&self) -> SurfaceRewriteLimits {
        self.rewrite_limits
    }

    pub fn set_rewrite_limits(&mut self, limits: SurfaceRewriteLimits) {
        self.rewrite_limits = limits;
    }

    pub fn prefer_exact_rules(&self) -> bool {
        self.prefer_exact_rules
    }

    pub fn set_prefer_exact_rules(&mut self, enabled: bool) {
        self.prefer_exact_rules = enabled;
    }

    pub fn recursive_memo_enabled(&self) -> bool {
        self.recursive_memo_enabled
    }

    pub fn use_mork_backend(&self) -> bool {
        self.use_mork_backend
    }

    pub fn set_use_mork_backend(&mut self, enabled: bool) {
        self.use_mork_backend = enabled;
    }

    pub fn mork_limits(&self) -> MorkExecutionLimits {
        self.mork_limits
    }

    pub fn set_mork_limits(&mut self, limits: MorkExecutionLimits) {
        self.mork_limits = limits;
    }

    pub fn set_recursive_memo_enabled(&mut self, enabled: bool) {
        self.recursive_memo_enabled = enabled;
    }

    pub fn core_ground_eval_enabled(&self) -> bool {
        self.core_ground_eval_enabled
    }

    pub fn set_core_ground_eval_enabled(&mut self, enabled: bool) {
        self.core_ground_eval_enabled = enabled;
    }

    pub fn last_surface_diagnostics(&self) -> Option<SurfaceEvalDiagnostics> {
        self.last_surface_diagnostics.clone()
    }

    pub fn parse_line(input: &str) -> Result<SurfaceStmt> {
        match Self::parse_line_with_legacy_syntax(input, SurfaceSyntaxPolicy::Strict, None)? {
            Some(stmt) => Ok(stmt),
            None => bail!("empty MeTTa input"),
        }
    }

    pub fn parse_line_with_policy(
        input: &str,
        syntax_policy: SurfaceSyntaxPolicy,
    ) -> Result<Option<SurfaceStmt>> {
        Self::parse_line_with_legacy_syntax(input, syntax_policy, None)
    }

    pub fn parse_line_for_session(&self, input: &str) -> Result<Option<SurfaceStmt>> {
        if self.syntax_spec_required && self.syntax_spec.is_none() {
            if let Some(err) = &self.syntax_spec_error {
                bail!("{err}");
            }
            bail!(
                "surface syntax spec is required for profile {:?} but was not loaded",
                self.profile
            );
        }
        if self.lookup_plan_required && self.lookup_plan.is_none() {
            if let Some(err) = &self.lookup_plan_error {
                bail!("{err}");
            }
            bail!("lookup plan is required for profile {:?} but was not loaded", self.profile);
        }
        match self.parser_backend {
            SurfaceParserBackend::LegacySExpr => Self::parse_line_with_legacy_syntax(
                input,
                self.syntax_policy,
                self.syntax_spec.as_ref(),
            ),
            SurfaceParserBackend::TreeSitter => Self::parse_line_with_tree_sitter(
                input,
                self.syntax_policy,
                self.syntax_spec.as_ref(),
                self.profile,
            ),
        }
    }

    fn parse_line_with_legacy_syntax(
        input: &str,
        syntax_policy: SurfaceSyntaxPolicy,
        syntax_spec: Option<&SyntaxSpec>,
    ) -> Result<Option<SurfaceStmt>> {
        let syntax_spec = match syntax_spec {
            Some(spec) => Some(spec),
            None => Some(legacy_builtin_syntax_spec()),
        };
        let trimmed = input.trim();
        if trimmed.is_empty() {
            bail!("empty MeTTa input");
        }

        let (force_eval, body) = if let Some(rest) = trimmed.strip_prefix('!') {
            (true, rest.trim())
        } else {
            (false, trimmed)
        };

        if force_eval && body.is_empty() {
            if syntax_policy == SurfaceSyntaxPolicy::HyperonCompat {
                return Ok(None);
            }
            bail!("empty MeTTa input");
        }

        let tokens = tokenize(body)?;
        let mut pos = 0usize;
        let expr = parse_sexpr(&tokens, &mut pos)?;
        if pos != tokens.len() {
            bail!("unexpected trailing tokens in MeTTa expression");
        }

        classify_surface_stmt_from_expr(expr, force_eval, syntax_spec)
    }

    fn parse_line_with_tree_sitter(
        input: &str,
        syntax_policy: SurfaceSyntaxPolicy,
        syntax_spec: Option<&SyntaxSpec>,
        profile: SurfaceProfile,
    ) -> Result<Option<SurfaceStmt>> {
        if profile == SurfaceProfile::HE && syntax_spec.is_none() {
            bail!(
                "surface syntax spec is required for HE profile (missing he.syntax_spec.json/checksum artifacts)"
            );
        }
        let trimmed = input.trim();
        if trimmed.is_empty() {
            bail!("empty MeTTa input");
        }

        if trimmed == "!" {
            if syntax_policy == SurfaceSyntaxPolicy::HyperonCompat {
                return Ok(None);
            }
            bail!("empty MeTTa input");
        }

        let dialect_key = dialect_key_for_tree_sitter(syntax_spec, profile);
        let (force_eval, expr) = parse_sexpr_via_tree_sitter(&dialect_key, trimmed)?;
        classify_surface_stmt_from_expr(expr, force_eval, syntax_spec)
    }

    pub fn apply_stmt(&mut self, stmt: SurfaceStmt) -> Result<SurfaceOutcome> {
        match stmt {
            SurfaceStmt::DefineEq(lhs, rhs) => {
                self.add_eq_rule(DEFAULT_SPACE_IDENT, lhs, rhs)?;
                self.last_surface_diagnostics = None;
                let space_state = self.space_state(DEFAULT_SPACE_IDENT);
                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "added equation, total surface eq rules: {}, exact core eq rules: {}, pattern core eq rules: {}",
                        space_state.eq_patterns.len(),
                        space_state.eq_entries.len(),
                        space_state.pattern_eq_entries.len()
                    ),
                })
            },
            SurfaceStmt::DefineType(atom, ty) => {
                self.add_type_rule(DEFAULT_SPACE_IDENT, atom, ty)?;
                self.last_surface_diagnostics = None;
                let space_state = self.space_state(DEFAULT_SPACE_IDENT);
                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "added type entry, total type entries: {}",
                        space_state.type_entries.len()
                    ),
                })
            },
            SurfaceStmt::DeclareMemoized { space, head } => {
                self.last_surface_diagnostics = None;
                self.apply_declare_memoized_mutation(&space, &head)
            },
            SurfaceStmt::AllocSpace => {
                self.last_surface_diagnostics = None;
                let handle = self.alloc_fresh_space_ident();
                let out_atom = self.encode_expr_atom(&SExpr::Atom(handle))?;
                Ok(SurfaceOutcome::EvalMany {
                    core_terms: vec![format!("C_State(C_Done,C_Space(C_ANil,C_ANil),{out_atom})")],
                })
            },
            SurfaceStmt::Eval(expr) => {
                let core_terms = self.lower_eval_to_core_states(&expr)?;
                Ok(SurfaceOutcome::EvalMany { core_terms })
            },
            SurfaceStmt::EvalIn { space, expr } => {
                let core_terms = self.lower_eval_to_core_states_in_space(&space, &expr)?;
                Ok(SurfaceOutcome::EvalMany { core_terms })
            },
            SurfaceStmt::AddAtom { space, atom_expr } => {
                self.last_surface_diagnostics = None;
                self.apply_add_atom_mutation(&space, atom_expr)
            },
            SurfaceStmt::RemoveAtom { space, atom_expr } => {
                self.last_surface_diagnostics = None;
                self.apply_remove_atom_mutation(&space, atom_expr)
            },
            SurfaceStmt::NewSpace { space } => {
                let state = self.space_state_mut(&space);
                let removed_eq_rules = state.eq_patterns.len();
                let removed_exact_eq_rules = state.eq_entries.len();
                let removed_pattern_eq_rules = state.pattern_eq_entries.len();
                let removed_type_entries = state.type_entries.len();
                let removed_memoized_heads = state.memoized_heads.len();
                state.eq_entries.clear();
                state.pattern_eq_entries.clear();
                state.eq_patterns.clear();
                state.type_entries.clear();
                state.memoized_heads.clear();
                self.bump_space_revision(&space);
                self.last_surface_diagnostics = None;
                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "new space initialized for {}, removed {} surface eq rule(s), {} exact core eq rule(s), {} pattern core eq rule(s), {} type entry(ies), {} memoized declaration(s)",
                        space,
                        removed_eq_rules,
                        removed_exact_eq_rules,
                        removed_pattern_eq_rules,
                        removed_type_entries,
                        removed_memoized_heads
                    ),
                })
            },
        }
    }

    pub fn decode_atom_to_surface(&self, atom_core: &str) -> String {
        // HE profile: use HE-specific decoder
        if self.profile == SurfaceProfile::HE {
            return crate::metta_surface_he::he_decode_atom(atom_core);
        }
        let atom = atom_core.trim();
        if let Some(list_str) = self.try_decode_cons_list(atom) {
            return list_str;
        }
        match atom {
            "C_GBoolTrue" => return "true".to_string(),
            "C_GBoolFalse" => return "false".to_string(),
            "C_ATrue" => return "true".to_string(),
            "C_AFalse" => return "false".to_string(),
            "C_Bool" => return "Bool".to_string(),
            "C_Atom" => return "Atom".to_string(),
            "C_ANil" => return "()".to_string(),
            "C_not" => return "not".to_string(),
            "C_and" => return "and".to_string(),
            "C_or" => return "or".to_string(),
            "C_xor" => return "xor".to_string(),
            "C_eqBool" => return "eq-bool".to_string(),
            "C_add" => return "+".to_string(),
            "C_sub" => return "-".to_string(),
            "C_mul" => return "*".to_string(),
            "C_div" => return "/".to_string(),
            "C_modOp" => return "%".to_string(),
            "C_lt" => return "<".to_string(),
            "C_le" => return "<=".to_string(),
            "C_gt" => return ">".to_string(),
            "C_ge" => return ">=".to_string(),
            "C_eqInt" => return "==".to_string(),
            "C_concat" => return "concat".to_string(),
            "C_length" => return "length".to_string(),
            _ => {},
        }

        if let Some(inner) = atom
            .strip_prefix("C_GInt(")
            .and_then(|s| s.strip_suffix(')'))
        {
            if let Some(n) = decode_numeric_token(inner.trim()) {
                return n.to_string();
            }
            return inner.trim().to_string();
        }

        // UserAtom: user-defined symbol wrapping a GStringCodes name
        if let Some(inner) = atom
            .strip_prefix("C_UserAtom(")
            .and_then(|s| s.strip_suffix(')'))
        {
            if let Some(decoded) = try_decode_gstringcodes(inner.trim()) {
                return decoded;
            }
            // fallback: decode inner as generic atom
            return self.decode_atom_to_surface(inner.trim());
        }

        // GStringCodes: self-describing char-code cons-list (string literals)
        if let Some(decoded) = try_decode_gstringcodes(atom) {
            return quote_surface_string(&decoded);
        }

        // GString: bare token wrapper (logic-block outputs like concat results)
        if let Some(inner) = atom
            .strip_prefix("C_GString(")
            .and_then(|s| s.strip_suffix(')'))
        {
            return quote_surface_string(inner.trim());
        }

        atom.to_string()
    }

    fn try_decode_cons_list(&self, atom: &str) -> Option<String> {
        let mut items = Vec::new();
        let mut cur = atom.trim().to_string();
        loop {
            let cur_trim = cur.trim();
            if cur_trim == "C_ANil" {
                let rendered = if items.is_empty() {
                    "()".to_string()
                } else {
                    format!("({})", items.join(" "))
                };
                return Some(rendered);
            }
            if let Some(inner) = cur_trim
                .strip_prefix("C_ACons(")
                .and_then(|s| s.strip_suffix(')'))
            {
                let args = split_top_level_args(inner);
                if args.len() != 2 {
                    return None;
                }
                let head = self.decode_atom_to_surface(args[0].trim());
                items.push(head);
                cur = args[1].trim().to_string();
                continue;
            }
            if items.is_empty() {
                return None;
            }
            let tail = self.decode_atom_to_surface(cur_trim);
            return Some(format!("({} . {})", items.join(" "), tail));
        }
    }

    fn lower_eval_to_core_states(&mut self, expr: &SExpr) -> Result<Vec<String>> {
        self.lower_eval_to_core_states_in_space(DEFAULT_SPACE_IDENT, expr)
    }

    fn lower_eval_to_core_states_in_space(
        &mut self,
        space: &str,
        expr: &SExpr,
    ) -> Result<Vec<String>> {
        // HE profile: bypass surface rewriter entirely, lower directly to HE core term
        if self.profile == SurfaceProfile::HE {
            let space_state = self.space_state(space);
            let core_term = crate::metta_surface_he::he_lower_eval(expr, space_state)
                .map_err(|e| anyhow!("HE lowering: {e}"))?;
            self.last_surface_diagnostics = Some(SurfaceEvalDiagnostics {
                steps: 0,
                frontier_terms: 0,
                max_frontier: 0,
                rewrite_calls: 0,
                cache_hits: 0,
                cache_misses: 0,
                candidate_rules: 0,
                rule_checks: 0,
                rule_matches: 0,
                child_rewrites: 0,
                ground_rewrites: 0,
                memo_hits: 0,
                memo_misses: 0,
                memo_stores: 0,
                memo_in_progress_blocks: 0,
                truncated_by_branch_cap: 0,
                truncated_by_outcome_cap: false,
                hit_step_cap: false,
                normal_forms: 1,
                elapsed_ms: 0.0,
            });
            return Ok(vec![core_term]);
        }

        let core_fast_path =
            self.core_ground_eval_enabled && is_core_eval_candidate(expr, self.space_state(space));
        // Fast path for ground calls: route directly into core C_Eval so recursion can execute
        // in the core engine instead of pre-normalizing through the surface frontier loop.
        if core_fast_path {
            let (eqs, tys) = {
                let active_space = self.space_state(space);
                (
                    fold_eq_entries(&active_space.eq_entries, &active_space.pattern_eq_entries),
                    fold_type_entries(&active_space.type_entries),
                )
            };
            let src = self.encode_expr_atom(expr)?;
            self.last_surface_diagnostics = Some(SurfaceEvalDiagnostics {
                steps: 0,
                frontier_terms: 0,
                max_frontier: 0,
                rewrite_calls: 0,
                cache_hits: 0,
                cache_misses: 0,
                candidate_rules: 0,
                rule_checks: 0,
                rule_matches: 0,
                child_rewrites: 0,
                ground_rewrites: 0,
                memo_hits: 0,
                memo_misses: 0,
                memo_stores: 0,
                memo_in_progress_blocks: 0,
                truncated_by_branch_cap: 0,
                truncated_by_outcome_cap: false,
                hit_step_cap: false,
                normal_forms: 1,
                elapsed_ms: 0.0,
            });
            return Ok(vec![format!("C_State(C_Eval({src}),C_Space({eqs},{tys}),C_AFalse)")]);
        }

        let (normalized, profile) = self.normalize_surface_exprs(expr.clone(), space)?;
        self.last_surface_diagnostics = Some(profile.to_eval_diagnostics());
        if surface_profile_enabled() {
            eprintln!("{}", profile.as_log_line(space));
        }
        let (eqs, tys) = {
            let active_space = self.space_state(space);
            (
                fold_eq_entries(&active_space.eq_entries, &active_space.pattern_eq_entries),
                fold_type_entries(&active_space.type_entries),
            )
        };
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for nf in normalized {
            let instr = self.lower_expr_to_instr(&nf)?;
            let term = format!("C_State({instr},C_Space({eqs},{tys}),C_AFalse)");
            if seen.insert(term.clone()) {
                out.push(term);
            }
            if out.len() >= self.rewrite_limits.max_outcomes {
                break;
            }
        }
        if out.is_empty() {
            bail!("surface lowering produced no runnable branches")
        }
        Ok(out)
    }

    fn add_eq_rule(&mut self, space: &str, lhs: SExpr, rhs: SExpr) -> Result<()> {
        let lhs_atom = self.encode_expr_atom(&lhs)?;
        let rhs_atom = self.encode_expr_atom(&rhs)?;
        let has_pattern = contains_pattern_var(&lhs) || contains_pattern_var(&rhs);
        if !has_pattern {
            self.space_state_mut(space)
                .eq_entries
                .push((lhs_atom, rhs_atom));
        } else {
            self.space_state_mut(space)
                .pattern_eq_entries
                .push((lhs_atom, rhs_atom));
        }
        self.space_state_mut(space).eq_patterns.push((lhs, rhs));
        self.bump_space_revision(space);
        Ok(())
    }

    fn add_type_rule(&mut self, space: &str, atom: SExpr, ty: SExpr) -> Result<()> {
        let atom_enc = self.encode_expr_atom(&atom)?;
        let ty_enc = self.encode_expr_atom(&ty)?;
        self.space_state_mut(space)
            .type_entries
            .push((atom_enc, ty_enc));
        self.bump_space_revision(space);
        Ok(())
    }

    fn apply_declare_memoized_mutation(
        &mut self,
        space: &str,
        head: &str,
    ) -> Result<SurfaceOutcome> {
        if !is_valid_memo_head(head) {
            bail!("declare-memoized! expects a callable head atom, got '{}'", head);
        }
        let inserted = self
            .space_state_mut(space)
            .memoized_heads
            .insert(head.to_string());
        if inserted {
            self.bump_space_revision(space);
        }
        let total = self.space_state(space).memoized_heads.len();
        Ok(SurfaceOutcome::Mutation {
            message: if inserted {
                format!(
                    "declared memoized head '{}' in {}, total memoized declarations: {}",
                    head, space, total
                )
            } else {
                format!(
                    "memoized head '{}' already declared in {}, total memoized declarations: {}",
                    head, space, total
                )
            },
        })
    }

    fn apply_add_atom_mutation(&mut self, space: &str, atom_expr: SExpr) -> Result<SurfaceOutcome> {
        let SExpr::List(items) = atom_expr else {
            bail!("add-atom! expects a list payload: (= lhs rhs) or (: atom ty)");
        };
        if items.len() != 3 {
            bail!("add-atom! expects exactly one payload form: (= lhs rhs) or (: atom ty)");
        }
        let SExpr::Atom(head) = &items[0] else {
            bail!("add-atom! payload head must be '=' or ':'");
        };
        match head.as_str() {
            "=" => {
                self.add_eq_rule(space, items[1].clone(), items[2].clone())?;
                let space_state = self.space_state(space);
                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "added equation via add-atom! in {}, total surface eq rules: {}, exact core eq rules: {}, pattern core eq rules: {}",
                        space,
                        space_state.eq_patterns.len(),
                        space_state.eq_entries.len(),
                        space_state.pattern_eq_entries.len()
                    ),
                })
            },
            ":" => {
                self.add_type_rule(space, items[1].clone(), items[2].clone())?;
                let space_state = self.space_state(space);
                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "added type entry via add-atom! in {}, total type entries: {}",
                        space,
                        space_state.type_entries.len()
                    ),
                })
            },
            _ => bail!("add-atom! supports only (= lhs rhs) and (: atom ty) payloads"),
        }
    }

    fn apply_remove_atom_mutation(
        &mut self,
        space: &str,
        atom_expr: SExpr,
    ) -> Result<SurfaceOutcome> {
        let SExpr::List(items) = atom_expr else {
            bail!("remove-atom! expects a list payload: (= lhs rhs) or (: atom ty)");
        };
        if items.len() != 3 {
            bail!("remove-atom! expects exactly one payload form: (= lhs rhs) or (: atom ty)");
        }
        let SExpr::Atom(head) = &items[0] else {
            bail!("remove-atom! payload head must be '=' or ':'");
        };
        match head.as_str() {
            "=" => {
                let lhs = items[1].clone();
                let rhs = items[2].clone();
                let mut removed_surface_rules = 0usize;
                if let Some(state) = self.spaces.get_mut(space) {
                    let before_patterns = state.eq_patterns.len();
                    state
                        .eq_patterns
                        .retain(|(plhs, prhs)| *plhs != lhs || *prhs != rhs);
                    removed_surface_rules = before_patterns - state.eq_patterns.len();
                }

                let mut removed_exact_rules = 0usize;
                let has_pattern = contains_pattern_var(&lhs) || contains_pattern_var(&rhs);
                let lhs_atom = self.encode_expr_atom(&lhs)?;
                let rhs_atom = self.encode_expr_atom(&rhs)?;
                let mut removed_pattern_core_rules = 0usize;
                if !has_pattern {
                    if let Some(state) = self.spaces.get_mut(space) {
                        let before_exact = state.eq_entries.len();
                        state
                            .eq_entries
                            .retain(|(src, dst)| *src != lhs_atom || *dst != rhs_atom);
                        removed_exact_rules = before_exact - state.eq_entries.len();
                    }
                } else if let Some(state) = self.spaces.get_mut(space) {
                    let before_pattern = state.pattern_eq_entries.len();
                    state
                        .pattern_eq_entries
                        .retain(|(src, dst)| *src != lhs_atom || *dst != rhs_atom);
                    removed_pattern_core_rules = before_pattern - state.pattern_eq_entries.len();
                }
                if removed_surface_rules > 0
                    || removed_exact_rules > 0
                    || removed_pattern_core_rules > 0
                {
                    self.bump_space_revision(space);
                }

                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "removed equation via remove-atom! in {}, removed {} surface eq rule(s), {} exact core eq rule(s), {} pattern core eq rule(s)",
                        space, removed_surface_rules, removed_exact_rules, removed_pattern_core_rules
                    ),
                })
            },
            ":" => {
                let atom = items[1].clone();
                let ty = items[2].clone();
                let atom_enc = self.encode_expr_atom(&atom)?;
                let ty_enc = self.encode_expr_atom(&ty)?;
                let mut removed = 0usize;
                if let Some(state) = self.spaces.get_mut(space) {
                    let before = state.type_entries.len();
                    state
                        .type_entries
                        .retain(|(a, t)| *a != atom_enc || *t != ty_enc);
                    removed = before - state.type_entries.len();
                }
                if removed > 0 {
                    self.bump_space_revision(space);
                }
                Ok(SurfaceOutcome::Mutation {
                    message: format!(
                        "removed type entry via remove-atom! in {}, removed {} type entry(ies)",
                        space, removed
                    ),
                })
            },
            _ => bail!("remove-atom! supports only (= lhs rhs) and (: atom ty) payloads"),
        }
    }

    fn normalize_surface_exprs(
        &self,
        expr: SExpr,
        space: &str,
    ) -> Result<(Vec<SExpr>, SurfaceRewriteProfile)> {
        let started = Instant::now();
        let mut profile = SurfaceRewriteProfile::default();
        let space_state = self.space_state(space);

        // Surface-level MORK rewriting is intentionally disabled.
        //
        // Core backend execution must route through `Language::run_backend` so
        // semantics stay artifact-driven and shared across languages.
        #[cfg(feature = "mork-backend")]
        if self.use_mork_backend {
            bail!("surface MORK rewrite path is disabled; use core backend dispatch (run_backend)");
        }
        let index = RuleIndex::from_pattern_keys(
            space_state
                .eq_patterns
                .iter()
                .map(|(lhs, _rhs)| pattern_index_key(lhs)),
        );
        let mut rewrite_cache: HashMap<SExpr, Vec<SExpr>> = HashMap::new();
        let search_outcome = explore_rewrite_frontier(expr, self.rewrite_limits, |cur| {
            self.rewrite_many_once_cached(
                cur,
                space,
                space_state,
                &index,
                &mut rewrite_cache,
                &mut profile,
            )
        });
        profile.steps = profile.steps.saturating_add(search_outcome.stats.steps);
        profile.frontier_terms = profile
            .frontier_terms
            .saturating_add(search_outcome.stats.frontier_terms);
        profile.max_frontier = profile.max_frontier.max(search_outcome.stats.max_frontier);
        profile.truncated_by_branch_cap = profile
            .truncated_by_branch_cap
            .saturating_add(search_outcome.stats.truncated_by_branch_cap);
        profile.truncated_by_outcome_cap |= search_outcome.stats.truncated_by_outcome_cap;
        profile.hit_step_cap |= search_outcome.stats.hit_step_cap;
        profile.normal_forms = search_outcome.stats.normal_forms;
        profile.elapsed_ms = started.elapsed().as_secs_f64() * 1000.0;
        Ok((search_outcome.normal_forms, profile))
    }

    fn rewrite_many_once_cached(
        &self,
        expr: &SExpr,
        space: &str,
        space_state: &SurfaceSpaceState,
        index: &RuleIndex<String>,
        rewrite_cache: &mut HashMap<SExpr, Vec<SExpr>>,
        profile: &mut SurfaceRewriteProfile,
    ) -> Vec<SExpr> {
        profile.rewrite_calls += 1;
        if let Some(cached) = rewrite_cache.get(expr) {
            profile.cache_hits += 1;
            return cached.clone();
        }
        profile.cache_misses += 1;

        if rewrite_protected_builtin(expr) {
            let out = Vec::new();
            rewrite_cache.insert(expr.clone(), out.clone());
            return out;
        }

        let SExpr::List(items) = expr else {
            let out = Vec::new();
            rewrite_cache.insert(expr.clone(), out.clone());
            return out;
        };

        if let Some(mut memoized) = self.memoized_ground_call_normal_form(expr, space, profile) {
            memoized.retain(|item| item != expr);
            let out = dedup_exprs(memoized);
            rewrite_cache.insert(expr.clone(), out.clone());
            return out;
        }

        if let Some(out) = self.rewrite_if_condition_first(
            items,
            space,
            space_state,
            index,
            rewrite_cache,
            profile,
        ) {
            rewrite_cache.insert(expr.clone(), out.clone());
            return out;
        }

        // Prefer rewriting inside children first.
        let mut child_variants = Vec::new();
        for (idx, child) in items.iter().enumerate() {
            for child_rewritten in self.rewrite_many_once_cached(
                child,
                space,
                space_state,
                index,
                rewrite_cache,
                profile,
            ) {
                let mut next_items = items.clone();
                next_items[idx] = child_rewritten;
                child_variants.push(SExpr::List(next_items));
            }
        }
        if !child_variants.is_empty() {
            let out = dedup_exprs(child_variants);
            profile.child_rewrites += out.len();
            rewrite_cache.insert(expr.clone(), out.clone());
            return out;
        }

        if let Some(ground_eval) = eval_ground_expr(expr) {
            if &ground_eval != expr {
                let out = vec![ground_eval];
                profile.ground_rewrites += out.len();
                rewrite_cache.insert(expr.clone(), out.clone());
                return out;
            }
        }

        let out = self.try_apply_eq_rules_indexed(expr, space_state, index, profile);
        rewrite_cache.insert(expr.clone(), out.clone());
        out
    }

    fn rewrite_if_condition_first(
        &self,
        items: &[SExpr],
        space: &str,
        space_state: &SurfaceSpaceState,
        index: &RuleIndex<String>,
        rewrite_cache: &mut HashMap<SExpr, Vec<SExpr>>,
        profile: &mut SurfaceRewriteProfile,
    ) -> Option<Vec<SExpr>> {
        let [SExpr::Atom(head), cond, then_branch, else_branch] = items else {
            return None;
        };
        if head != "if" {
            return None;
        }

        if let Some(cond_bool) = bool_literal_atom(cond) {
            let out = if cond_bool {
                vec![then_branch.clone()]
            } else {
                vec![else_branch.clone()]
            };
            profile.ground_rewrites += out.len();
            return Some(out);
        }

        let cond_rewrites =
            self.rewrite_many_once_cached(cond, space, space_state, index, rewrite_cache, profile);
        if !cond_rewrites.is_empty() {
            let mut out = Vec::with_capacity(cond_rewrites.len());
            for cond_next in cond_rewrites {
                out.push(SExpr::List(vec![
                    SExpr::Atom(head.clone()),
                    cond_next,
                    then_branch.clone(),
                    else_branch.clone(),
                ]));
            }
            let out = dedup_exprs(out);
            profile.child_rewrites += out.len();
            return Some(out);
        }

        let expr = SExpr::List(items.to_vec());
        Some(self.try_apply_eq_rules_indexed(&expr, space_state, index, profile))
    }

    fn memoized_ground_call_normal_form(
        &self,
        expr: &SExpr,
        space: &str,
        profile: &mut SurfaceRewriteProfile,
    ) -> Option<Vec<SExpr>> {
        let memo_enabled =
            self.recursive_memo_enabled || self.is_declared_memoized_expr(space, expr);
        if !memo_enabled || !is_ground_call_expr(expr) {
            return None;
        }
        let prefer_exact =
            self.prefer_exact_rules || prefer_exact_rule_matches() || is_ground_call_expr(expr);
        let key = GroundCallMemoKey {
            space: space.to_string(),
            revision: self.space_revisions.get(space).copied().unwrap_or_default(),
            expr: expr.clone(),
            limits: self.rewrite_limits,
            exact_rules: prefer_exact,
        };
        match self.ground_call_memo.get_or_try_compute(key, || {
            self.normalize_surface_exprs(expr.clone(), space)
                .map(|(vals, nested)| {
                    profile.absorb_nested(&nested);
                    vals
                })
                .ok()
                .filter(|vals| !vals.is_empty())
        }) {
            MemoComputeOutcome::Hit(cached) => {
                profile.memo_hits += 1;
                Some(cached)
            },
            MemoComputeOutcome::InProgress => {
                profile.memo_in_progress_blocks += 1;
                None
            },
            MemoComputeOutcome::Stored(vals) => {
                profile.memo_misses += 1;
                profile.memo_stores += 1;
                Some(vals)
            },
            MemoComputeOutcome::Empty => {
                profile.memo_misses += 1;
                None
            },
        }
    }

    fn is_declared_memoized_expr(&self, space: &str, expr: &SExpr) -> bool {
        let SExpr::List(items) = expr else {
            return false;
        };
        let Some(SExpr::Atom(head)) = items.first() else {
            return false;
        };
        self.space_state(space).memoized_heads.contains(head)
    }

    fn try_apply_eq_rules_indexed(
        &self,
        expr: &SExpr,
        space_state: &SurfaceSpaceState,
        index: &RuleIndex<String>,
        profile: &mut SurfaceRewriteProfile,
    ) -> Vec<SExpr> {
        let prefer_exact =
            self.prefer_exact_rules || prefer_exact_rule_matches() || is_ground_call_expr(expr);
        let mut exact_out = Vec::new();
        let mut out = Vec::new();
        let candidate_indices = index.candidates_for_query(query_index_key(expr));
        profile.candidate_rules += candidate_indices.len();
        for rule_idx in candidate_indices {
            let (lhs, rhs) = &space_state.eq_patterns[rule_idx];
            profile.rule_checks += 1;
            let mut env = HashMap::new();
            if pattern_match(lhs, expr, &mut env) {
                profile.rule_matches += 1;
                let rewritten = pattern_subst(rhs, &env);
                if prefer_exact && !contains_pattern_var(lhs) {
                    exact_out.push(rewritten);
                } else {
                    out.push(rewritten);
                }
            }
        }
        if prefer_exact && !exact_out.is_empty() {
            return dedup_exprs(exact_out);
        }
        dedup_exprs(out)
    }

    fn space_state(&self, space: &str) -> &SurfaceSpaceState {
        if space == DEFAULT_SPACE_IDENT {
            return self
                .spaces
                .get(DEFAULT_SPACE_IDENT)
                .expect("default surface space must exist");
        }
        self.spaces.get(space).unwrap_or(&self.empty_space)
    }

    fn space_state_mut(&mut self, space: &str) -> &mut SurfaceSpaceState {
        self.space_revisions.entry(space.to_string()).or_insert(0);
        self.spaces.entry(space.to_string()).or_default()
    }

    fn bump_space_revision(&mut self, space: &str) {
        let key = space.to_string();
        let rev = self.space_revisions.entry(key.clone()).or_insert(0);
        *rev = rev.saturating_add(1);
        self.ground_call_memo.retain_keys(|k| k.space != key);
    }

    fn alloc_fresh_space_ident(&mut self) -> String {
        loop {
            self.next_space_index = self.next_space_index.saturating_add(1);
            let candidate = format!("&space{}", self.next_space_index);
            if !self.spaces.contains_key(&candidate) {
                self.spaces
                    .insert(candidate.clone(), SurfaceSpaceState::default());
                self.space_revisions.insert(candidate.clone(), 0);
                return candidate;
            }
        }
    }

    fn lower_expr_to_instr(&mut self, expr: &SExpr) -> Result<String> {
        if let SExpr::List(items) = expr {
            if let Some(SExpr::Atom(op)) = items.first() {
                match (op.as_str(), items.len()) {
                    ("unify", 3) => {
                        let lhs = self.encode_expr_atom(&items[1])?;
                        let rhs = self.encode_expr_atom(&items[2])?;
                        return Ok(format!("C_Unify({lhs},{rhs})"));
                    },
                    ("match", 3) => {
                        // First-class core match instruction.
                        let lhs = self.encode_expr_atom(&items[1])?;
                        let rhs = self.encode_expr_atom(&items[2])?;
                        return Ok(format!("C_Match({lhs},{rhs})"));
                    },
                    ("type-check", 3) => {
                        let atom = self.encode_expr_atom(&items[1])?;
                        let ty = self.encode_expr_atom(&items[2])?;
                        return Ok(format!("C_TypeCheck({atom},{ty})"));
                    },
                    ("cast", 3) => {
                        let atom = self.encode_expr_atom(&items[1])?;
                        let ty = self.encode_expr_atom(&items[2])?;
                        return Ok(format!("C_Cast({atom},{ty})"));
                    },
                    ("if", 4) => {
                        if let (Some(cond), Some(then_val), Some(else_val)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                            self.try_eval_ground_atom(&items[3])?,
                        ) {
                            if is_ground_bool_token(&cond) {
                                return Ok(format!("C_If({cond},{then_val},{else_val})"));
                            }
                        }
                    },
                    ("not", 2) => {
                        let arg = self.encode_ground_arg(&items[1])?;
                        return Ok(format!("C_Grounded1(C_not,{arg})"));
                    },
                    ("length", 2) => {
                        let arg = self.encode_ground_arg(&items[1])?;
                        return Ok(format!("C_Grounded1(C_length,{arg})"));
                    },
                    ("and", 3) => {
                        let lhs = self.encode_ground_arg(&items[1])?;
                        let rhs = self.encode_ground_arg(&items[2])?;
                        return Ok(format!("C_Grounded2(C_and,{lhs},{rhs})"));
                    },
                    ("or", 3) => {
                        let lhs = self.encode_ground_arg(&items[1])?;
                        let rhs = self.encode_ground_arg(&items[2])?;
                        return Ok(format!("C_Grounded2(C_or,{lhs},{rhs})"));
                    },
                    ("xor", 3) => {
                        let lhs = self.encode_ground_arg(&items[1])?;
                        let rhs = self.encode_ground_arg(&items[2])?;
                        return Ok(format!("C_Grounded2(C_xor,{lhs},{rhs})"));
                    },
                    ("eq-bool", 3) => {
                        let lhs = self.encode_ground_arg(&items[1])?;
                        let rhs = self.encode_ground_arg(&items[2])?;
                        return Ok(format!("C_Grounded2(C_eqBool,{lhs},{rhs})"));
                    },
                    ("+", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_add,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("-", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_sub,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("*", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_mul,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("/", 3) | ("div", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_div,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("%", 3) | ("mod", 3) | ("modOp", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_modOp,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("<", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_lt,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("<=", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_le,{lhs},{rhs})"));
                            }
                        }
                    },
                    (">", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_gt,{lhs},{rhs})"));
                            }
                        }
                    },
                    (">=", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_ge,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("==", 3) => {
                        if let (Some(lhs), Some(rhs)) = (
                            self.try_eval_ground_atom(&items[1])?,
                            self.try_eval_ground_atom(&items[2])?,
                        ) {
                            if is_ground_int_token(&lhs) && is_ground_int_token(&rhs) {
                                return Ok(format!("C_Grounded2(C_eqInt,{lhs},{rhs})"));
                            }
                        }
                    },
                    ("concat", 3) => {
                        let lhs = self.encode_ground_arg(&items[1])?;
                        let rhs = self.encode_ground_arg(&items[2])?;
                        return Ok(format!("C_Grounded2(C_concat,{lhs},{rhs})"));
                    },
                    _ => {},
                }
            }
        }

        let src = self.encode_expr_atom(expr)?;
        Ok(format!("C_Eval({src})"))
    }

    fn encode_ground_arg(&mut self, expr: &SExpr) -> Result<String> {
        if let Some(v) = self.try_eval_ground_atom(expr)? {
            Ok(v)
        } else {
            self.encode_expr_atom(expr)
        }
    }

    fn try_eval_ground_atom(&mut self, expr: &SExpr) -> Result<Option<String>> {
        match expr {
            SExpr::Atom(a) => {
                let lower = a.to_ascii_lowercase();
                if lower == "true" {
                    return Ok(Some("C_GBoolTrue".to_string()));
                }
                if lower == "false" {
                    return Ok(Some("C_GBoolFalse".to_string()));
                }
                if let Ok(n) = a.parse::<i32>() {
                    return Ok(Some(format_c_gint(n)));
                }
                Ok(None)
            },
            SExpr::List(items) => {
                if items.is_empty() {
                    return Ok(None);
                }
                let Some(SExpr::Atom(op)) = items.first() else {
                    return Ok(None);
                };
                match (op.as_str(), items.len()) {
                    ("if", 4) => {
                        let cond = self.try_eval_ground_atom(&items[1])?;
                        match cond.as_deref() {
                            Some("C_GBoolTrue") => self.try_eval_ground_atom(&items[2]),
                            Some("C_GBoolFalse") => self.try_eval_ground_atom(&items[3]),
                            _ => Ok(None),
                        }
                    },
                    ("not", 2) => {
                        let v = self.try_eval_ground_atom(&items[1])?;
                        match v.as_deref() {
                            Some("C_GBoolTrue") => Ok(Some("C_GBoolFalse".to_string())),
                            Some("C_GBoolFalse") => Ok(Some("C_GBoolTrue".to_string())),
                            _ => Ok(None),
                        }
                    },
                    ("and", 3) | ("or", 3) | ("xor", 3) | ("eq-bool", 3) => {
                        let lhs = self.try_eval_ground_atom(&items[1])?;
                        let rhs = self.try_eval_ground_atom(&items[2])?;
                        match (lhs.as_deref(), rhs.as_deref(), op.as_str()) {
                            (Some("C_GBoolTrue"), Some("C_GBoolTrue"), "and") => {
                                Ok(Some("C_GBoolTrue".to_string()))
                            },
                            (Some("C_GBoolTrue"), Some("C_GBoolFalse"), "and")
                            | (Some("C_GBoolFalse"), Some("C_GBoolTrue"), "and")
                            | (Some("C_GBoolFalse"), Some("C_GBoolFalse"), "and") => {
                                Ok(Some("C_GBoolFalse".to_string()))
                            },
                            (Some("C_GBoolTrue"), Some("C_GBoolTrue"), "or")
                            | (Some("C_GBoolTrue"), Some("C_GBoolFalse"), "or")
                            | (Some("C_GBoolFalse"), Some("C_GBoolTrue"), "or") => {
                                Ok(Some("C_GBoolTrue".to_string()))
                            },
                            (Some("C_GBoolFalse"), Some("C_GBoolFalse"), "or") => {
                                Ok(Some("C_GBoolFalse".to_string()))
                            },
                            (Some("C_GBoolTrue"), Some("C_GBoolFalse"), "xor")
                            | (Some("C_GBoolFalse"), Some("C_GBoolTrue"), "xor") => {
                                Ok(Some("C_GBoolTrue".to_string()))
                            },
                            (Some("C_GBoolTrue"), Some("C_GBoolTrue"), "xor")
                            | (Some("C_GBoolFalse"), Some("C_GBoolFalse"), "xor") => {
                                Ok(Some("C_GBoolFalse".to_string()))
                            },
                            (Some("C_GBoolTrue"), Some("C_GBoolTrue"), "eq-bool")
                            | (Some("C_GBoolFalse"), Some("C_GBoolFalse"), "eq-bool") => {
                                Ok(Some("C_GBoolTrue".to_string()))
                            },
                            (Some("C_GBoolTrue"), Some("C_GBoolFalse"), "eq-bool")
                            | (Some("C_GBoolFalse"), Some("C_GBoolTrue"), "eq-bool") => {
                                Ok(Some("C_GBoolFalse".to_string()))
                            },
                            _ => Ok(None),
                        }
                    },
                    ("+", 3)
                    | ("-", 3)
                    | ("*", 3)
                    | ("/", 3)
                    | ("%", 3)
                    | ("<", 3)
                    | ("<=", 3)
                    | (">", 3)
                    | (">=", 3)
                    | ("==", 3) => {
                        let lhs = self.try_eval_ground_atom(&items[1])?;
                        let rhs = self.try_eval_ground_atom(&items[2])?;
                        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
                            return Ok(None);
                        };
                        let Some(ln) = parse_c_gint(&lhs) else {
                            return Ok(None);
                        };
                        let Some(rn) = parse_c_gint(&rhs) else {
                            return Ok(None);
                        };

                        match op.as_str() {
                            "+" => Ok(ln.checked_add(rn).map(format_c_gint)),
                            "-" => Ok(ln.checked_sub(rn).map(format_c_gint)),
                            "*" => Ok(ln.checked_mul(rn).map(format_c_gint)),
                            "/" => Ok(ln.checked_div(rn).map(format_c_gint)),
                            "%" => Ok(ln.checked_rem(rn).map(format_c_gint)),
                            "<" => {
                                if ln < rn {
                                    Ok(Some("C_GBoolTrue".to_string()))
                                } else {
                                    Ok(Some("C_GBoolFalse".to_string()))
                                }
                            },
                            "<=" => {
                                if ln <= rn {
                                    Ok(Some("C_GBoolTrue".to_string()))
                                } else {
                                    Ok(Some("C_GBoolFalse".to_string()))
                                }
                            },
                            ">" => {
                                if ln > rn {
                                    Ok(Some("C_GBoolTrue".to_string()))
                                } else {
                                    Ok(Some("C_GBoolFalse".to_string()))
                                }
                            },
                            ">=" => {
                                if ln >= rn {
                                    Ok(Some("C_GBoolTrue".to_string()))
                                } else {
                                    Ok(Some("C_GBoolFalse".to_string()))
                                }
                            },
                            "==" => {
                                if ln == rn {
                                    Ok(Some("C_GBoolTrue".to_string()))
                                } else {
                                    Ok(Some("C_GBoolFalse".to_string()))
                                }
                            },
                            _ => Ok(None),
                        }
                    },
                    _ => Ok(None),
                }
            },
        }
    }

    fn encode_expr_atom(&mut self, expr: &SExpr) -> Result<String> {
        // HE profile: use HE-specific encoding
        if self.profile == SurfaceProfile::HE {
            return crate::metta_surface_he::he_encode_sexpr(expr)
                .map_err(|e| anyhow!("HE encode: {e}"));
        }
        match expr {
            SExpr::Atom(a) => self.encode_atom_symbol(a),
            SExpr::List(items) => {
                if items.is_empty() {
                    return Ok("C_ANil".to_string());
                }
                let mut acc = "C_ANil".to_string();
                for item in items.iter().rev() {
                    let item_enc = self.encode_expr_atom(item)?;
                    acc = format!("C_ACons({item_enc},{acc})");
                }
                Ok(acc)
            },
        }
    }

    fn encode_atom_symbol(&mut self, symbol: &str) -> Result<String> {
        if let Some(decoded) = parse_quoted_string_literal(symbol) {
            // String literals use bare GStringCodes (no UserAtom wrapper).
            return Ok(encode_gstringcodes(&decoded));
        }

        let lower = symbol.to_ascii_lowercase();
        match lower.as_str() {
            "true" => return Ok("C_GBoolTrue".to_string()),
            "false" => return Ok("C_GBoolFalse".to_string()),
            "atom" => return Ok("C_Atom".to_string()),
            "bool" => return Ok("C_Bool".to_string()),
            "nil" | "()" => return Ok("C_ANil".to_string()),
            "not" => return Ok("C_not".to_string()),
            "and" => return Ok("C_and".to_string()),
            "or" => return Ok("C_or".to_string()),
            "xor" => return Ok("C_xor".to_string()),
            "eq-bool" => return Ok("C_eqBool".to_string()),
            "add" => return Ok("C_add".to_string()),
            "sub" => return Ok("C_sub".to_string()),
            "mul" => return Ok("C_mul".to_string()),
            "div" | "/" => return Ok("C_div".to_string()),
            "mod" | "modop" | "%" => return Ok("C_modOp".to_string()),
            "lt" => return Ok("C_lt".to_string()),
            "le" | "<=" => return Ok("C_le".to_string()),
            "gt" | ">" => return Ok("C_gt".to_string()),
            "ge" | ">=" => return Ok("C_ge".to_string()),
            "eq-int" => return Ok("C_eqInt".to_string()),
            "concat" => return Ok("C_concat".to_string()),
            "length" => return Ok("C_length".to_string()),
            _ => {},
        }

        if let Ok(n) = symbol.parse::<i32>() {
            return Ok(format_c_gint(n));
        }

        // Encode user-defined symbols as UserAtom(GStringCodes(char-code cons-list)).
        // UserAtom wrapper preserves the symbol/string distinction:
        //   symbol `foo`  → C_UserAtom(C_GStringCodes(102,111,111))
        //   string "foo"  → C_GStringCodes(102,111,111)  (no wrapper)
        // Self-describing, portable, matches Lean FullLanguageDef.
        Ok(format!("C_UserAtom({})", encode_gstringcodes(symbol)))
    }
}

fn syntax_config_from_profile(
    profile: SurfaceProfile,
) -> (SurfaceSyntaxPolicy, Option<SyntaxSpec>, bool, Option<String>) {
    let dialect = match profile {
        SurfaceProfile::HE => Some("he"),
        SurfaceProfile::Legacy => None,
    };
    if let Some(dialect) = dialect {
        match try_load_syntax_spec(dialect) {
            Ok(Some(loaded)) => {
                let policy = if loaded.spec.eval_prefix.bang_prefixed_word_is_symbol {
                    SurfaceSyntaxPolicy::HyperonCompat
                } else {
                    SurfaceSyntaxPolicy::Strict
                };
                (policy, Some(loaded.spec), true, None)
            },
            Ok(None) => (
                SurfaceSyntaxPolicy::HyperonCompat,
                None,
                true,
                Some(
                    "surface syntax spec required for HE profile, but no syntax artifacts were found"
                        .to_string(),
                ),
            ),
            Err(e) => (
                SurfaceSyntaxPolicy::HyperonCompat,
                None,
                true,
                Some(format!("failed to load HE syntax spec: {e}")),
            ),
        }
    } else {
        (
            SurfaceSyntaxPolicy::Strict,
            Some(legacy_builtin_syntax_spec().clone()),
            false,
            None,
        )
    }
}

fn lookup_plan_config_from_profile(
    profile: SurfaceProfile,
) -> (
    Option<LookupPlanArtifact>,
    Option<HashMap<String, LookupRelationMetadata>>,
    bool,
    Option<String>,
) {
    let dialect = match profile {
        SurfaceProfile::HE => Some("he"),
        SurfaceProfile::Legacy => None,
    };
    if let Some(dialect) = dialect {
        match try_load_lookup_plan(dialect) {
            Ok(Some(loaded)) => {
                let metadata = relation_metadata_index(&loaded.artifact);
                (Some(loaded.artifact), Some(metadata), true, None)
            },
            Ok(None) => (
                None,
                None,
                true,
                Some(
                    "lookup-plan artifacts are required for HE profile, but no lookup-plan artifacts were found"
                        .to_string(),
                ),
            ),
            Err(e) => (
                None,
                None,
                true,
                Some(format!("failed to load HE lookup plan: {e}")),
            ),
        }
    } else {
        (None, None, false, None)
    }
}

fn legacy_builtin_syntax_spec() -> &'static SyntaxSpec {
    static LEGACY: OnceLock<SyntaxSpec> = OnceLock::new();
    LEGACY.get_or_init(|| SyntaxSpec {
        schema_version: 2,
        dialect: "Legacy".to_string(),
        lexer: LexerSpec {
            line_comment_start: Some(";".to_string()),
            supports_string_literals: true,
            string_delimiter: "\"".to_string(),
            escape_char: "\\".to_string(),
            sexpr_open: "(".to_string(),
            sexpr_close: ")".to_string(),
            allow_hash_in_symbol: true,
            reserve_hash_in_variable: true,
            trim_ascii_whitespace: true,
        },
        eval_prefix: EvalPrefixPolicy {
            prefix: "!".to_string(),
            allow_whitespace_after_prefix: true,
            allow_newline_after_prefix: true,
            bang_prefixed_word_is_symbol: false,
        },
        lowering_heads: LoweringHeads::default(),
        dispatch_policy: DispatchPolicy::default(),
        command_heads: vec![
            CommandHead {
                head: "=".to_string(),
                command: "defineEq".to_string(),
                arity_min: 2,
                arity_max: Some(2),
            },
            CommandHead {
                head: ":".to_string(),
                command: "defineType".to_string(),
                arity_min: 2,
                arity_max: Some(2),
            },
            CommandHead {
                head: "add-atom!".to_string(),
                command: "addAtom".to_string(),
                arity_min: 1,
                arity_max: Some(2),
            },
            CommandHead {
                head: "remove-atom!".to_string(),
                command: "removeAtom".to_string(),
                arity_min: 1,
                arity_max: Some(2),
            },
            CommandHead {
                head: "new-space!".to_string(),
                command: "newSpace".to_string(),
                arity_min: 0,
                arity_max: Some(1),
            },
            CommandHead {
                head: "declare-memoized!".to_string(),
                command: "declareMemoized".to_string(),
                arity_min: 1,
                arity_max: Some(2),
            },
            CommandHead {
                head: "in-space".to_string(),
                command: "inSpace".to_string(),
                arity_min: 2,
                arity_max: Some(2),
            },
        ],
        head_aliases: vec![
            crate::syntax_spec::SugarAlias {
                alias: "add-atom".to_string(),
                canonical: "add-atom!".to_string(),
            },
            crate::syntax_spec::SugarAlias {
                alias: "remove-atom".to_string(),
                canonical: "remove-atom!".to_string(),
            },
            crate::syntax_spec::SugarAlias {
                alias: "new-space".to_string(),
                canonical: "new-space!".to_string(),
            },
            crate::syntax_spec::SugarAlias {
                alias: "declare-memoized".to_string(),
                canonical: "declare-memoized!".to_string(),
            },
        ],
        eval_space_aliases: vec![
            crate::syntax_spec::EvalSpaceAlias {
                head: "match".to_string(),
                canonical_head: "match".to_string(),
                arity: 2,
            },
            crate::syntax_spec::EvalSpaceAlias {
                head: "unify".to_string(),
                canonical_head: "unify".to_string(),
                arity: 2,
            },
            crate::syntax_spec::EvalSpaceAlias {
                head: "type-check".to_string(),
                canonical_head: "type-check".to_string(),
                arity: 2,
            },
            crate::syntax_spec::EvalSpaceAlias {
                head: "cast".to_string(),
                canonical_head: "cast".to_string(),
                arity: 2,
            },
        ],
        predicate_special_heads: vec![],
    })
}

fn parser_backend_from_profile(_profile: SurfaceProfile) -> SurfaceParserBackend {
    match std::env::var("METTAIL_PARSER_BACKEND") {
        Ok(value) if value.eq_ignore_ascii_case("tree-sitter") => SurfaceParserBackend::TreeSitter,
        _ => SurfaceParserBackend::LegacySExpr,
    }
}

fn classify_surface_stmt_from_expr(
    expr: SExpr,
    force_eval: bool,
    syntax_spec: Option<&SyntaxSpec>,
) -> Result<Option<SurfaceStmt>> {
    if force_eval {
        if let Some(space_stmt) = parse_mutable_space_eval_stmt(&expr, syntax_spec) {
            return Ok(Some(space_stmt));
        }
    }
    if let Some(space_stmt) = parse_mutable_space_stmt(&expr, syntax_spec) {
        return Ok(Some(space_stmt));
    }
    if let Some(space_stmt) = parse_in_space_mutable_stmt(&expr, syntax_spec) {
        return Ok(Some(space_stmt));
    }
    if let Some((space, expr_in_space)) = parse_eval_space_stmt(&expr, syntax_spec) {
        return Ok(Some(SurfaceStmt::EvalIn { space, expr: expr_in_space }));
    }

    if force_eval {
        return Ok(Some(SurfaceStmt::Eval(expr)));
    }

    let syntax_spec = match syntax_spec {
        Some(spec) => spec,
        None => legacy_builtin_syntax_spec(),
    };
    if let SExpr::List(items) = &expr {
        if items.len() == 3 {
            if let SExpr::Atom(head) = &items[0] {
                match command_for_head(head, syntax_spec) {
                    Some(KnownCommand::DefineEq) => {
                        return Ok(Some(SurfaceStmt::DefineEq(items[1].clone(), items[2].clone())));
                    },
                    Some(KnownCommand::DefineType) => {
                        return Ok(Some(SurfaceStmt::DefineType(
                            items[1].clone(),
                            items[2].clone(),
                        )));
                    },
                    _ => {},
                }
            }
        }
    }

    Ok(Some(SurfaceStmt::Eval(expr)))
}

fn dialect_key_for_tree_sitter(
    syntax_spec: Option<&SyntaxSpec>,
    profile: SurfaceProfile,
) -> String {
    if let Some(spec) = syntax_spec {
        let dialect = spec.dialect.to_ascii_lowercase();
        if dialect.contains("petta") {
            return "petta".to_string();
        }
        if dialect.contains("he") {
            return "he".to_string();
        }
    }
    match profile {
        SurfaceProfile::HE => "he".to_string(),
        SurfaceProfile::Legacy => "he".to_string(),
    }
}

extern "C" {
    fn tree_sitter_metta_he() -> TSLanguage;
    fn tree_sitter_metta_petta() -> TSLanguage;
}

fn tree_sitter_language_for_dialect(dialect_key: &str) -> Result<TSLanguage> {
    match dialect_key {
        "he" => Ok(unsafe { tree_sitter_metta_he() }),
        "petta" => Ok(unsafe { tree_sitter_metta_petta() }),
        other => bail!("unsupported embedded tree-sitter dialect '{}'", other),
    }
}

fn parse_sexpr_via_tree_sitter(dialect_key: &str, input: &str) -> Result<(bool, SExpr)> {
    let mut parser = TSParser::new();
    let language = tree_sitter_language_for_dialect(dialect_key)?;
    parser.set_language(&language).map_err(|e| {
        anyhow!("failed to set embedded tree-sitter language '{}': {e}", dialect_key)
    })?;
    let tree = parser
        .parse(input, None)
        .ok_or_else(|| anyhow!("embedded tree-sitter returned no parse tree"))?;
    let root = tree.root_node();
    if root.has_error() || root.is_error() {
        bail!("embedded tree-sitter parse contains ERROR/MISSING nodes");
    }
    decode_tree_sitter_root(root, input)
}

fn decode_tree_sitter_root(root: TSNode<'_>, source: &str) -> Result<(bool, SExpr)> {
    let mut tops = Vec::new();
    for idx in 0..root.named_child_count() {
        if let Some(child) = root.named_child(idx) {
            if matches!(child.kind(), "eval_form" | "atom") {
                tops.push(child);
            }
        }
    }

    if tops.is_empty() {
        bail!("embedded tree-sitter parse produced no top-level form");
    }
    if tops.len() != 1 {
        bail!(
            "embedded tree-sitter parse produced {} top-level forms; expected exactly 1",
            tops.len()
        );
    }

    let top = tops[0];
    if top.kind() == "eval_form" {
        let atom = first_named_child_of_kind(top, "atom")
            .ok_or_else(|| anyhow!("embedded tree-sitter eval_form missing atom child"))?;
        return Ok((true, decode_tree_sitter_atom(atom, source)?));
    }
    Ok((false, decode_tree_sitter_atom(top, source)?))
}

fn first_named_child_of_kind<'a>(node: TSNode<'a>, kind: &str) -> Option<TSNode<'a>> {
    (0..node.named_child_count())
        .filter_map(|idx| node.named_child(idx))
        .find(|child| child.kind() == kind)
}

fn decode_tree_sitter_atom(node: TSNode<'_>, source: &str) -> Result<SExpr> {
    match node.kind() {
        "atom" => {
            let child = (0..node.named_child_count())
                .filter_map(|idx| node.named_child(idx))
                .find(|child| child.kind() != "comment")
                .ok_or_else(|| anyhow!("embedded tree-sitter atom node has no concrete child"))?;
            decode_tree_sitter_atom(child, source)
        },
        "symbol" | "variable" | "string" => {
            let text = node
                .utf8_text(source.as_bytes())
                .map_err(|e| anyhow!("invalid utf8 span from embedded tree-sitter: {e}"))?;
            Ok(SExpr::Atom(text.to_string()))
        },
        "list" => {
            let mut items = Vec::new();
            for idx in 0..node.named_child_count() {
                if let Some(child) = node.named_child(idx) {
                    if child.kind() == "atom" {
                        items.push(decode_tree_sitter_atom(child, source)?);
                    }
                }
            }
            Ok(SExpr::List(items))
        },
        other => bail!("unsupported embedded tree-sitter atom node kind '{}'", other),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KnownCommand {
    DefineEq,
    DefineType,
    AddAtom,
    RemoveAtom,
    NewSpace,
    DeclareMemoized,
    InSpace,
}

fn known_command_from_name(name: &str) -> Option<KnownCommand> {
    match name {
        "defineEq" => Some(KnownCommand::DefineEq),
        "defineType" => Some(KnownCommand::DefineType),
        "addAtom" => Some(KnownCommand::AddAtom),
        "removeAtom" => Some(KnownCommand::RemoveAtom),
        "newSpace" => Some(KnownCommand::NewSpace),
        "declareMemoized" => Some(KnownCommand::DeclareMemoized),
        "inSpace" => Some(KnownCommand::InSpace),
        _ => None,
    }
}

fn command_for_head(head: &str, syntax_spec: &SyntaxSpec) -> Option<KnownCommand> {
    let canonical_head: Cow<'_, str> = match syntax_spec
        .head_aliases
        .iter()
        .find(|entry| entry.alias == head)
    {
        Some(alias) => Cow::Borrowed(alias.canonical.as_str()),
        None => Cow::Borrowed(head),
    };
    syntax_spec
        .command_heads
        .iter()
        .find(|entry| entry.head == canonical_head.as_ref())
        .and_then(|entry| known_command_from_name(&entry.command))
}

fn parse_mutable_space_stmt(expr: &SExpr, syntax_spec: Option<&SyntaxSpec>) -> Option<SurfaceStmt> {
    let syntax_spec = match syntax_spec {
        Some(spec) => spec,
        None => legacy_builtin_syntax_spec(),
    };
    let SExpr::List(items) = expr else {
        return None;
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return None;
    };
    match command_for_head(head, syntax_spec) {
        Some(KnownCommand::AddAtom) => match items.as_slice() {
            [_op, atom_expr] => Some(SurfaceStmt::AddAtom {
                space: DEFAULT_SPACE_IDENT.to_string(),
                atom_expr: atom_expr.clone(),
            }),
            [_op, SExpr::Atom(space), atom_expr] if is_space_ident(space) => {
                Some(SurfaceStmt::AddAtom {
                    space: space.clone(),
                    atom_expr: atom_expr.clone(),
                })
            },
            _ => None,
        },
        Some(KnownCommand::RemoveAtom) => match items.as_slice() {
            [_op, atom_expr] => Some(SurfaceStmt::RemoveAtom {
                space: DEFAULT_SPACE_IDENT.to_string(),
                atom_expr: atom_expr.clone(),
            }),
            [_op, SExpr::Atom(space), atom_expr] if is_space_ident(space) => {
                Some(SurfaceStmt::RemoveAtom {
                    space: space.clone(),
                    atom_expr: atom_expr.clone(),
                })
            },
            _ => None,
        },
        Some(KnownCommand::NewSpace) => match items.as_slice() {
            [_op] => Some(SurfaceStmt::NewSpace { space: DEFAULT_SPACE_IDENT.to_string() }),
            [_op, SExpr::Atom(space)] if is_space_ident(space) => {
                Some(SurfaceStmt::NewSpace { space: space.clone() })
            },
            _ => None,
        },
        Some(KnownCommand::DeclareMemoized) => match items.as_slice() {
            [_op, target] => {
                extract_declared_memo_head(target).map(|head| SurfaceStmt::DeclareMemoized {
                    space: DEFAULT_SPACE_IDENT.to_string(),
                    head,
                })
            },
            [_op, SExpr::Atom(space), target] if is_space_ident(space) => {
                extract_declared_memo_head(target)
                    .map(|head| SurfaceStmt::DeclareMemoized { space: space.clone(), head })
            },
            _ => None,
        },
        Some(KnownCommand::DefineEq) if items.len() == 3 => {
            Some(SurfaceStmt::DefineEq(items[1].clone(), items[2].clone()))
        },
        Some(KnownCommand::DefineType) if items.len() == 3 => {
            Some(SurfaceStmt::DefineType(items[1].clone(), items[2].clone()))
        },
        _ => None,
    }
}

fn parse_mutable_space_eval_stmt(
    expr: &SExpr,
    syntax_spec: Option<&SyntaxSpec>,
) -> Option<SurfaceStmt> {
    let syntax_spec = match syntax_spec {
        Some(spec) => spec,
        None => legacy_builtin_syntax_spec(),
    };
    let SExpr::List(items) = expr else {
        return None;
    };
    match items.as_slice() {
        [SExpr::Atom(op)]
            if command_for_head(op, syntax_spec) == Some(KnownCommand::NewSpace)
                && op.ends_with('!') =>
        {
            Some(SurfaceStmt::AllocSpace)
        },
        _ => None,
    }
}

fn remap_stmt_space(space: String, default_space: &str) -> String {
    if space == DEFAULT_SPACE_IDENT {
        default_space.to_string()
    } else {
        space
    }
}

fn retarget_surface_stmt(stmt: SurfaceStmt, default_space: &str) -> SurfaceStmt {
    if default_space == DEFAULT_SPACE_IDENT {
        return stmt;
    }
    match stmt {
        SurfaceStmt::DefineEq(lhs, rhs) => SurfaceStmt::AddAtom {
            space: default_space.to_string(),
            atom_expr: SExpr::List(vec![SExpr::Atom("=".to_string()), lhs, rhs]),
        },
        SurfaceStmt::DefineType(atom, ty) => SurfaceStmt::AddAtom {
            space: default_space.to_string(),
            atom_expr: SExpr::List(vec![SExpr::Atom(":".to_string()), atom, ty]),
        },
        SurfaceStmt::Eval(expr) => SurfaceStmt::EvalIn { space: default_space.to_string(), expr },
        SurfaceStmt::EvalIn { space, expr } => SurfaceStmt::EvalIn {
            space: remap_stmt_space(space, default_space),
            expr,
        },
        SurfaceStmt::AddAtom { space, atom_expr } => SurfaceStmt::AddAtom {
            space: remap_stmt_space(space, default_space),
            atom_expr,
        },
        SurfaceStmt::RemoveAtom { space, atom_expr } => SurfaceStmt::RemoveAtom {
            space: remap_stmt_space(space, default_space),
            atom_expr,
        },
        SurfaceStmt::DeclareMemoized { space, head } => SurfaceStmt::DeclareMemoized {
            space: remap_stmt_space(space, default_space),
            head,
        },
        SurfaceStmt::NewSpace { space } => SurfaceStmt::NewSpace {
            space: remap_stmt_space(space, default_space),
        },
        SurfaceStmt::AllocSpace => SurfaceStmt::AllocSpace,
    }
}

fn parse_in_space_mutable_stmt(
    expr: &SExpr,
    syntax_spec: Option<&SyntaxSpec>,
) -> Option<SurfaceStmt> {
    let syntax_spec = match syntax_spec {
        Some(spec) => spec,
        None => legacy_builtin_syntax_spec(),
    };
    let SExpr::List(items) = expr else {
        return None;
    };
    let [SExpr::Atom(op), SExpr::Atom(space), inner] = items.as_slice() else {
        return None;
    };
    if command_for_head(op, syntax_spec) != Some(KnownCommand::InSpace) || !is_space_ident(space) {
        return None;
    }

    if let Some(inner_stmt) = parse_mutable_space_stmt(inner, Some(syntax_spec)) {
        return Some(retarget_surface_stmt(inner_stmt, space));
    }

    if let SExpr::List(inner_items) = inner {
        if inner_items.len() == 3 {
            if let Some(SExpr::Atom(head)) = inner_items.first() {
                match command_for_head(head, syntax_spec) {
                    Some(KnownCommand::DefineEq) | Some(KnownCommand::DefineType) => {
                        return Some(SurfaceStmt::AddAtom {
                            space: space.clone(),
                            atom_expr: inner.clone(),
                        });
                    },
                    _ => {},
                }
            }
        }
    }

    None
}

fn parse_eval_space_stmt(
    expr: &SExpr,
    syntax_spec: Option<&SyntaxSpec>,
) -> Option<(String, SExpr)> {
    let syntax_spec = match syntax_spec {
        Some(spec) => spec,
        None => legacy_builtin_syntax_spec(),
    };
    let SExpr::List(items) = expr else {
        return None;
    };
    if let [SExpr::Atom(op), SExpr::Atom(space), expr] = items.as_slice() {
        if command_for_head(op, syntax_spec) == Some(KnownCommand::InSpace) && is_space_ident(space)
        {
            return Some((space.clone(), expr.clone()));
        }
    }

    if let [SExpr::Atom(op), SExpr::Atom(space), rest @ ..] = items.as_slice() {
        if !is_space_ident(space) {
            return None;
        }
        // Spec-driven `(head &space ...)` aliases; keeps parser policy out of hardcoded Rust branches.
        for alias in &syntax_spec.eval_space_aliases {
            if op == &alias.head && rest.len() as u64 == alias.arity {
                let mut lowered = Vec::with_capacity(rest.len() + 1);
                lowered.push(SExpr::Atom(alias.canonical_head.clone()));
                lowered.extend(rest.iter().cloned());
                return Some((space.clone(), SExpr::List(lowered)));
            }
        }
    }

    None
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfaceOutcome {
    Mutation { message: String },
    EvalMany { core_terms: Vec<String> },
}

#[derive(Debug, Clone, Default)]
struct SurfaceRewriteProfile {
    steps: usize,
    frontier_terms: usize,
    max_frontier: usize,
    rewrite_calls: usize,
    cache_hits: usize,
    cache_misses: usize,
    candidate_rules: usize,
    rule_checks: usize,
    rule_matches: usize,
    child_rewrites: usize,
    ground_rewrites: usize,
    memo_hits: usize,
    memo_misses: usize,
    memo_stores: usize,
    memo_in_progress_blocks: usize,
    truncated_by_branch_cap: usize,
    truncated_by_outcome_cap: bool,
    hit_step_cap: bool,
    normal_forms: usize,
    elapsed_ms: f64,
}

impl SurfaceRewriteProfile {
    fn as_log_line(&self, space: &str) -> String {
        format!(
            "[surface-rewrite-profile] space={space} steps={} frontier_terms={} max_frontier={} rewrite_calls={} cache_hits={} cache_misses={} candidate_rules={} rule_checks={} rule_matches={} child_rewrites={} ground_rewrites={} memo_hits={} memo_misses={} memo_stores={} memo_in_progress_blocks={} normal_forms={} trunc_branch={} trunc_outcomes={} hit_step_cap={} elapsed_ms={:.3}",
            self.steps,
            self.frontier_terms,
            self.max_frontier,
            self.rewrite_calls,
            self.cache_hits,
            self.cache_misses,
            self.candidate_rules,
            self.rule_checks,
            self.rule_matches,
            self.child_rewrites,
            self.ground_rewrites,
            self.memo_hits,
            self.memo_misses,
            self.memo_stores,
            self.memo_in_progress_blocks,
            self.normal_forms,
            self.truncated_by_branch_cap,
            self.truncated_by_outcome_cap,
            self.hit_step_cap,
            self.elapsed_ms
        )
    }

    fn to_eval_diagnostics(&self) -> SurfaceEvalDiagnostics {
        SurfaceEvalDiagnostics {
            steps: self.steps,
            frontier_terms: self.frontier_terms,
            max_frontier: self.max_frontier,
            rewrite_calls: self.rewrite_calls,
            cache_hits: self.cache_hits,
            cache_misses: self.cache_misses,
            candidate_rules: self.candidate_rules,
            rule_checks: self.rule_checks,
            rule_matches: self.rule_matches,
            child_rewrites: self.child_rewrites,
            ground_rewrites: self.ground_rewrites,
            memo_hits: self.memo_hits,
            memo_misses: self.memo_misses,
            memo_stores: self.memo_stores,
            memo_in_progress_blocks: self.memo_in_progress_blocks,
            truncated_by_branch_cap: self.truncated_by_branch_cap,
            truncated_by_outcome_cap: self.truncated_by_outcome_cap,
            hit_step_cap: self.hit_step_cap,
            normal_forms: self.normal_forms,
            elapsed_ms: self.elapsed_ms,
        }
    }

    fn absorb_nested(&mut self, nested: &SurfaceRewriteProfile) {
        self.steps = self.steps.saturating_add(nested.steps);
        self.frontier_terms = self.frontier_terms.saturating_add(nested.frontier_terms);
        self.max_frontier = self.max_frontier.max(nested.max_frontier);
        self.rewrite_calls = self.rewrite_calls.saturating_add(nested.rewrite_calls);
        self.cache_hits = self.cache_hits.saturating_add(nested.cache_hits);
        self.cache_misses = self.cache_misses.saturating_add(nested.cache_misses);
        self.candidate_rules = self.candidate_rules.saturating_add(nested.candidate_rules);
        self.rule_checks = self.rule_checks.saturating_add(nested.rule_checks);
        self.rule_matches = self.rule_matches.saturating_add(nested.rule_matches);
        self.child_rewrites = self.child_rewrites.saturating_add(nested.child_rewrites);
        self.ground_rewrites = self.ground_rewrites.saturating_add(nested.ground_rewrites);
        self.memo_hits = self.memo_hits.saturating_add(nested.memo_hits);
        self.memo_misses = self.memo_misses.saturating_add(nested.memo_misses);
        self.memo_stores = self.memo_stores.saturating_add(nested.memo_stores);
        self.memo_in_progress_blocks = self
            .memo_in_progress_blocks
            .saturating_add(nested.memo_in_progress_blocks);
        self.truncated_by_branch_cap = self
            .truncated_by_branch_cap
            .saturating_add(nested.truncated_by_branch_cap);
        self.truncated_by_outcome_cap |= nested.truncated_by_outcome_cap;
        self.hit_step_cap |= nested.hit_step_cap;
        self.normal_forms = self.normal_forms.saturating_add(nested.normal_forms);
        self.elapsed_ms += nested.elapsed_ms;
    }
}

fn pattern_index_key(lhs: &SExpr) -> PatternIndexKey<String> {
    match lhs {
        SExpr::Atom(a) if is_pattern_var_atom(a) => PatternIndexKey::AtomAny,
        SExpr::Atom(a) => PatternIndexKey::AtomConst(a.clone()),
        SExpr::List(items) => {
            let arity = items.len();
            if let Some(SExpr::Atom(head)) = items.first() {
                if !is_pattern_var_atom(head) {
                    return PatternIndexKey::ListHeadConst { arity, head: head.clone() };
                }
            }
            PatternIndexKey::ListArityAny { arity }
        },
    }
}

fn query_index_key(expr: &SExpr) -> QueryIndexKey<String> {
    match expr {
        SExpr::Atom(a) if is_pattern_var_atom(a) => QueryIndexKey::AtomOther,
        SExpr::Atom(a) => QueryIndexKey::AtomConst(a.clone()),
        SExpr::List(items) => QueryIndexKey::List {
            arity: items.len(),
            head: items.first().and_then(|h| {
                if let SExpr::Atom(head) = h {
                    if !is_pattern_var_atom(head) {
                        return Some(head.clone());
                    }
                }
                None
            }),
        },
    }
}

fn surface_profile_enabled() -> bool {
    std::env::var_os("METTAIL_SURFACE_PROFILE").is_some()
}

fn prefer_exact_rule_matches() -> bool {
    std::env::var_os("METTAIL_SURFACE_PREFER_EXACT_RULES").is_some()
}

fn dedup_exprs(exprs: Vec<SExpr>) -> Vec<SExpr> {
    dedup_stable(exprs)
}

fn fold_eq_entries(entries: &[(String, String)], pattern_entries: &[(String, String)]) -> String {
    let mut acc = "C_ANil".to_string();
    for (src, dst) in pattern_entries.iter().rev() {
        acc = format!("C_ACons(C_APEqEntry({src},{dst}),{acc})");
    }
    for (src, dst) in entries.iter().rev() {
        acc = format!("C_ACons(C_AEqEntry({src},{dst}),{acc})");
    }
    acc
}

fn fold_type_entries(entries: &[(String, String)]) -> String {
    let mut acc = "C_ANil".to_string();
    for (atom, ty) in entries.iter().rev() {
        acc = format!("C_ACons(C_ATypeEntry({atom},{ty}),{acc})");
    }
    acc
}

fn tokenize(input: &str) -> Result<Vec<String>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '(' | ')' => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
                tokens.push(ch.to_string());
            },
            '"' => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
                let mut s = String::from("\"");
                let mut escaped = false;
                let mut closed = false;
                for c in chars.by_ref() {
                    s.push(c);
                    if escaped {
                        escaped = false;
                        continue;
                    }
                    if c == '\\' {
                        escaped = true;
                        continue;
                    }
                    if c == '"' {
                        closed = true;
                        break;
                    }
                }
                if !closed {
                    bail!("unterminated string literal");
                }
                tokens.push(s);
            },
            c if c.is_whitespace() => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
            },
            _ => current.push(ch),
        }
    }

    if !current.is_empty() {
        tokens.push(current);
    }

    if tokens.is_empty() {
        bail!("empty MeTTa input");
    }
    Ok(tokens)
}

fn parse_sexpr(tokens: &[String], pos: &mut usize) -> Result<SExpr> {
    let tok = tokens
        .get(*pos)
        .ok_or_else(|| anyhow!("unexpected end of input"))?;

    if tok == "(" {
        *pos += 1;
        let mut items = Vec::new();
        while let Some(next) = tokens.get(*pos) {
            if next == ")" {
                *pos += 1;
                return Ok(SExpr::List(items));
            }
            items.push(parse_sexpr(tokens, pos)?);
        }
        bail!("unterminated list");
    }

    if tok == ")" {
        bail!("unexpected ')'");
    }

    *pos += 1;
    Ok(SExpr::Atom(tok.clone()))
}

pub fn looks_like_surface_metta(input: &str) -> bool {
    let s = input.trim();
    s.starts_with("!(") || s.starts_with('(') || s.starts_with('!')
}

fn parse_c_gint(s: &str) -> Option<i32> {
    let inner = s.strip_prefix("C_GInt(")?.strip_suffix(')')?;
    decode_numeric_token(inner.trim())
}

fn contains_pattern_var(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(a) => is_pattern_var_atom(a),
        SExpr::List(items) => items.iter().any(contains_pattern_var),
    }
}

fn is_pattern_var_atom(s: &str) -> bool {
    s.starts_with('$') && s.len() > 1
}

fn is_space_ident(s: &str) -> bool {
    let Some(rest) = s.strip_prefix('&') else {
        return false;
    };
    !rest.is_empty()
        && rest
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

fn extract_declared_memo_head(target: &SExpr) -> Option<String> {
    match target {
        SExpr::Atom(head) => Some(head.clone()),
        SExpr::List(items) => match items.first() {
            Some(SExpr::Atom(head)) => Some(head.clone()),
            _ => None,
        },
    }
}

fn is_valid_memo_head(head: &str) -> bool {
    !head.is_empty() && !is_pattern_var_atom(head) && !is_space_ident(head)
}

fn pattern_match(pattern: &SExpr, value: &SExpr, env: &mut HashMap<String, SExpr>) -> bool {
    match (pattern, value) {
        (SExpr::Atom(v), val) if is_pattern_var_atom(v) => {
            if let Some(bound) = env.get(v) {
                bound == val
            } else {
                env.insert(v.clone(), val.clone());
                true
            }
        },
        (SExpr::Atom(a), SExpr::Atom(b)) => a == b,
        (SExpr::List(pa), SExpr::List(va)) => {
            pa.len() == va.len() && pa.iter().zip(va).all(|(p, v)| pattern_match(p, v, env))
        },
        _ => false,
    }
}

fn pattern_subst(expr: &SExpr, env: &HashMap<String, SExpr>) -> SExpr {
    match expr {
        SExpr::Atom(a) if is_pattern_var_atom(a) => env
            .get(a)
            .cloned()
            .unwrap_or_else(|| SExpr::Atom(a.clone())),
        SExpr::Atom(a) => SExpr::Atom(a.clone()),
        SExpr::List(items) => SExpr::List(items.iter().map(|it| pattern_subst(it, env)).collect()),
    }
}

fn rewrite_protected_builtin(expr: &SExpr) -> bool {
    let SExpr::List(items) = expr else {
        return false;
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return false;
    };
    matches!(head.as_str(), "unify" | "match" | "type-check" | "cast")
}

fn is_ground_call_expr(expr: &SExpr) -> bool {
    let SExpr::List(items) = expr else {
        return false;
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return false;
    };
    if is_pattern_var_atom(head) || is_non_memoized_surface_head(head) {
        return false;
    }
    !contains_pattern_var(expr)
}

fn expr_head_atom(expr: &SExpr) -> Option<&str> {
    let SExpr::List(items) = expr else {
        return None;
    };
    let SExpr::Atom(head) = items.first()? else {
        return None;
    };
    Some(head.as_str())
}

fn contains_non_atom_list_head(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(_) => false,
        SExpr::List(items) => {
            let head_bad = matches!(items.first(), Some(SExpr::List(_)));
            head_bad || items.iter().any(contains_non_atom_list_head)
        },
    }
}

fn contains_pattern_var_head(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(_) => false,
        SExpr::List(items) => {
            let head_bad =
                matches!(items.first(), Some(SExpr::Atom(head)) if is_pattern_var_atom(head));
            head_bad || items.iter().any(contains_pattern_var_head)
        },
    }
}

fn is_core_fast_path_unsafe_head(head: &str) -> bool {
    matches!(
        head,
        "add-atom!"
            | "add-atom"
            | "remove-atom!"
            | "remove-atom"
            | "new-space!"
            | "new-space"
            | "declare-memoized!"
            | "declare-memoized"
            | "in-space"
            | "println!"
            | "match"
            | "unify"
            | "type-check"
            | "cast"
    )
}

fn contains_core_fast_path_unsafe_head(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(_) => false,
        SExpr::List(items) => {
            let head_unsafe = matches!(items.first(), Some(SExpr::Atom(head)) if is_core_fast_path_unsafe_head(head));
            head_unsafe || items.iter().any(contains_core_fast_path_unsafe_head)
        },
    }
}

fn is_core_lp_translatable_expr(expr: &SExpr) -> bool {
    !contains_pattern_var_head(expr)
        && !contains_non_atom_list_head(expr)
        && !contains_core_fast_path_unsafe_head(expr)
}

fn is_core_lp_translatable_rule(lhs: &SExpr, rhs: &SExpr) -> bool {
    is_core_lp_translatable_expr(lhs) && is_core_lp_translatable_expr(rhs)
}

fn is_core_ground_eval_candidate(expr: &SExpr, space_state: &SurfaceSpaceState) -> bool {
    is_core_fast_path_eligible::<MeTTaCoreFastPathHooks>(expr, space_state.eq_patterns.iter())
}

fn is_core_builtin_head(head: &str) -> bool {
    matches!(
        head,
        "if" | "not"
            | "and"
            | "or"
            | "xor"
            | "eq-bool"
            | "+"
            | "add"
            | "-"
            | "sub"
            | "*"
            | "mul"
            | "/"
            | "%"
            | "div"
            | "mod"
            | "modop"
            | "modOp"
            | "<"
            | "lt"
            | "<="
            | "le"
            | ">"
            | "gt"
            | ">="
            | "ge"
            | "=="
            | "eq-int"
            | "concat"
            | "length"
    )
}

fn is_core_builtin_mixed_candidate(expr: &SExpr, space_state: &SurfaceSpaceState) -> bool {
    if contains_pattern_var(expr)
        || !expr_fragment_safe::<MeTTaCoreFastPathHooks>(expr, RuleFragment::CoreGroundEval)
    {
        return false;
    }
    let SExpr::List(items) = expr else {
        return false;
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return false;
    };
    if !is_core_builtin_head(head) {
        return false;
    }
    items.iter().skip(1).all(|item| match item {
        SExpr::Atom(_) => true,
        SExpr::List(_) => {
            is_core_builtin_mixed_candidate(item, space_state)
                || is_core_ground_eval_candidate(item, space_state)
        },
    })
}

fn contains_core_ground_eval_subexpr(expr: &SExpr, space_state: &SurfaceSpaceState) -> bool {
    match expr {
        SExpr::Atom(_) => false,
        SExpr::List(items) => {
            is_core_ground_eval_candidate(expr, space_state)
                || is_core_builtin_mixed_candidate(expr, space_state)
                || items
                    .iter()
                    .any(|item| contains_core_ground_eval_subexpr(item, space_state))
        },
    }
}

fn is_core_eval_candidate(expr: &SExpr, space_state: &SurfaceSpaceState) -> bool {
    if is_core_ground_eval_candidate(expr, space_state) {
        return true;
    }
    if is_core_builtin_mixed_candidate(expr, space_state) {
        return true;
    }
    if contains_pattern_var(expr)
        || !expr_fragment_safe::<MeTTaCoreFastPathHooks>(expr, RuleFragment::CoreGroundEval)
    {
        return false;
    }
    let SExpr::List(items) = expr else {
        return false;
    };
    items
        .iter()
        .any(|item| contains_core_ground_eval_subexpr(item, space_state))
}

fn is_non_memoized_surface_head(head: &str) -> bool {
    matches!(
        head,
        "if" | "match"
            | "unify"
            | "type-check"
            | "cast"
            | "not"
            | "and"
            | "or"
            | "xor"
            | "eq-bool"
            | "+"
            | "-"
            | "*"
            | "/"
            | "%"
            | "div"
            | "mod"
            | "modOp"
            | "<"
            | "<="
            | ">"
            | ">="
            | "=="
            | "concat"
            | "length"
            | "println!"
            | "add-atom!"
            | "add-atom"
            | "remove-atom!"
            | "remove-atom"
            | "new-space!"
            | "new-space"
            | "declare-memoized!"
            | "declare-memoized"
            | "in-space"
    )
}

fn parse_int_atom(a: &str) -> Option<i32> {
    a.parse::<i32>().ok()
}

fn is_ground_int_token(encoded: &str) -> bool {
    encoded.starts_with("C_GInt(") && encoded.ends_with(')')
}

fn is_ground_bool_token(encoded: &str) -> bool {
    matches!(encoded, "C_GBoolTrue" | "C_GBoolFalse")
}

fn bool_literal_atom(expr: &SExpr) -> Option<bool> {
    match expr {
        SExpr::Atom(a) if a.eq_ignore_ascii_case("true") => Some(true),
        SExpr::Atom(a) if a.eq_ignore_ascii_case("false") => Some(false),
        _ => None,
    }
}

fn bool_atom(v: bool) -> SExpr {
    if v {
        SExpr::Atom("true".to_string())
    } else {
        SExpr::Atom("false".to_string())
    }
}

fn eval_ground_expr(expr: &SExpr) -> Option<SExpr> {
    let SExpr::List(items) = expr else {
        return None;
    };
    let Some(SExpr::Atom(op)) = items.first() else {
        return None;
    };

    match (op.as_str(), items.len()) {
        ("if", 4) => match eval_ground_expr_or_self(&items[1])? {
            SExpr::Atom(b) if b.eq_ignore_ascii_case("true") => {
                Some(eval_ground_expr_or_self(&items[2])?)
            },
            SExpr::Atom(b) if b.eq_ignore_ascii_case("false") => {
                Some(eval_ground_expr_or_self(&items[3])?)
            },
            _ => None,
        },
        ("not", 2) => match eval_ground_expr_or_self(&items[1])? {
            SExpr::Atom(b) if b.eq_ignore_ascii_case("true") => Some(bool_atom(false)),
            SExpr::Atom(b) if b.eq_ignore_ascii_case("false") => Some(bool_atom(true)),
            _ => None,
        },
        ("and", 3) | ("or", 3) | ("xor", 3) | ("eq-bool", 3) => {
            let lhs = eval_ground_expr_or_self(&items[1])?;
            let rhs = eval_ground_expr_or_self(&items[2])?;
            let (SExpr::Atom(lb), SExpr::Atom(rb)) = (lhs, rhs) else {
                return None;
            };
            let lv = match lb.to_ascii_lowercase().as_str() {
                "true" => true,
                "false" => false,
                _ => return None,
            };
            let rv = match rb.to_ascii_lowercase().as_str() {
                "true" => true,
                "false" => false,
                _ => return None,
            };
            let out = match op.as_str() {
                "and" => lv && rv,
                "or" => lv || rv,
                "xor" => lv ^ rv,
                "eq-bool" => lv == rv,
                _ => return None,
            };
            Some(bool_atom(out))
        },
        ("+", 3) | ("-", 3) | ("*", 3) | ("<", 3) | ("==", 3) => {
            let lhs = eval_ground_expr_or_self(&items[1])?;
            let rhs = eval_ground_expr_or_self(&items[2])?;
            let (SExpr::Atom(la), SExpr::Atom(ra)) = (lhs, rhs) else {
                return None;
            };
            let (Some(ln), Some(rn)) = (parse_int_atom(&la), parse_int_atom(&ra)) else {
                return None;
            };
            match op.as_str() {
                "+" => ln.checked_add(rn).map(|n| SExpr::Atom(n.to_string())),
                "-" => ln.checked_sub(rn).map(|n| SExpr::Atom(n.to_string())),
                "*" => ln.checked_mul(rn).map(|n| SExpr::Atom(n.to_string())),
                "<" => Some(bool_atom(ln < rn)),
                "==" => Some(bool_atom(ln == rn)),
                _ => None,
            }
        },
        _ => None,
    }
}

fn eval_ground_expr_or_self(expr: &SExpr) -> Option<SExpr> {
    eval_ground_expr(expr).or_else(|| match expr {
        SExpr::Atom(_) => Some(expr.clone()),
        _ => None,
    })
}

pub fn extract_state_out_atom(core_state_term: &str) -> Option<String> {
    let trimmed = core_state_term.trim();
    if !(trimmed.starts_with("C_State(") && trimmed.ends_with(')')) {
        return None;
    }
    let inner = &trimmed["C_State(".len()..trimmed.len() - 1];
    let args = split_top_level_args(inner);
    if args.len() == 3 {
        Some(args[2].trim().to_string())
    } else {
        None
    }
}

/// Encode a string as C_GStringCodes(C_ACons(c1,C_ACons(c2,...,C_ANil)))
/// where c1, c2, ... are Unicode codepoints (matching Lean's codeTokensOfString).
fn encode_gstringcodes(s: &str) -> String {
    let mut acc = "C_ANil".to_string();
    for ch in s.chars().rev() {
        let tok = encode_nonneg_token(ch as u32);
        acc = format!("C_ACons({tok},{acc})");
    }
    format!("C_GStringCodes({acc})")
}

/// Decode C_GStringCodes(C_ACons(N1,C_ACons(N2,...,C_ANil))) back to a string.
/// Each N is a decimal Unicode codepoint token.
fn try_decode_gstringcodes(atom: &str) -> Option<String> {
    let inner = atom.strip_prefix("C_GStringCodes(")?.strip_suffix(')')?;
    let mut chars = Vec::new();
    let mut cur = inner.trim().to_string();
    loop {
        let cur_trim = cur.trim();
        if cur_trim == "C_ANil" {
            return Some(String::from_iter(chars));
        }
        let cons_inner = cur_trim.strip_prefix("C_ACons(")?.strip_suffix(')')?;
        let args = split_top_level_args(cons_inner);
        if args.len() != 2 {
            return None;
        }
        let code = decode_code_token(args[0].trim())?;
        chars.push(char::from_u32(code)?);
        cur = args[1].trim().to_string();
    }
}

fn format_c_gint(n: i32) -> String {
    format!("C_GInt({})", encode_i32_token(n))
}

fn encode_i32_token(n: i32) -> String {
    if n < 0 {
        format!("C_neg_{}", n.unsigned_abs())
    } else {
        format!("C_{n}")
    }
}

fn encode_nonneg_token(n: u32) -> String {
    format!("C_{n}")
}

fn parse_quoted_string_literal(symbol: &str) -> Option<String> {
    if symbol.len() < 2 || !symbol.starts_with('"') || !symbol.ends_with('"') {
        return None;
    }
    let mut decoded = String::new();
    let mut chars = symbol[1..symbol.len() - 1].chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            decoded.push(ch);
            continue;
        }
        let esc = chars.next()?;
        match esc {
            '\\' => decoded.push('\\'),
            '"' => decoded.push('"'),
            'n' => decoded.push('\n'),
            't' => decoded.push('\t'),
            'r' => decoded.push('\r'),
            'u' => {
                if chars.next()? != '{' {
                    return None;
                }
                let mut hex = String::new();
                loop {
                    let c = chars.next()?;
                    if c == '}' {
                        break;
                    }
                    hex.push(c);
                }
                let code = u32::from_str_radix(&hex, 16).ok()?;
                decoded.push(char::from_u32(code)?);
            },
            other => decoded.push(other),
        }
    }
    Some(decoded)
}

fn quote_surface_string(s: &str) -> String {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn decode_numeric_token(tok: &str) -> Option<i32> {
    if let Some(rest) = tok.strip_prefix("C_neg_") {
        let mag = rest.parse::<u32>().ok()?;
        i32::try_from(mag).ok().map(|m| -m)
    } else if let Some(rest) = tok.strip_prefix("C_") {
        rest.parse::<i32>().ok()
    } else {
        tok.parse::<i32>().ok()
    }
}

fn decode_code_token(tok: &str) -> Option<u32> {
    if let Some(rest) = tok.strip_prefix("C_") {
        rest.parse::<u32>().ok()
    } else {
        tok.parse::<u32>().ok()
    }
}

fn split_top_level_args(s: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                args.push(s[start..i].trim().to_string());
                start = i + 1;
            },
            _ => {},
        }
    }
    if start < s.len() {
        args.push(s[start..].trim().to_string());
    }
    args
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax_spec::{
        CommandHead, DispatchPolicy, EvalPrefixPolicy, LexerSpec, LoweringHeads, SyntaxSpec,
    };
    use crate::test_env::acquire_env_lock;
    use mettail_languages::mettafull_legacy::MeTTaFullStateLanguage;
    use mettail_runtime::Language;
    use std::fs;

    fn assert_any_term_contains(terms: &[String], needle: &str, message: &str) {
        assert!(terms.iter().any(|t| t.contains(needle)), "{}: {:?}", message, terms);
    }

    fn assert_any_term_contains_any(terms: &[String], needles: &[&str], message: &str) {
        assert!(
            terms.iter().any(|t| needles.iter().any(|n| t.contains(n))),
            "{}: {:?}",
            message,
            terms
        );
    }

    fn run_surface_core_terms(core_terms: &[String]) -> Vec<String> {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaFullStateLanguage;
        let mut displays = Vec::new();
        for term in core_terms {
            let parsed = lang
                .parse_term(term)
                .expect("surface core term should parse");
            let results = lang
                .run_ascent(parsed.as_ref())
                .expect("Ascent should execute for lowered surface term");
            for item in &results.all_terms {
                displays.push(item.display.clone());
            }
        }
        displays
    }

    fn make_test_syntax_spec(command_heads: Vec<CommandHead>) -> SyntaxSpec {
        SyntaxSpec {
            schema_version: 2,
            dialect: "TestDialect".to_string(),
            lexer: LexerSpec {
                line_comment_start: Some(";".to_string()),
                supports_string_literals: true,
                string_delimiter: "\"".to_string(),
                escape_char: "\\".to_string(),
                sexpr_open: "(".to_string(),
                sexpr_close: ")".to_string(),
                allow_hash_in_symbol: true,
                reserve_hash_in_variable: true,
                trim_ascii_whitespace: true,
            },
            eval_prefix: EvalPrefixPolicy {
                prefix: "!".to_string(),
                allow_whitespace_after_prefix: true,
                allow_newline_after_prefix: true,
                bang_prefixed_word_is_symbol: false,
            },
            lowering_heads: LoweringHeads::default(),
            dispatch_policy: DispatchPolicy::default(),
            command_heads,
            head_aliases: vec![],
            eval_space_aliases: vec![],
            predicate_special_heads: vec![],
        }
    }

    fn policy_from_spec(spec: &SyntaxSpec) -> SurfaceSyntaxPolicy {
        if spec.eval_prefix.bang_prefixed_word_is_symbol {
            SurfaceSyntaxPolicy::HyperonCompat
        } else {
            SurfaceSyntaxPolicy::Strict
        }
    }

    fn load_real_syntax_spec(dialect: &str) -> SyntaxSpec {
        let loaded = try_load_syntax_spec(dialect)
            .expect("syntax spec load should not fail")
            .expect("syntax spec should be present in artifacts");
        loaded.spec
    }

    fn fixture_path(path: &str) -> String {
        let direct = std::path::PathBuf::from(path);
        if direct.exists() {
            return direct.display().to_string();
        }
        let from_manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        if from_manifest.exists() {
            return from_manifest.display().to_string();
        }
        let from_manifest_parent = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join(path);
        from_manifest_parent.display().to_string()
    }

    fn coalesced_forms(path: &str) -> Vec<String> {
        let resolved = fixture_path(path);
        let content = fs::read_to_string(&resolved).expect("fixture file should be readable");
        let forms =
            crate::run_metta_file::coalesce_source_forms(&content, &resolved, DEFAULT_SPACE_IDENT)
                .expect("coalesce should succeed");
        forms
            .into_iter()
            .map(|entry| entry.text.trim().to_string())
            .filter(|line| !line.is_empty())
            .collect()
    }

    fn assert_backend_parity_for_forms(spec: &SyntaxSpec, forms: &[String], label: &str) {
        let policy = policy_from_spec(spec);
        for input in forms {
            let legacy =
                MeTTaSurfaceSession::parse_line_with_legacy_syntax(input, policy, Some(spec));
            let tree = MeTTaSurfaceSession::parse_line_with_tree_sitter(
                input,
                policy,
                Some(spec),
                SurfaceProfile::HE,
            );
            match (legacy, tree) {
                (Ok(left), Ok(right)) => {
                    assert_eq!(left, right, "backend mismatch for {label} input: {input}");
                },
                (Err(_), Err(_)) => {},
                (left, right) => panic!(
                    "backend mismatch for {label} input: {input}; legacy={left:?} tree={right:?}"
                ),
            }
        }
    }

    fn assert_backend_parity_for_negative_cases(spec: &SyntaxSpec, label: &str, cases: &[&str]) {
        let policy = policy_from_spec(spec);
        for input in cases {
            let legacy =
                MeTTaSurfaceSession::parse_line_with_legacy_syntax(input, policy, Some(spec));
            let tree = MeTTaSurfaceSession::parse_line_with_tree_sitter(
                input,
                policy,
                Some(spec),
                SurfaceProfile::HE,
            );
            assert_eq!(
                legacy.is_err(),
                tree.is_err(),
                "negative-case parse mismatch for {label} input: {input}; legacy={legacy:?} tree={tree:?}"
            );
        }
    }

    #[test]
    fn parse_eq_definition() {
        let stmt = MeTTaSurfaceSession::parse_line("(= (foo true) false)").expect("should parse");
        match stmt {
            SurfaceStmt::DefineEq(_, _) => {},
            _ => panic!("expected DefineEq"),
        }
    }

    #[test]
    fn parse_bang_eval() {
        let stmt = MeTTaSurfaceSession::parse_line("!(and true false)").expect("should parse");
        match stmt {
            SurfaceStmt::Eval(_) => {},
            _ => panic!("expected Eval"),
        }
    }

    #[test]
    fn parse_standalone_bang_hyperon_compat_is_noop() {
        let parsed =
            MeTTaSurfaceSession::parse_line_with_policy("!", SurfaceSyntaxPolicy::HyperonCompat)
                .expect("compat parse should succeed");
        assert!(parsed.is_none(), "standalone bang should be a no-op in compat mode");
    }

    #[test]
    fn parse_standalone_bang_strict_is_error() {
        let parsed = MeTTaSurfaceSession::parse_line_with_policy("!", SurfaceSyntaxPolicy::Strict);
        assert!(parsed.is_err(), "standalone bang should error in strict mode");
    }

    #[test]
    fn he_profile_defaults_to_hyperon_compat() {
        let session = MeTTaSurfaceSession::with_profile(SurfaceProfile::HE);
        assert_eq!(session.syntax_policy(), SurfaceSyntaxPolicy::HyperonCompat);
    }

    #[test]
    fn he_profile_defaults_to_legacy_parser_backend() {
        let _guard = acquire_env_lock();
        std::env::remove_var("METTAIL_PARSER_BACKEND");
        let session = MeTTaSurfaceSession::with_profile(SurfaceProfile::HE);
        assert_eq!(session.parser_backend(), SurfaceParserBackend::LegacySExpr);
    }

    #[test]
    fn env_can_select_tree_sitter_parser_backend() {
        let _guard = acquire_env_lock();
        std::env::set_var("METTAIL_PARSER_BACKEND", "tree-sitter");
        let session = MeTTaSurfaceSession::with_profile(SurfaceProfile::HE);
        std::env::remove_var("METTAIL_PARSER_BACKEND");
        assert_eq!(session.parser_backend(), SurfaceParserBackend::TreeSitter);
    }

    #[test]
    fn tree_sitter_backend_matches_legacy_parser_for_core_forms() {
        let he_spec = load_real_syntax_spec("he");
        let cases = [
            "(= (double $x) (+ $x $x))",
            "!(+ 1 2)",
            "!(match &self (= (color) $x) $x)",
            "(: Add (-> Nat Nat Nat))",
        ];

        for input in cases {
            let legacy = MeTTaSurfaceSession::parse_line_with_legacy_syntax(
                input,
                SurfaceSyntaxPolicy::HyperonCompat,
                Some(&he_spec),
            )
            .expect("legacy parse should succeed");
            let tree = MeTTaSurfaceSession::parse_line_with_tree_sitter(
                input,
                SurfaceSyntaxPolicy::HyperonCompat,
                Some(&he_spec),
                SurfaceProfile::HE,
            )
            .expect("tree-sitter parse should succeed");
            assert_eq!(
                tree, legacy,
                "embedded tree-sitter parse should match legacy parse for input: {input}"
            );
        }
    }

    #[test]
    fn he_profile_requires_syntax_spec_when_missing() {
        let _guard = acquire_env_lock();
        let dir = format!(".artifacts/test-runtime/missing_he_spec_{}", std::process::id());
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        std::env::set_var("METTAIL_SYNTAX_SPEC_DIR", &dir);
        let session = MeTTaSurfaceSession::with_profile(SurfaceProfile::HE);
        let err = session
            .parse_line_for_session("!(foo)")
            .expect_err("HE parse should fail when syntax spec is missing");
        assert!(
            err.to_string()
                .contains("surface syntax spec required for HE profile"),
            "unexpected error: {err}"
        );
        std::env::remove_var("METTAIL_SYNTAX_SPEC_DIR");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn he_profile_requires_lookup_plan_when_missing() {
        let _guard = acquire_env_lock();
        let lookup_dir =
            format!(".artifacts/test-runtime/missing_he_lookup_plan_{}", std::process::id());
        fs::create_dir_all(&lookup_dir).expect("artifact dir should be creatable");

        let syntax_dir =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/syntax");
        std::env::set_var("METTAIL_SYNTAX_SPEC_DIR", &syntax_dir);
        std::env::set_var("METTAIL_LOOKUP_PLAN_DIR", &lookup_dir);

        let session = MeTTaSurfaceSession::with_profile(SurfaceProfile::HE);
        let err = session
            .parse_line_for_session("!(foo)")
            .expect_err("HE parse should fail when lookup plan is missing");
        assert!(
            err.to_string()
                .contains("lookup-plan artifacts are required for HE profile"),
            "unexpected error: {err}"
        );

        std::env::remove_var("METTAIL_SYNTAX_SPEC_DIR");
        std::env::remove_var("METTAIL_LOOKUP_PLAN_DIR");
        let _ = fs::remove_dir_all(&lookup_dir);
    }

    #[test]
    fn backend_parity_he_fixture_file() {
        let he_spec = load_real_syntax_spec("he");
        let forms = coalesced_forms("repl/src/examples/petta_adapted/he_minimalmetta.metta");
        assert!(!forms.is_empty(), "fixture should provide parse inputs");
        assert_backend_parity_for_forms(&he_spec, &forms, "he_minimalmetta");
    }

    #[test]
    fn backend_parity_petta_fixture_file() {
        let petta_spec = load_real_syntax_spec("petta");
        let forms = coalesced_forms("repl/src/examples/petta_adapted/comments.metta");
        assert!(!forms.is_empty(), "fixture should provide parse inputs");
        assert_backend_parity_for_forms(&petta_spec, &forms, "petta_comments");
    }

    #[test]
    fn backend_parity_negative_cases_he_and_petta() {
        let he_spec = load_real_syntax_spec("he");
        let petta_spec = load_real_syntax_spec("petta");
        let cases = ["(= (foo bar)", "!((", "!(foo))"];
        assert_backend_parity_for_negative_cases(&he_spec, "he", &cases);
        assert_backend_parity_for_negative_cases(&petta_spec, "petta", &cases);
    }

    #[test]
    fn parse_uses_syntax_spec_command_heads_for_define_eq() {
        let spec = make_test_syntax_spec(vec![CommandHead {
            head: "eqdef".to_string(),
            command: "defineEq".to_string(),
            arity_min: 2,
            arity_max: Some(2),
        }]);
        let parsed = MeTTaSurfaceSession::parse_line_with_legacy_syntax(
            "(eqdef foo bar)",
            SurfaceSyntaxPolicy::Strict,
            Some(&spec),
        )
        .expect("parse should succeed")
        .expect("statement should be produced");
        assert!(matches!(parsed, SurfaceStmt::DefineEq(_, _)));
    }

    #[test]
    fn lowering_match_maps_to_unify() {
        let mut session = MeTTaSurfaceSession::new();
        let stmt = MeTTaSurfaceSession::parse_line("!(match foo foo)").expect("parse");
        let out = session.apply_stmt(stmt).expect("lower");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains(
                    &core_terms,
                    "C_Match(C_UserAtom(C_GStringCodes(C_ACons(C_102,C_ACons(C_111,C_ACons(C_111,C_ANil))))),C_UserAtom(C_GStringCodes(C_ACons(C_102,C_ACons(C_111,C_ACons(C_111,C_ANil))))))",
                    "surface match should lower to C_Match",
                );
            },
            _ => panic!("expected Eval"),
        }
    }

    #[test]
    fn parse_mutable_space_ops() {
        let add = MeTTaSurfaceSession::parse_line("(add-atom! (= foo true))").expect("parse add");
        assert!(matches!(
            add,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&self"
        ));

        let remove =
            MeTTaSurfaceSession::parse_line("(remove-atom! (= foo true))").expect("parse remove");
        assert!(matches!(
            remove,
            SurfaceStmt::RemoveAtom { ref space, .. } if space == "&self"
        ));

        let new_space = MeTTaSurfaceSession::parse_line("(new-space!)").expect("parse new-space");
        assert!(matches!(
            new_space,
            SurfaceStmt::NewSpace { ref space } if space == "&self"
        ));
    }

    #[test]
    fn parse_declare_memoized_ops() {
        let decl =
            MeTTaSurfaceSession::parse_line("(declare-memoized! fib)").expect("parse declaration");
        assert!(matches!(
            decl,
            SurfaceStmt::DeclareMemoized { ref space, ref head }
                if space == "&self" && head == "fib"
        ));

        let decl_tmp = MeTTaSurfaceSession::parse_line("!(declare-memoized! &tmp (fib $n))")
            .expect("parse scoped declaration");
        assert!(matches!(
            decl_tmp,
            SurfaceStmt::DeclareMemoized { ref space, ref head }
                if space == "&tmp" && head == "fib"
        ));
    }

    #[test]
    fn parse_he_style_space_mutations() {
        let add =
            MeTTaSurfaceSession::parse_line("!(add-atom! &self (= foo true))").expect("parse add");
        assert!(matches!(
            add,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&self"
        ));

        let add_tmp = MeTTaSurfaceSession::parse_line("!(add-atom! &tmp (: foo Bool))")
            .expect("parse add tmp");
        assert!(matches!(
            add_tmp,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&tmp"
        ));

        let reset_default = MeTTaSurfaceSession::parse_line("!(new-space)").expect("parse reset");
        assert!(matches!(
            reset_default,
            SurfaceStmt::NewSpace { ref space } if space == "&self"
        ));

        let reset_tmp =
            MeTTaSurfaceSession::parse_line("(new-space! &tmp)").expect("parse reset tmp");
        assert!(matches!(
            reset_tmp,
            SurfaceStmt::NewSpace { ref space } if space == "&tmp"
        ));
    }

    #[test]
    fn parse_new_space_handle_allocation() {
        let stmt = MeTTaSurfaceSession::parse_line("!(new-space!)").expect("parse alloc");
        assert!(matches!(stmt, SurfaceStmt::AllocSpace));
    }

    #[test]
    fn parse_eval_in_space_wrapper() {
        let stmt = MeTTaSurfaceSession::parse_line("!(in-space &tmp (type-check foo Bool))")
            .expect("parse");
        assert!(matches!(
            stmt,
            SurfaceStmt::EvalIn { ref space, .. } if space == "&tmp"
        ));
    }

    #[test]
    fn parse_eval_space_aliases() {
        let m = MeTTaSurfaceSession::parse_line("!(match &tmp foo foo)").expect("parse match");
        assert!(matches!(
            m,
            SurfaceStmt::EvalIn { ref space, .. } if space == "&tmp"
        ));

        let tc = MeTTaSurfaceSession::parse_line("!(type-check &tmp foo Bool)")
            .expect("parse type-check");
        assert!(matches!(
            tc,
            SurfaceStmt::EvalIn { ref space, .. } if space == "&tmp"
        ));
    }

    #[test]
    fn parse_in_space_mutation_wrappers() {
        let add = MeTTaSurfaceSession::parse_line("!(in-space &tmp (add-atom! (= foo true)))")
            .expect("parse in-space add");
        assert!(matches!(
            add,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&tmp"
        ));

        let remove =
            MeTTaSurfaceSession::parse_line("!(in-space &tmp (remove-atom! (= foo true)))")
                .expect("parse in-space remove");
        assert!(matches!(
            remove,
            SurfaceStmt::RemoveAtom { ref space, .. } if space == "&tmp"
        ));

        let reset =
            MeTTaSurfaceSession::parse_line("!(in-space &tmp (new-space!))").expect("parse reset");
        assert!(matches!(
            reset,
            SurfaceStmt::NewSpace { ref space } if space == "&tmp"
        ));

        let eq_stmt =
            MeTTaSurfaceSession::parse_line("!(in-space &tmp (= foo true))").expect("parse eq");
        assert!(matches!(
            eq_stmt,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&tmp"
        ));

        let ty_stmt =
            MeTTaSurfaceSession::parse_line("!(in-space &tmp (: foo Bool))").expect("parse type");
        assert!(matches!(
            ty_stmt,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&tmp"
        ));
    }

    #[test]
    fn parse_in_space_mutation_retargets_inner_self() {
        let add =
            MeTTaSurfaceSession::parse_line("!(in-space &tmp (add-atom! &self (= foo true)))")
                .expect("parse add");
        assert!(matches!(
            add,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&tmp"
        ));

        let add_other =
            MeTTaSurfaceSession::parse_line("!(in-space &tmp (add-atom! &other (= foo true)))")
                .expect("parse add other");
        assert!(matches!(
            add_other,
            SurfaceStmt::AddAtom { ref space, .. } if space == "&other"
        ));
    }

    #[test]
    fn lowering_grounded_and() {
        let mut session = MeTTaSurfaceSession::new();
        let stmt = MeTTaSurfaceSession::parse_line("!(and true false)").expect("parse");
        let out = session.apply_stmt(stmt).expect("lower");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_Grounded2(C_and,C_GBoolTrue,C_GBoolFalse)", "C_Eval(C_GBoolFalse)"],
                    "unexpected core term",
                );
            },
            _ => panic!("expected Eval"),
        }
    }

    #[test]
    fn mutation_persists_into_eval_space() {
        let mut session = MeTTaSurfaceSession::new();
        let def = MeTTaSurfaceSession::parse_line("(= foo true)").expect("parse def");
        let _ = session.apply_stmt(def).expect("apply def");

        let eval = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains(
                    &core_terms,
                    "C_AEqEntry",
                    "expected encoded eq entries in eval state",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn extract_out_atom_from_state_term() {
        let term = "C_State(C_Done,C_Space(C_ANil,C_ANil),C_GBoolTrue)";
        let out = extract_state_out_atom(term).expect("should extract");
        assert_eq!(out, "C_GBoolTrue");
    }

    #[test]
    fn decode_known_atoms() {
        let session = MeTTaSurfaceSession::new();
        assert_eq!(session.decode_atom_to_surface("C_GBoolFalse"), "false");
        assert_eq!(session.decode_atom_to_surface("C_ATrue"), "true");
        assert_eq!(session.decode_atom_to_surface("C_GInt(C_42)"), "42");
        assert_eq!(session.decode_atom_to_surface("C_GInt(C_neg_9)"), "-9");
        assert_eq!(session.decode_atom_to_surface("C_div"), "/");
        assert_eq!(session.decode_atom_to_surface("C_add"), "+");
        assert_eq!(session.decode_atom_to_surface("C_eqInt"), "==");
        // UserAtom: symbol "foo" = UserAtom(GStringCodes(f=102, o=111, o=111))
        assert_eq!(
            session.decode_atom_to_surface(
                "C_UserAtom(C_GStringCodes(C_ACons(C_102,C_ACons(C_111,C_ACons(C_111,C_ANil)))))"
            ),
            "foo"
        );
        // Bare GStringCodes: string literal (no UserAtom wrapper)
        assert_eq!(
            session.decode_atom_to_surface(
                "C_GStringCodes(C_ACons(C_102,C_ACons(C_111,C_ACons(C_111,C_ANil))))"
            ),
            "\"foo\""
        );
        // GString: logic-block outputs (e.g., concat result)
        assert_eq!(session.decode_atom_to_surface("C_GString(hello)"), "\"hello\"");
    }

    #[test]
    fn decode_cons_list_atoms() {
        let session = MeTTaSurfaceSession::new();
        assert_eq!(
            session.decode_atom_to_surface("C_ACons(C_ATrue,C_ACons(C_AFalse,C_ANil))"),
            "(true false)"
        );
        assert_eq!(session.decode_atom_to_surface("C_ACons(C_ATrue,C_AFalse)"), "(true . false)");
    }

    #[test]
    fn lowering_arith_and_if_surface_forms() {
        let mut session = MeTTaSurfaceSession::new();
        let arith = MeTTaSurfaceSession::parse_line("!(+ 1 (* 2 3))").expect("parse arith");
        let out = session.apply_stmt(arith).expect("apply arith");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_Grounded2(C_add,C_GInt(C_1),C_GInt(C_6))", "C_Eval(C_GInt(C_7))"],
                    "unexpected arithmetic lowering",
                );
            },
            _ => panic!("expected eval"),
        }

        let if_stmt = MeTTaSurfaceSession::parse_line("!(if (< 1 2) 7 9)").expect("parse if");
        let out = session.apply_stmt(if_stmt).expect("apply if");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_If(C_GBoolTrue,C_GInt(C_7),C_GInt(C_9))", "C_Eval(C_GInt(C_7))"],
                    "unexpected if lowering",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn pattern_rule_rewrites_to_ground_eval() {
        let mut session = MeTTaSurfaceSession::new();
        let def = MeTTaSurfaceSession::parse_line("(= (inc $x) (+ $x 1))").expect("parse");
        let _ = session.apply_stmt(def).expect("apply");

        let eval = MeTTaSurfaceSession::parse_line("!(inc 4)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_Grounded2(C_add,C_GInt(C_4),C_GInt(C_1))", "C_Eval(C_GInt(C_5))"],
                    "pattern rewrite missing in lowered term",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn recursive_pattern_rewrite_on_subterms() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (id $x) $x)").expect("parse"))
            .expect("apply");
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(= (twice $x) (+ (id $x) (id $x)))")
                    .expect("parse"),
            )
            .expect("apply");

        let eval = MeTTaSurfaceSession::parse_line("!(twice 5)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_Grounded2(C_add,C_GInt(C_5),C_GInt(C_5))", "C_Eval(C_GInt(C_10))"],
                    "recursive rewrite did not normalize subterms",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn recursive_memo_hits_for_repeated_ground_calls() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_recursive_memo_enabled(true);
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (id $x) $x)").expect("parse"))
            .expect("apply");
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(= (twice-id $x) (+ (id $x) (id $x)))")
                    .expect("parse"),
            )
            .expect("apply");

        let eval = MeTTaSurfaceSession::parse_line("!(twice-id 5)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_Grounded2(C_add,C_GInt(C_5),C_GInt(C_5))", "C_Eval(C_GInt(C_10))"],
                    "twice-id rewrite should reduce to ground add",
                );
            },
            _ => panic!("expected eval"),
        }
        let diag = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after eval");
        assert!(
            diag.memo_stores > 0,
            "expected at least one ground-call memo store, got {:?}",
            diag
        );
        let out2 = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(twice-id 5)").expect("parse eval"))
            .expect("apply eval");
        match out2 {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains_any(
                    &core_terms,
                    &["C_Grounded2(C_add,C_GInt(C_5),C_GInt(C_5))", "C_Eval(C_GInt(C_10))"],
                    "twice-id second rewrite should reduce to ground add",
                );
            },
            _ => panic!("expected eval"),
        }
        let diag2 = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after second eval");
        assert!(
            diag2.memo_hits > 0,
            "expected at least one ground-call memo hit on repeated eval, got {:?}",
            diag2
        );
    }

    #[test]
    fn declare_memoized_enables_per_head_caching() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_recursive_memo_enabled(false);
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (id $x) $x)").expect("parse"))
            .expect("apply");
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(= (twice-id $x) (+ (id $x) (id $x)))")
                    .expect("parse"),
            )
            .expect("apply");

        let first = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(twice-id 9)").expect("parse eval"))
            .expect("apply eval");
        assert!(matches!(first, SurfaceOutcome::EvalMany { .. }));
        let first_diag = session
            .last_surface_diagnostics()
            .expect("diag after first eval");
        assert_eq!(first_diag.memo_stores, 0, "memo should be disabled before declaration");

        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(declare-memoized! twice-id)").expect("parse"),
            )
            .expect("declare memoized");
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(twice-id 9)").expect("parse eval"))
            .expect("apply eval");
        let second_diag = session
            .last_surface_diagnostics()
            .expect("diag after second eval");
        assert!(
            second_diag.memo_stores > 0,
            "expected memo store after declaration, got {:?}",
            second_diag
        );

        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(twice-id 9)").expect("parse eval"))
            .expect("apply eval");
        let third_diag = session
            .last_surface_diagnostics()
            .expect("diag after third eval");
        assert!(
            third_diag.memo_hits > 0,
            "expected memo hit after declaration, got {:?}",
            third_diag
        );
    }

    #[test]
    fn recursive_memo_is_enabled_by_default() {
        let session = MeTTaSurfaceSession::new();
        assert!(
            session.recursive_memo_enabled(),
            "ground-call memoization should default to enabled"
        );
        assert!(
            !session.core_ground_eval_enabled(),
            "raw surface sessions should keep core-ground routing off unless explicitly enabled"
        );
    }

    #[test]
    fn core_ground_eval_fast_path_does_not_require_surface_memo() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_core_ground_eval_enabled(true);
        session.set_recursive_memo_enabled(false);
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (id $x) $x)").expect("parse"))
            .expect("apply");

        let out = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(id 7)").expect("parse eval"))
            .expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_eq!(
                    core_terms.len(),
                    1,
                    "core ground-eval fast path should emit a single core C_Eval state"
                );
                assert!(
                    core_terms[0].contains("C_State(C_Eval("),
                    "expected direct C_Eval state from core fast path, got {:?}",
                    core_terms
                );
            },
            _ => panic!("expected eval"),
        }
        let diag = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after eval");
        assert_eq!(
            diag.rewrite_calls, 0,
            "surface rewrite loop should be bypassed by core fast path when enabled"
        );
    }

    #[test]
    fn core_ground_eval_fast_path_rejects_higher_order_rules() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_core_ground_eval_enabled(true);
        session.set_recursive_memo_enabled(false);
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(= (trickyspec $f) (if (== ($f 1) 2) 22 33))")
                    .expect("parse"),
            )
            .expect("apply");

        let out = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(trickyspec noop)").expect("parse eval"))
            .expect("apply eval");
        assert!(matches!(out, SurfaceOutcome::EvalMany { .. }));
        let diag = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after eval");
        assert!(
            diag.rewrite_calls > 0,
            "higher-order rule should stay on surface path, got {:?}",
            diag
        );
    }

    #[test]
    fn core_ground_eval_fast_path_accepts_mixed_ground_expression_with_ground_subcalls() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_core_ground_eval_enabled(true);
        session.set_recursive_memo_enabled(false);
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (id $x) $x)").expect("parse"))
            .expect("apply");

        let out = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(+ (id 2) (id 3))").expect("parse eval"))
            .expect("apply eval");
        assert!(matches!(out, SurfaceOutcome::EvalMany { .. }));
        let diag = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after eval");
        assert_eq!(
            diag.rewrite_calls, 0,
            "mixed ground expression with safe subcalls should route directly to core fast path"
        );
    }

    #[test]
    fn core_ground_eval_fast_path_accepts_pure_builtin_ground_expression() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_core_ground_eval_enabled(true);
        session.set_recursive_memo_enabled(false);

        let out = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(+ 1 (* 2 3))").expect("parse eval"))
            .expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_eq!(core_terms.len(), 1, "expected single core fast-path branch");
                assert!(
                    core_terms[0].contains("C_State(C_Eval("),
                    "expected direct C_Eval state from core fast path, got {:?}",
                    core_terms
                );
            },
            _ => panic!("expected eval"),
        }
        let diag = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after eval");
        assert_eq!(
            diag.rewrite_calls, 0,
            "pure builtin ground expression should bypass surface rewrite loop"
        );
    }

    #[test]
    fn core_ground_eval_fast_path_accepts_non_builtin_outer_with_builtin_mixed_subexpr() {
        let mut session = MeTTaSurfaceSession::new();
        session.set_core_ground_eval_enabled(true);
        session.set_recursive_memo_enabled(false);

        let out = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("!(outer-call (+ 1 (* 2 3)))").expect("parse eval"),
            )
            .expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_eq!(core_terms.len(), 1, "expected single core fast-path branch");
                assert!(
                    core_terms[0].contains("C_State(C_Eval("),
                    "expected direct C_Eval state from core fast path, got {:?}",
                    core_terms
                );
            },
            _ => panic!("expected eval"),
        }
        let diag = session
            .last_surface_diagnostics()
            .expect("surface diagnostics should be present after eval");
        assert_eq!(
            diag.rewrite_calls, 0,
            "mixed builtin subexpression under non-builtin outer head should bypass surface rewrite loop"
        );
    }

    #[test]
    fn rewrite_does_not_enter_typecheck_builtin() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= foo true)").expect("parse"))
            .expect("apply");
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(: foo Bool)").expect("parse"))
            .expect("apply");

        let eval = MeTTaSurfaceSession::parse_line("!(type-check foo Bool)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                // "foo" encoded as UserAtom(GStringCodes(f=102, o=111, o=111))
                assert_any_term_contains(
                    &core_terms,
                    "C_TypeCheck(C_UserAtom(C_GStringCodes(C_ACons(C_102,C_ACons(C_111,C_ACons(C_111,C_ANil))))),C_Bool)",
                    "type-check arguments should use UserAtom encoding",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn recursive_factorial_rewrite_terminates() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (fact 0) 1)").expect("parse"))
            .expect("apply");
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(= (fact $n) (* $n (fact (- $n 1))))")
                    .expect("parse"),
            )
            .expect("apply");

        let eval = MeTTaSurfaceSession::parse_line("!(fact 5)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains(
                    &core_terms,
                    "C_Eval(C_GInt(C_120))",
                    "factorial did not normalize to bounded arithmetic",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn if_rewrite_is_condition_first() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (boom) (boom2))").expect("parse"))
            .expect("apply");

        let expr = SExpr::List(vec![
            SExpr::Atom("if".to_string()),
            SExpr::List(vec![
                SExpr::Atom("<".to_string()),
                SExpr::Atom("3".to_string()),
                SExpr::Atom("2".to_string()),
            ]),
            SExpr::List(vec![SExpr::Atom("boom".to_string())]),
            SExpr::Atom("1".to_string()),
        ]);

        let space_state = session.space_state(DEFAULT_SPACE_IDENT);
        let index = RuleIndex::from_pattern_keys(
            space_state
                .eq_patterns
                .iter()
                .map(|(lhs, _rhs)| pattern_index_key(lhs)),
        );
        let mut rewrite_cache = HashMap::new();
        let mut profile = SurfaceRewriteProfile::default();
        let step1 = session.rewrite_many_once_cached(
            &expr,
            DEFAULT_SPACE_IDENT,
            space_state,
            &index,
            &mut rewrite_cache,
            &mut profile,
        );

        assert_eq!(
            step1,
            vec![SExpr::List(vec![
                SExpr::Atom("if".to_string()),
                SExpr::Atom("false".to_string()),
                SExpr::List(vec![SExpr::Atom("boom".to_string())]),
                SExpr::Atom("1".to_string()),
            ])],
            "expected only condition rewrite on first step"
        );

        let mut rewrite_cache = HashMap::new();
        let mut profile = SurfaceRewriteProfile::default();
        let step2 = session.rewrite_many_once_cached(
            &step1[0],
            DEFAULT_SPACE_IDENT,
            space_state,
            &index,
            &mut rewrite_cache,
            &mut profile,
        );
        assert_eq!(step2, vec![SExpr::Atom("1".to_string())]);
    }

    #[test]
    fn non_ground_add_does_not_lower_to_grounded_call() {
        let mut session = MeTTaSurfaceSession::new();
        let eval = MeTTaSurfaceSession::parse_line("!(+ foo 1)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert!(
                    core_terms.iter().any(|t| t.contains("C_Eval(")),
                    "expected fallback C_Eval lowering for non-ground add"
                );
                assert!(
                    core_terms.iter().all(|t| !t.contains("C_Grounded2(C_add,")),
                    "non-ground add should not lower to C_Grounded2(C_add, ...)"
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn gstringcodes_encode_decode_roundtrip() {
        let test_cases = vec![
            "foo",
            "bar",
            "hello-world",
            "my_var",
            "x",
            "ATrue",
            "GString",
            "C_Atom", // would collide with GString encoding
        ];
        for sym in test_cases {
            let encoded = encode_gstringcodes(sym);
            let decoded = try_decode_gstringcodes(&encoded);
            assert_eq!(
                decoded.as_deref(),
                Some(sym),
                "roundtrip failed for symbol: {sym}, encoded: {encoded}"
            );
        }
    }

    #[test]
    fn gstringcodes_handles_whitespace_and_unicode() {
        // "hi there" contains space (code 32)
        let encoded = encode_gstringcodes("hi there");
        assert!(
            encoded.contains("C_ACons(C_32,"),
            "space char code token C_32 should be present"
        );
        let decoded = try_decode_gstringcodes(&encoded);
        assert_eq!(decoded.as_deref(), Some("hi there"));
    }

    #[test]
    fn decode_strings_are_quoted_and_escaped() {
        let session = MeTTaSurfaceSession::new();
        let encoded = encode_gstringcodes("a\"b\n");
        assert_eq!(session.decode_atom_to_surface(&encoded), "\"a\\\"b\\n\"");
    }

    #[test]
    fn tokenize_and_lower_quoted_string_literals() {
        let mut session = MeTTaSurfaceSession::new();
        let stmt =
            MeTTaSurfaceSession::parse_line("!(println! \"hello world\")").expect("parse println");
        let out = session.apply_stmt(stmt).expect("lower println");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert_any_term_contains(
                    &core_terms,
                    "C_GStringCodes(C_ACons(C_104,",
                    "println lowering should include gstringcodes for quoted literal",
                );
                assert_any_term_contains(
                    &core_terms,
                    "C_32",
                    "quoted literal should preserve embedded whitespace character code",
                );
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn concat_and_length_runtime_with_quoted_strings() {
        let mut session = MeTTaSurfaceSession::new();

        let concat = MeTTaSurfaceSession::parse_line("!(concat \"ab\" \"cd\")").expect("parse");
        let concat_terms = match session.apply_stmt(concat).expect("apply concat") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let concat_displays = run_surface_core_terms(&concat_terms);
        assert!(
            concat_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GString(abcd))")),
            "expected concat return atom, got: {concat_displays:?}"
        );

        let len = MeTTaSurfaceSession::parse_line("!(length \"hello\")").expect("parse");
        let len_terms = match session.apply_stmt(len).expect("apply length") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let len_displays = run_surface_core_terms(&len_terms);
        assert!(
            len_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GInt(C_5))")),
            "expected length return 5, got: {len_displays:?}"
        );
    }

    #[test]
    fn nondeterministic_rewrite_produces_multiple_branches() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (choose $x) $x)").expect("parse"))
            .expect("apply");
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(= (choose $x) (f $x))").expect("parse"))
            .expect("apply");

        let eval = MeTTaSurfaceSession::parse_line("!(choose 1)").expect("parse eval");
        let out = session.apply_stmt(eval).expect("apply eval");
        match out {
            SurfaceOutcome::EvalMany { core_terms } => {
                assert!(core_terms.len() >= 2, "expected multiple branches");
            },
            _ => panic!("expected eval"),
        }
    }

    #[test]
    fn mutable_space_add_remove_eq_affects_runtime_results() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(add-atom! (= foo true))").expect("parse"))
            .expect("apply add");

        let eval_added = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let added_terms = match session.apply_stmt(eval_added).expect("apply eval") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval outcome"),
        };
        let added_displays = run_surface_core_terms(&added_terms);
        assert!(
            added_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "expected foo lookup to return true after add-atom!, got: {added_displays:?}"
        );

        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(remove-atom! (= foo true))").expect("parse"),
            )
            .expect("apply remove");

        let eval_removed = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let removed_terms = match session.apply_stmt(eval_removed).expect("apply eval") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval outcome"),
        };
        let removed_displays = run_surface_core_terms(&removed_terms);
        assert!(
            !removed_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "unexpected true result after remove-atom!: {removed_displays:?}"
        );
    }

    #[test]
    fn mutable_space_new_space_clears_eq_and_types() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(add-atom! (= foo true))").expect("parse"))
            .expect("apply eq add");
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(add-atom! (: foo Bool))").expect("parse"))
            .expect("apply type add");

        let eval_before = MeTTaSurfaceSession::parse_line("!(type-check foo Bool)").expect("parse");
        let before_terms = match session.apply_stmt(eval_before).expect("apply eval") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval outcome"),
        };
        let before_displays = run_surface_core_terms(&before_terms);
        assert!(
            before_displays
                .iter()
                .any(|d| d.contains("C_Return(C_ATrue)")),
            "expected type-check success before new-space!, got: {before_displays:?}"
        );

        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(new-space!)").expect("parse"))
            .expect("apply new-space");

        let eval_after = MeTTaSurfaceSession::parse_line("!(type-check foo Bool)").expect("parse");
        let after_terms = match session.apply_stmt(eval_after).expect("apply eval") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval outcome"),
        };
        let after_displays = run_surface_core_terms(&after_terms);
        assert!(
            after_displays
                .iter()
                .any(|d| d.contains("C_Return(C_AFalse)")),
            "expected type-check failure after new-space!, got: {after_displays:?}"
        );
    }

    #[test]
    fn named_spaces_are_isolated_from_default_space() {
        let mut session = MeTTaSurfaceSession::new();

        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(add-atom! &tmp (= foo true))").expect("parse"),
            )
            .expect("apply tmp add");

        let eval_tmp = MeTTaSurfaceSession::parse_line("!(in-space &tmp foo)").expect("parse");
        let tmp_terms = match session.apply_stmt(eval_tmp).expect("apply tmp eval") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let tmp_displays = run_surface_core_terms(&tmp_terms);
        assert!(
            tmp_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "tmp-space eval should see tmp mutation: {tmp_displays:?}"
        );

        let eval_default_before = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let default_before_terms = match session
            .apply_stmt(eval_default_before)
            .expect("apply default eval before")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let default_before_displays = run_surface_core_terms(&default_before_terms);
        assert!(
            !default_before_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "tmp-space mutation leaked into default space: {default_before_displays:?}"
        );

        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(add-atom! &self (= foo true))").expect("parse"),
            )
            .expect("apply self add");

        let eval_default_after = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let default_after_terms = match session
            .apply_stmt(eval_default_after)
            .expect("apply default eval after")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let default_after_displays = run_surface_core_terms(&default_after_terms);
        assert!(
            default_after_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "default-space mutation missing: {default_after_displays:?}"
        );

        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("(new-space! &tmp)").expect("parse"))
            .expect("apply reset tmp");

        let eval_default_still = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let default_still_terms = match session
            .apply_stmt(eval_default_still)
            .expect("apply default eval still")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let default_still_displays = run_surface_core_terms(&default_still_terms);
        assert!(
            default_still_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "resetting tmp should not clear default space: {default_still_displays:?}"
        );
    }

    #[test]
    fn in_space_mutation_wrapper_executes_in_target_space() {
        let mut session = MeTTaSurfaceSession::new();

        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("!(in-space &tmp (add-atom! (= foo true)))")
                    .expect("parse add"),
            )
            .expect("apply add");

        let tmp_terms = match session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(in-space &tmp foo)").expect("parse"))
            .expect("apply tmp eval")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let tmp_displays = run_surface_core_terms(&tmp_terms);
        assert!(
            tmp_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "expected tmp foo to be true: {tmp_displays:?}"
        );

        let self_terms = match session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!foo").expect("parse"))
            .expect("apply self eval")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let self_displays = run_surface_core_terms(&self_terms);
        assert!(
            !self_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "wrapper mutation leaked into default space: {self_displays:?}"
        );

        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("!(in-space &tmp (new-space!))")
                    .expect("parse reset"),
            )
            .expect("apply reset");
        let after_reset_terms = match session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(in-space &tmp foo)").expect("parse"))
            .expect("apply after reset")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let after_reset_displays = run_surface_core_terms(&after_reset_terms);
        assert!(
            !after_reset_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "tmp reset should clear tmp mutation: {after_reset_displays:?}"
        );
    }

    #[test]
    fn eval_in_unknown_named_space_does_not_fallback_to_default() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(add-atom! &self (= foo true))").expect("parse"),
            )
            .expect("apply self add");

        let eval_default = MeTTaSurfaceSession::parse_line("!foo").expect("parse eval");
        let default_terms = match session
            .apply_stmt(eval_default)
            .expect("apply default eval")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let default_displays = run_surface_core_terms(&default_terms);
        assert!(
            default_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "default eval should resolve foo=true: {default_displays:?}"
        );

        let eval_unknown =
            MeTTaSurfaceSession::parse_line("!(in-space &unknown foo)").expect("parse");
        let unknown_terms = match session
            .apply_stmt(eval_unknown)
            .expect("apply unknown eval")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let unknown_displays = run_surface_core_terms(&unknown_terms);
        assert!(
            !unknown_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "unknown named space should not alias default space: {unknown_displays:?}"
        );
    }

    #[test]
    fn new_space_handle_allocation_can_be_reused() {
        let mut session = MeTTaSurfaceSession::new();
        let alloc = MeTTaSurfaceSession::parse_line("!(new-space!)").expect("parse alloc");
        let alloc_terms = match session.apply_stmt(alloc).expect("apply alloc") {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval from new-space handle allocation"),
        };
        let alloc_displays = run_surface_core_terms(&alloc_terms);
        let handle = alloc_displays
            .iter()
            .find_map(|d| extract_state_out_atom(d))
            .map(|a| session.decode_atom_to_surface(&a))
            .filter(|h| h.starts_with("&space"))
            .expect("expected allocated &spaceN handle");

        let add_stmt = format!("(add-atom! {handle} (= foo true))");
        let _ = session
            .apply_stmt(MeTTaSurfaceSession::parse_line(&add_stmt).expect("parse add"))
            .expect("apply add");

        let eval_stmt = format!("!(in-space {handle} foo)");
        let eval_terms = match session
            .apply_stmt(MeTTaSurfaceSession::parse_line(&eval_stmt).expect("parse eval"))
            .expect("apply eval")
        {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let eval_displays = run_surface_core_terms(&eval_terms);
        assert!(
            eval_displays
                .iter()
                .any(|d| d.contains("C_Return(C_GBoolTrue)")),
            "expected in-space handle lookup to return true, got: {eval_displays:?}"
        );
    }

    #[test]
    fn match_with_space_path_executes() {
        let mut session = MeTTaSurfaceSession::new();
        let stmt = MeTTaSurfaceSession::parse_line("!(in-space &tmp (match 7 7))").expect("parse");
        let out = session.apply_stmt(stmt).expect("apply");
        let terms = match out {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let displays = run_surface_core_terms(&terms);
        assert!(
            displays.iter().any(|d| d.contains("C_Return(C_ATrue)")),
            "expected in-space match to return true, got: {displays:?}"
        );
    }

    #[test]
    fn space_alias_typecheck_executes() {
        let mut session = MeTTaSurfaceSession::new();
        let _ = session
            .apply_stmt(
                MeTTaSurfaceSession::parse_line("(add-atom! &tmp (: foo Bool))").expect("parse"),
            )
            .expect("apply");
        let stmt = MeTTaSurfaceSession::parse_line("!(type-check &tmp foo Bool)").expect("parse");
        let out = session.apply_stmt(stmt).expect("apply");
        let terms = match out {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let displays = run_surface_core_terms(&terms);
        assert!(
            displays.iter().any(|d| d.contains("C_Return(C_ATrue)")),
            "expected type-check alias in space to return true, got: {displays:?}"
        );
    }

    #[test]
    fn match_runtime_semantics_via_unify() {
        let mut session = MeTTaSurfaceSession::new();

        let out_eq = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(match 7 7)").expect("parse"))
            .expect("apply");
        let terms_eq = match out_eq {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let displays_eq = run_surface_core_terms(&terms_eq);
        assert!(
            displays_eq.iter().any(|d| d.contains("C_Return(C_ATrue)")),
            "expected match 7 7 to return true, got: {displays_eq:?}"
        );

        let out_neq = session
            .apply_stmt(MeTTaSurfaceSession::parse_line("!(match 7 8)").expect("parse"))
            .expect("apply");
        let terms_neq = match out_neq {
            SurfaceOutcome::EvalMany { core_terms } => core_terms,
            _ => panic!("expected eval"),
        };
        let displays_neq = run_surface_core_terms(&terms_neq);
        assert!(
            displays_neq
                .iter()
                .any(|d| d.contains("C_Return(C_AFalse)")),
            "expected match 7 8 to return false, got: {displays_neq:?}"
        );
    }
}
