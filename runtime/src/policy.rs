//! Shared execution policy types for language runtimes.
//!
//! These types are intentionally language-agnostic so policy knobs can be
//! consumed by any GSLT+NTT-derived runtime, not only MeTTa surface lowering.

use crate::{RuntimeOptimizationHints, SurfacePolicyHint};

/// Default bound for rewrite/fixpoint steps in bounded evaluators.
pub const DEFAULT_REWRITE_STEPS: usize = 512;
/// Default bound for branching fanout per rewrite step.
pub const DEFAULT_REWRITE_BRANCHES: usize = 64;
/// Default bound for emitted normal-form outcomes.
pub const DEFAULT_REWRITE_OUTCOMES: usize = 32;
/// Default number of rule-copy bands generated for MORK unfold/base/fold scheduling.
pub const DEFAULT_MORK_RULE_COPIES: usize = 32;
/// Default hard step cap passed to `Space::metta_calculus` in MORK execution.
pub const DEFAULT_MORK_MAX_STEPS: usize = 1_000_000;

/// Generic limits for nondeterministic rewrite-style execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RewriteLimits {
    pub max_steps: usize,
    pub max_branches: usize,
    pub max_outcomes: usize,
}

impl Default for RewriteLimits {
    fn default() -> Self {
        Self {
            max_steps: DEFAULT_REWRITE_STEPS,
            max_branches: DEFAULT_REWRITE_BRANCHES,
            max_outcomes: DEFAULT_REWRITE_OUTCOMES,
        }
    }
}

/// Generic execution bounds for MORK-style forward chaining backends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MorkExecutionLimits {
    /// Number of interleaved copies per phase (unfold/base/fold).
    pub rule_copies: usize,
    /// Maximum fixpoint transitions for one query.
    pub max_steps: usize,
}

impl Default for MorkExecutionLimits {
    fn default() -> Self {
        Self {
            rule_copies: DEFAULT_MORK_RULE_COPIES,
            max_steps: DEFAULT_MORK_MAX_STEPS,
        }
    }
}

/// Backend preference for execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeBackend {
    /// Default backend for the active language runtime.
    Auto,
    /// Force Ascent/datalog-style backend where supported.
    Ascent,
    /// Force MORK backend where supported.
    Mork,
}

impl Default for RuntimeBackend {
    fn default() -> Self {
        Self::Auto
    }
}

/// Unified per-run execution policy override.
///
/// This keeps CLI/repl policy state in one object instead of scattered flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct RuntimeExecutionPolicy {
    pub surface_fuel: Option<usize>,
    pub core_fuel: Option<usize>,
    pub surface_first_branch_only: Option<bool>,
    pub surface_exact_priority: Option<bool>,
    pub surface_recursive_memo: Option<bool>,
    pub surface_deterministic: Option<bool>,
    pub backend: Option<RuntimeBackend>,
    pub mork_rule_copies: Option<usize>,
    pub mork_max_steps: Option<usize>,
}

/// Effective surface execution settings after applying language/theory hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EffectiveSurfaceExecutionPolicy {
    pub deterministic: bool,
    pub first_branch_only: bool,
    pub exact_priority: bool,
    pub recursive_memo: bool,
}

/// Resolved optimization-contract safety gates for runtime dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct RuntimeDispatchContracts {
    /// Deterministic-collapse optimization contract.
    pub deterministic_reduction: bool,
    /// Memoization safety contract.
    pub memoization_safe: bool,
    /// Specialization/indexing safety contract.
    pub specialization_safe: bool,
    /// Core ground-eval safety requires both memoization and specialization
    /// contracts.
    pub core_ground_eval_safe: bool,
}

/// Resolve optimization contracts from language metadata hints.
pub fn resolve_runtime_dispatch_contracts(
    hints: RuntimeOptimizationHints,
) -> RuntimeDispatchContracts {
    let optimization_contracts = hints.optimization_contracts;
    RuntimeDispatchContracts {
        deterministic_reduction: optimization_contracts.deterministic_reduction,
        memoization_safe: optimization_contracts.memoization_safe,
        specialization_safe: optimization_contracts.specialization_safe,
        core_ground_eval_safe: optimization_contracts.memoization_safe
            && optimization_contracts.specialization_safe,
    }
}

impl RuntimeExecutionPolicy {
    /// Resolve effective surface rewrite policy by combining explicit per-run
    /// overrides with language metadata hints.
    pub fn effective_surface_policy(
        self,
        hints: RuntimeOptimizationHints,
    ) -> EffectiveSurfaceExecutionPolicy {
        let contracts = resolve_runtime_dispatch_contracts(hints);
        let hinted_deterministic = matches!(hints.surface_policy, SurfacePolicyHint::Deterministic)
            && contracts.deterministic_reduction;
        let deterministic = self.surface_deterministic.unwrap_or(hinted_deterministic);

        let first_branch_only = self.surface_first_branch_only.unwrap_or(false) || deterministic;
        let exact_priority = if deterministic {
            true
        } else {
            self.surface_exact_priority.unwrap_or(false)
        };
        let recursive_memo = if deterministic {
            true
        } else {
            self.surface_recursive_memo.unwrap_or(true)
        };

        EffectiveSurfaceExecutionPolicy {
            deterministic,
            first_branch_only,
            exact_priority,
            recursive_memo,
        }
    }

    /// Classify report label for surface policy after combining explicit overrides
    /// with theory/runtime hints.
    pub fn surface_policy_label(self, hints: RuntimeOptimizationHints) -> &'static str {
        let contracts = resolve_runtime_dispatch_contracts(hints);
        let hinted_deterministic = matches!(hints.surface_policy, SurfacePolicyHint::Deterministic)
            && contracts.deterministic_reduction;
        let deterministic = self.surface_deterministic.unwrap_or(hinted_deterministic);
        if self.surface_deterministic == Some(true) {
            return "deterministic";
        }
        let has_custom_surface_override = self.surface_first_branch_only == Some(true)
            || self.surface_exact_priority == Some(true)
            || self.surface_recursive_memo.is_some()
            || self.surface_deterministic == Some(false);
        if has_custom_surface_override {
            return "custom";
        }
        if deterministic {
            "theory-deterministic"
        } else {
            "default"
        }
    }
}

/// Resolve core ground-eval enablement from environment override plus language hints
/// and pre-resolved optimization contracts.
pub fn resolve_core_ground_eval_enabled_with_contracts(
    env_override_enabled: bool,
    hints: RuntimeOptimizationHints,
    contracts: RuntimeDispatchContracts,
) -> bool {
    env_override_enabled || (hints.enable_core_ground_eval && contracts.core_ground_eval_safe)
}

/// Resolve core ground-eval enablement from environment override plus language hints.
pub fn resolve_core_ground_eval_enabled(
    env_override_enabled: bool,
    hints: RuntimeOptimizationHints,
) -> bool {
    let contracts = resolve_runtime_dispatch_contracts(hints);
    resolve_core_ground_eval_enabled_with_contracts(env_override_enabled, hints, contracts)
}

/// Named rule/expression fragments that can be used as optimization safety gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuleFragment {
    /// Fragment safe for core ground-call evaluation fast-path.
    CoreGroundEval,
}

/// Backend-agnostic safety contract for optimization fragments.
///
/// Adapters map their AST/rule representations to this contract so runtime
/// policy can conservatively enable optimizations only when formally safe.
pub trait RuleFragmentSafety {
    type Expr;
    type Rule;

    /// Whether an expression is in the selected safe fragment.
    fn expr_is_fragment_safe(expr: &Self::Expr, fragment: RuleFragment) -> bool;

    /// Whether a rule is in the selected safe fragment.
    fn rule_is_fragment_safe(rule: &Self::Rule, fragment: RuleFragment) -> bool;
}

/// Helper to query fragment safety for an expression through adapter hooks.
pub fn expr_fragment_safe<Hooks>(expr: &Hooks::Expr, fragment: RuleFragment) -> bool
where
    Hooks: RuleFragmentSafety,
{
    Hooks::expr_is_fragment_safe(expr, fragment)
}

/// Helper to query fragment safety for a rule through adapter hooks.
pub fn rule_fragment_safe<Hooks>(rule: &Hooks::Rule, fragment: RuleFragment) -> bool
where
    Hooks: RuleFragmentSafety,
{
    Hooks::rule_is_fragment_safe(rule, fragment)
}

/// Backend-agnostic hooks for deciding whether an expression can safely use
/// a core fast-path evaluator.
///
/// Language adapters provide this once, then reuse the shared eligibility
/// function across REPL/runtime entry points.
pub trait CoreFastPathEligibility: RuleFragmentSafety {
    /// Syntactic/semantic gate for expression shape (e.g. groundness).
    fn is_ground_candidate(expr: &Self::Expr) -> bool;

    /// Extract the dispatch head used for rule lookup.
    fn expr_head(expr: &Self::Expr) -> Option<&str>;

    /// Extract the head from one rule candidate.
    fn rule_head(rule: &Self::Rule) -> Option<&str>;
}

/// Generic core fast-path eligibility resolution.
///
/// This provides the shared "head-matched rules must all be translatable"
/// policy so language adapters only define shape/safety predicates.
pub fn is_core_fast_path_eligible<'a, Hooks>(
    expr: &Hooks::Expr,
    rules: impl IntoIterator<Item = &'a Hooks::Rule>,
) -> bool
where
    Hooks: CoreFastPathEligibility,
    Hooks::Rule: 'a,
{
    if !Hooks::is_ground_candidate(expr) {
        return false;
    }
    if !expr_fragment_safe::<Hooks>(expr, RuleFragment::CoreGroundEval) {
        return false;
    }

    let Some(target_head) = Hooks::expr_head(expr) else {
        return false;
    };

    let mut matched_any = false;
    for rule in rules {
        let Some(rule_head) = Hooks::rule_head(rule) else {
            continue;
        };
        if rule_head != target_head {
            continue;
        }
        matched_any = true;
        if !rule_fragment_safe::<Hooks>(rule, RuleFragment::CoreGroundEval) {
            return false;
        }
    }

    matched_any
}
