use crate::artifact_contract::load_json_with_checksum;
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::Path;

pub const EXECUTION_CONTRACT_SCHEMA_VERSION: u64 = 4;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExecutionOwner {
    ArtifactBackend,
    GroundedBuiltin,
    ExternalOracle,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExecutionFragmentKind {
    RuleExec,
    Query,
    SpaceEffect,
    Oracle,
    MetaPhase,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExecutionEffectClass {
    PureStructural,
    ReadOnlyLookup,
    NondeterministicReadOnly,
    WritesState,
    OracleIo,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExecutionResourceClass {
    DefaultAtomspace,
    NamedAtomspace,
    MapResource,
    QueueResource,
    SolverResource,
    ExternalResource,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum MemoShape {
    Scalar,
    OutcomeSet,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum BindingMode {
    Bound,
    Free,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum UsageKind {
    Enumerate,
    Exists,
    NegatedExists,
    AggregateInput,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum BuiltinDemandKind {
    RawArgs,
    StructuralEqArgs,
    BoolArgs,
    BoolThenElseArgs,
    NumericArgs,
    FloatArgs,
    TupleArgs,
    ElemAndTupleArgs,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum PremiseArgRole {
    Pattern,
    Template,
    ResultVar,
    PlainInput,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ResultBindingPolicy {
    MustBeFreshVar,
    MayReuseBoundVar,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum RelationPremiseLoweringKind {
    FactMatchEmitPayload,
    LookupExists,
    LookupEnumerate,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SpaceEffectPayloadKind {
    FactPayload,
    SourceRulePayload,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SpaceEffectSinkKind {
    InsertFact,
    RemoveFact,
    InsertRule,
    RemoveRule,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum PayloadPatternShapeKind {
    AnyPattern,
    NonRewritePattern,
    RewriteEqRule,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum GroundedBuiltinHostKind {
    NumericCompare,
    F64Predicate,
    TupleMembership,
    IsVariableTerm,
    ReprTerm,
    ParseTerm,
    PrintlnTerm,
    MetaTypeOfTerm,
    TypeOfTerm,
    QuoteTerm,
    TestAssertion,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AggregationCollectionKind {
    TupleExpr,
    MinAtom,
    MaxAtom,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AggregationSourceKind {
    SubevalAllResults,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ControlBuiltinKind {
    BindThenBody,
    SequenceLastResult,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum LaneEligibilityKind {
    Always,
    GroundNumericArgs,
    GroundBoolArgs,
    GroundConditionOnly,
    GroundStructuralEqArgs,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ResidualPolicy {
    FailClosed,
    FallbackToRules,
    SymbolicFallback,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum NumericResultShape {
    PreserveIntegralIfExact,
    AlwaysFloat,
    AlwaysInteger,
    PreserveInputNumericClass,
}

fn default_lane_eligibility() -> LaneEligibilityKind {
    LaneEligibilityKind::Always
}

fn default_residual_policy() -> ResidualPolicy {
    ResidualPolicy::FailClosed
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExecutionLookupDemandArg {
    pub position: u64,
    pub mode: BindingMode,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExecutionLookupDemand {
    pub relation: String,
    pub logical_relation_id: String,
    pub scope_signature: String,
    pub arity: u64,
    pub args: Vec<ExecutionLookupDemandArg>,
    pub usage_kind: UsageKind,
    pub negated_target: Option<String>,
    pub in_recursive_scc: bool,
    pub hot_path: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExecutionLookupFamily {
    pub family: String,
    pub logical_relation_id: String,
    pub fact_relation: String,
    pub raw_relation: String,
    pub has_relation: String,
    pub result_relation: Option<String>,
    pub query_arity: u64,
    pub payload_arity: u64,
    pub key_positions: Vec<u64>,
    pub demand: Vec<ExecutionLookupDemand>,
    pub no_false_negatives: bool,
    pub exact_result: bool,
    pub stratified_negation_safe: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupQueryExecutionContract {
    pub head: String,
    #[serde(default)]
    pub surface_head: Option<String>,
    pub arity: u64,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub memo_shapes: Vec<MemoShape>,
    pub lookup_family: ExecutionLookupFamily,
    pub source_rule_compilable: bool,
    pub query_compilable: bool,
    pub space_effect_compilable: bool,
    pub builtin_demand: Option<BuiltinDemandKind>,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct SpaceEffectExecutionContract {
    pub head: String,
    #[serde(default)]
    pub surface_head: Option<String>,
    pub arity: u64,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub source_rule_compilable: bool,
    pub query_compilable: bool,
    pub space_effect_compilable: bool,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RelationPremiseExecutionContract {
    pub relation: String,
    pub arity: u64,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub memo_shapes: Vec<MemoShape>,
    pub lookup_family: ExecutionLookupFamily,
    pub arg_roles: Vec<PremiseArgRole>,
    pub result_binding_policy: Option<ResultBindingPolicy>,
    pub lowering_kind: RelationPremiseLoweringKind,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct SpaceEffectPayloadExecutionContract {
    pub head: String,
    pub arity: u64,
    pub space_arg_position: u64,
    pub payload_arg_position: u64,
    pub payload_kind: SpaceEffectPayloadKind,
    pub payload_shape: PayloadPatternShapeKind,
    pub sink_kind: SpaceEffectSinkKind,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub source_rule_compilable: bool,
    pub query_compilable: bool,
    pub space_effect_compilable: bool,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct IntrinsicBuiltinExecutionContract {
    pub head: String,
    pub relation: String,
    pub min_arity: u64,
    pub max_arity: Option<u64>,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub memo_shapes: Vec<MemoShape>,
    pub builtin_demand: BuiltinDemandKind,
    pub numeric_result_shape: Option<NumericResultShape>,
    #[serde(default = "default_lane_eligibility")]
    pub eligibility: LaneEligibilityKind,
    #[serde(default = "default_residual_policy")]
    pub residual_policy: ResidualPolicy,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct GroundedBuiltinExecutionContract {
    pub head: String,
    pub min_arity: u64,
    pub max_arity: Option<u64>,
    pub host_kind: GroundedBuiltinHostKind,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub memo_shapes: Vec<MemoShape>,
    pub builtin_demand: BuiltinDemandKind,
    #[serde(default = "default_lane_eligibility")]
    pub eligibility: LaneEligibilityKind,
    #[serde(default = "default_residual_policy")]
    pub residual_policy: ResidualPolicy,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct AggregationBuiltinExecutionContract {
    pub head: String,
    pub min_arity: u64,
    pub max_arity: Option<u64>,
    pub collection_kind: AggregationCollectionKind,
    pub source_kind: AggregationSourceKind,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub memo_shapes: Vec<MemoShape>,
    #[serde(default = "default_lane_eligibility")]
    pub eligibility: LaneEligibilityKind,
    #[serde(default = "default_residual_policy")]
    pub residual_policy: ResidualPolicy,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ControlBuiltinExecutionContract {
    pub head: String,
    pub min_arity: u64,
    pub max_arity: Option<u64>,
    pub control_kind: ControlBuiltinKind,
    pub owner: ExecutionOwner,
    pub fragment_kind: ExecutionFragmentKind,
    pub effect_class: ExecutionEffectClass,
    pub resource_class: ExecutionResourceClass,
    pub backend_name: String,
    pub memo_shapes: Vec<MemoShape>,
    #[serde(default = "default_lane_eligibility")]
    pub eligibility: LaneEligibilityKind,
    #[serde(default = "default_residual_policy")]
    pub residual_policy: ResidualPolicy,
    pub theorem_refs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "entry_kind", rename_all = "snake_case")]
pub enum ExecutionContractEntry {
    LookupQuery(LookupQueryExecutionContract),
    SpaceEffect(SpaceEffectExecutionContract),
    RelationPremise(RelationPremiseExecutionContract),
    SpaceEffectPayload(SpaceEffectPayloadExecutionContract),
    IntrinsicBuiltin(IntrinsicBuiltinExecutionContract),
    GroundedBuiltin(GroundedBuiltinExecutionContract),
    AggregationBuiltin(AggregationBuiltinExecutionContract),
    ControlBuiltin(ControlBuiltinExecutionContract),
}

impl ExecutionContractEntry {
    pub fn head(&self) -> &str {
        match self {
            Self::LookupQuery(entry) => &entry.head,
            Self::SpaceEffect(entry) => &entry.head,
            Self::RelationPremise(entry) => &entry.relation,
            Self::SpaceEffectPayload(entry) => &entry.head,
            Self::IntrinsicBuiltin(entry) => &entry.head,
            Self::GroundedBuiltin(entry) => &entry.head,
            Self::AggregationBuiltin(entry) => &entry.head,
            Self::ControlBuiltin(entry) => &entry.head,
        }
    }

    pub fn surface_head(&self) -> &str {
        match self {
            Self::LookupQuery(entry) => entry.surface_head.as_deref().unwrap_or(&entry.head),
            Self::SpaceEffect(entry) => entry.surface_head.as_deref().unwrap_or(&entry.head),
            Self::RelationPremise(entry) => &entry.relation,
            Self::SpaceEffectPayload(entry) => &entry.head,
            Self::IntrinsicBuiltin(entry) => &entry.head,
            Self::GroundedBuiltin(entry) => &entry.head,
            Self::AggregationBuiltin(entry) => &entry.head,
            Self::ControlBuiltin(entry) => &entry.head,
        }
    }

    pub fn owner(&self) -> &ExecutionOwner {
        match self {
            Self::LookupQuery(entry) => &entry.owner,
            Self::SpaceEffect(entry) => &entry.owner,
            Self::RelationPremise(entry) => &entry.owner,
            Self::SpaceEffectPayload(entry) => &entry.owner,
            Self::IntrinsicBuiltin(entry) => &entry.owner,
            Self::GroundedBuiltin(entry) => &entry.owner,
            Self::AggregationBuiltin(entry) => &entry.owner,
            Self::ControlBuiltin(entry) => &entry.owner,
        }
    }

    pub fn fragment_kind(&self) -> &ExecutionFragmentKind {
        match self {
            Self::LookupQuery(entry) => &entry.fragment_kind,
            Self::SpaceEffect(entry) => &entry.fragment_kind,
            Self::RelationPremise(entry) => &entry.fragment_kind,
            Self::SpaceEffectPayload(entry) => &entry.fragment_kind,
            Self::IntrinsicBuiltin(entry) => &entry.fragment_kind,
            Self::GroundedBuiltin(entry) => &entry.fragment_kind,
            Self::AggregationBuiltin(entry) => &entry.fragment_kind,
            Self::ControlBuiltin(entry) => &entry.fragment_kind,
        }
    }

    pub fn theorem_refs(&self) -> &[String] {
        match self {
            Self::LookupQuery(entry) => &entry.theorem_refs,
            Self::SpaceEffect(entry) => &entry.theorem_refs,
            Self::RelationPremise(entry) => &entry.theorem_refs,
            Self::SpaceEffectPayload(entry) => &entry.theorem_refs,
            Self::IntrinsicBuiltin(entry) => &entry.theorem_refs,
            Self::GroundedBuiltin(entry) => &entry.theorem_refs,
            Self::AggregationBuiltin(entry) => &entry.theorem_refs,
            Self::ControlBuiltin(entry) => &entry.theorem_refs,
        }
    }

    pub fn lookup_family(&self) -> Option<&ExecutionLookupFamily> {
        match self {
            Self::LookupQuery(entry) => Some(&entry.lookup_family),
            Self::RelationPremise(entry) => Some(&entry.lookup_family),
            Self::SpaceEffect(_)
            | Self::SpaceEffectPayload(_)
            | Self::IntrinsicBuiltin(_)
            | Self::GroundedBuiltin(_)
            | Self::AggregationBuiltin(_)
            | Self::ControlBuiltin(_) => None,
        }
    }

    pub fn builtin_demand(&self) -> Option<&BuiltinDemandKind> {
        match self {
            Self::LookupQuery(entry) => entry.builtin_demand.as_ref(),
            Self::SpaceEffect(_)
            | Self::RelationPremise(_)
            | Self::SpaceEffectPayload(_)
            | Self::AggregationBuiltin(_)
            | Self::ControlBuiltin(_) => None,
            Self::IntrinsicBuiltin(entry) => Some(&entry.builtin_demand),
            Self::GroundedBuiltin(entry) => Some(&entry.builtin_demand),
        }
    }

    pub fn numeric_result_shape(&self) -> Option<&NumericResultShape> {
        match self {
            Self::IntrinsicBuiltin(entry) => entry.numeric_result_shape.as_ref(),
            Self::LookupQuery(_)
            | Self::SpaceEffect(_)
            | Self::RelationPremise(_)
            | Self::SpaceEffectPayload(_)
            | Self::GroundedBuiltin(_)
            | Self::AggregationBuiltin(_)
            | Self::ControlBuiltin(_) => None,
        }
    }

    pub fn accepts_arity(&self, arity: usize) -> bool {
        let arity = arity as u64;
        match self {
            Self::LookupQuery(entry) => entry.arity == arity,
            Self::SpaceEffect(entry) => entry.arity == arity,
            Self::RelationPremise(entry) => entry.arity == arity,
            Self::SpaceEffectPayload(entry) => entry.arity == arity,
            Self::IntrinsicBuiltin(entry) => {
                arity >= entry.min_arity && entry.max_arity.map(|max| arity <= max).unwrap_or(true)
            },
            Self::GroundedBuiltin(entry) => {
                arity >= entry.min_arity && entry.max_arity.map(|max| arity <= max).unwrap_or(true)
            },
            Self::AggregationBuiltin(entry) => {
                arity >= entry.min_arity && entry.max_arity.map(|max| arity <= max).unwrap_or(true)
            },
            Self::ControlBuiltin(entry) => {
                arity >= entry.min_arity && entry.max_arity.map(|max| arity <= max).unwrap_or(true)
            },
        }
    }

    pub fn sort_key(&self) -> String {
        match self {
            Self::LookupQuery(entry) => format!(
                "lookup:{}:{}/{}",
                entry.lookup_family.logical_relation_id, entry.head, entry.arity
            ),
            Self::SpaceEffect(entry) => format!("space_effect:{}/{}", entry.head, entry.arity),
            Self::RelationPremise(entry) => format!(
                "relation_premise:{}:{}/{}",
                entry.lookup_family.logical_relation_id, entry.relation, entry.arity
            ),
            Self::SpaceEffectPayload(entry) => format!(
                "space_effect_payload:{}:{}:{}/{}",
                entry.head,
                match entry.payload_kind {
                    SpaceEffectPayloadKind::FactPayload => "fact_payload",
                    SpaceEffectPayloadKind::SourceRulePayload => "source_rule_payload",
                },
                match entry.sink_kind {
                    SpaceEffectSinkKind::InsertFact => "insert_fact",
                    SpaceEffectSinkKind::RemoveFact => "remove_fact",
                    SpaceEffectSinkKind::InsertRule => "insert_rule",
                    SpaceEffectSinkKind::RemoveRule => "remove_rule",
                },
                entry.arity
            ),
            Self::IntrinsicBuiltin(entry) => format!(
                "intrinsic:{}:{}/{}-{}",
                entry.relation,
                entry.head,
                entry.min_arity,
                entry
                    .max_arity
                    .map(|max| max.to_string())
                    .unwrap_or_else(|| "*".to_string())
            ),
            Self::GroundedBuiltin(entry) => format!(
                "grounded:{}:{}/{}-{}",
                match entry.host_kind {
                    GroundedBuiltinHostKind::NumericCompare => "numeric_compare",
                    GroundedBuiltinHostKind::F64Predicate => "f64_predicate",
                    GroundedBuiltinHostKind::TupleMembership => "tuple_membership",
                    GroundedBuiltinHostKind::IsVariableTerm => "is_variable_term",
                    GroundedBuiltinHostKind::ReprTerm => "repr_term",
                    GroundedBuiltinHostKind::ParseTerm => "parse_term",
                    GroundedBuiltinHostKind::PrintlnTerm => "println_term",
                    GroundedBuiltinHostKind::MetaTypeOfTerm => "meta_type_of_term",
                    GroundedBuiltinHostKind::TypeOfTerm => "type_of_term",
                    GroundedBuiltinHostKind::QuoteTerm => "quote_term",
                    GroundedBuiltinHostKind::TestAssertion => "test_assertion",
                },
                entry.head,
                entry.min_arity,
                entry
                    .max_arity
                    .map(|max| max.to_string())
                    .unwrap_or_else(|| "*".to_string())
            ),
            Self::AggregationBuiltin(entry) => format!(
                "aggregation:{}:{}:{}/{}-{}",
                match entry.source_kind {
                    AggregationSourceKind::SubevalAllResults => "subeval_all_results",
                },
                match entry.collection_kind {
                    AggregationCollectionKind::TupleExpr => "tuple_expr",
                    AggregationCollectionKind::MinAtom => "min_atom",
                    AggregationCollectionKind::MaxAtom => "max_atom",
                },
                entry.head,
                entry.min_arity,
                entry
                    .max_arity
                    .map(|max| max.to_string())
                    .unwrap_or_else(|| "*".to_string())
            ),
            Self::ControlBuiltin(entry) => format!(
                "control:{}:{}/{}-{}",
                match entry.control_kind {
                    ControlBuiltinKind::BindThenBody => "bind_then_body",
                    ControlBuiltinKind::SequenceLastResult => "sequence_last_result",
                },
                entry.head,
                entry.min_arity,
                entry
                    .max_arity
                    .map(|max| max.to_string())
                    .unwrap_or_else(|| "*".to_string())
            ),
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExecutionContractArtifact {
    pub schema_version: u64,
    pub dialect: String,
    pub entries: Vec<ExecutionContractEntry>,
}

pub fn load_execution_contract_artifact_from_dir(
    dir: &Path,
    json_file_name: &str,
    checksum_file_name: &str,
    expected_dialect: &str,
) -> Result<ExecutionContractArtifact, String> {
    let json_path = dir.join(json_file_name);
    let checksum_path = dir.join(checksum_file_name);
    let artifact: ExecutionContractArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "execution-contract")?;
    validate_execution_contract_artifact(&artifact, expected_dialect)?;
    Ok(artifact)
}

pub fn validate_execution_contract_artifact(
    artifact: &ExecutionContractArtifact,
    expected_dialect: &str,
) -> Result<(), String> {
    if artifact.schema_version != EXECUTION_CONTRACT_SCHEMA_VERSION {
        return Err(format!(
            "unsupported {} execution-contract schema_version {} (expected {})",
            expected_dialect, artifact.schema_version, EXECUTION_CONTRACT_SCHEMA_VERSION
        ));
    }
    if !artifact.dialect.eq_ignore_ascii_case(expected_dialect) {
        return Err(format!(
            "execution-contract dialect mismatch: expected {}, got {}",
            expected_dialect, artifact.dialect
        ));
    }
    if artifact.entries.is_empty() {
        return Err("execution-contract artifact has empty entries".to_string());
    }
    index_execution_contract_entries(artifact)?;
    Ok(())
}

fn validate_lookup_query_entry(entry: &LookupQueryExecutionContract) -> Result<(), String> {
    let tag = format!(
        "lookup_query:{}:{}/{}",
        entry.lookup_family.logical_relation_id, entry.head, entry.arity
    );
    if entry.head.trim().is_empty() {
        return Err("lookup_query entry head must be non-empty".to_string());
    }
    if entry.lookup_family.family.trim().is_empty() {
        return Err(format!("{tag}: lookup_family.family must be non-empty"));
    }
    if entry.lookup_family.logical_relation_id.trim().is_empty() {
        return Err(format!("{tag}: lookup_family.logical_relation_id must be non-empty"));
    }
    if entry.lookup_family.query_arity != entry.arity {
        return Err(format!(
            "{tag}: lookup_query arity {} must match lookup_family.query_arity {}",
            entry.arity, entry.lookup_family.query_arity
        ));
    }
    if !matches!(entry.fragment_kind, ExecutionFragmentKind::Query) {
        return Err(format!("{tag}: lookup_query entries must use fragment_kind=query"));
    }
    if !matches!(
        entry.effect_class,
        ExecutionEffectClass::ReadOnlyLookup | ExecutionEffectClass::NondeterministicReadOnly
    ) {
        return Err(format!("{tag}: lookup_query entries must use a read-only query effect class"));
    }
    if !entry.query_compilable {
        return Err(format!("{tag}: first-lane lookup certificate must set query_compilable=true"));
    }
    if entry.space_effect_compilable {
        return Err(format!("{tag}: lookup_query entries cannot set space_effect_compilable=true"));
    }
    if entry.builtin_demand.is_some() {
        return Err(format!("{tag}: lookup_query entries cannot currently carry builtin_demand"));
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    Ok(())
}

fn validate_space_effect_entry(entry: &SpaceEffectExecutionContract) -> Result<(), String> {
    let tag = format!("space_effect:{}/{}", entry.head, entry.arity);
    if entry.head.trim().is_empty() {
        return Err("space_effect entry head must be non-empty".to_string());
    }
    if !matches!(entry.fragment_kind, ExecutionFragmentKind::SpaceEffect) {
        return Err(format!("{tag}: space_effect entries must use fragment_kind=space_effect"));
    }
    if !entry.space_effect_compilable {
        return Err(format!(
            "{tag}: space_effect certificate must set space_effect_compilable=true"
        ));
    }
    if entry.query_compilable {
        return Err(format!("{tag}: space_effect entries cannot set query_compilable=true"));
    }
    if entry.source_rule_compilable {
        return Err(format!("{tag}: space_effect entries cannot set source_rule_compilable=true"));
    }
    if !matches!(entry.effect_class, ExecutionEffectClass::WritesState) {
        return Err(format!("{tag}: space_effect entries must use effect_class=writes_state"));
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    Ok(())
}

fn validate_relation_premise_entry(
    entry: &RelationPremiseExecutionContract,
) -> Result<(), String> {
    let tag = format!(
        "relation_premise:{}:{}/{}",
        entry.lookup_family.logical_relation_id, entry.relation, entry.arity
    );
    if entry.relation.trim().is_empty() {
        return Err("relation_premise entry relation must be non-empty".to_string());
    }
    if entry.lookup_family.family.trim().is_empty() {
        return Err(format!("{tag}: lookup_family.family must be non-empty"));
    }
    if entry.lookup_family.query_arity != entry.arity {
        return Err(format!(
            "{tag}: relation_premise arity {} must match lookup_family.query_arity {}",
            entry.arity, entry.lookup_family.query_arity
        ));
    }
    if entry.arg_roles.len() as u64 != entry.arity {
        return Err(format!("{tag}: arg_roles length must equal arity"));
    }
    if !matches!(entry.fragment_kind, ExecutionFragmentKind::Query) {
        return Err(format!("{tag}: relation_premise entries must use fragment_kind=query"));
    }
    if !matches!(
        entry.effect_class,
        ExecutionEffectClass::ReadOnlyLookup | ExecutionEffectClass::NondeterministicReadOnly
    ) {
        return Err(format!("{tag}: relation_premise entries must use a read-only query effect class"));
    }
    let result_var_count = entry
        .arg_roles
        .iter()
        .filter(|role| matches!(role, PremiseArgRole::ResultVar))
        .count();
    if result_var_count > 1 {
        return Err(format!("{tag}: arg_roles may contain at most one result_var slot"));
    }
    if entry.result_binding_policy.is_some() && result_var_count != 1 {
        return Err(format!(
            "{tag}: result_binding_policy requires exactly one result_var slot"
        ));
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    Ok(())
}

fn validate_space_effect_payload_entry(
    entry: &SpaceEffectPayloadExecutionContract,
) -> Result<(), String> {
    let tag = format!(
        "space_effect_payload:{}:{}/{}",
        entry.head, entry.space_arg_position, entry.payload_arg_position
    );
    if entry.head.trim().is_empty() {
        return Err("space_effect_payload entry head must be non-empty".to_string());
    }
    if !matches!(entry.fragment_kind, ExecutionFragmentKind::SpaceEffect) {
        return Err(format!(
            "{tag}: space_effect_payload entries must use fragment_kind=space_effect"
        ));
    }
    if !entry.space_effect_compilable {
        return Err(format!(
            "{tag}: space_effect_payload entries must set space_effect_compilable=true"
        ));
    }
    if entry.query_compilable {
        return Err(format!(
            "{tag}: space_effect_payload entries cannot set query_compilable=true"
        ));
    }
    if entry.source_rule_compilable {
        return Err(format!(
            "{tag}: space_effect_payload entries cannot set source_rule_compilable=true"
        ));
    }
    if !matches!(entry.effect_class, ExecutionEffectClass::WritesState) {
        return Err(format!(
            "{tag}: space_effect_payload entries must use effect_class=writes_state"
        ));
    }
    if entry.space_arg_position >= entry.arity {
        return Err(format!("{tag}: space_arg_position must be < arity"));
    }
    if entry.payload_arg_position >= entry.arity {
        return Err(format!("{tag}: payload_arg_position must be < arity"));
    }
    if entry.space_arg_position == entry.payload_arg_position {
        return Err(format!(
            "{tag}: space_arg_position and payload_arg_position must differ"
        ));
    }
    match (&entry.payload_kind, &entry.payload_shape) {
        (SpaceEffectPayloadKind::FactPayload, PayloadPatternShapeKind::RewriteEqRule) => {
            return Err(format!(
                "{tag}: fact_payload cannot require rewrite_eq_rule payload_shape"
            ))
        },
        (SpaceEffectPayloadKind::SourceRulePayload, PayloadPatternShapeKind::NonRewritePattern) => {
            return Err(format!(
                "{tag}: source_rule_payload cannot require non_rewrite_pattern payload_shape"
            ))
        },
        _ => {},
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    Ok(())
}

fn validate_intrinsic_builtin_entry(
    entry: &IntrinsicBuiltinExecutionContract,
) -> Result<(), String> {
    let tag = format!(
        "intrinsic_builtin:{}:{}/{}-{}",
        entry.relation,
        entry.head,
        entry.min_arity,
        entry
            .max_arity
            .map(|max| max.to_string())
            .unwrap_or_else(|| "*".to_string())
    );
    if entry.head.trim().is_empty() {
        return Err("intrinsic_builtin entry head must be non-empty".to_string());
    }
    if entry.relation.trim().is_empty() {
        return Err(format!("{tag}: relation must be non-empty"));
    }
    if let Some(max_arity) = entry.max_arity {
        if max_arity < entry.min_arity {
            return Err(format!(
                "{tag}: max_arity {} must be >= min_arity {}",
                max_arity, entry.min_arity
            ));
        }
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    if matches!(entry.builtin_demand, BuiltinDemandKind::BoolThenElseArgs)
        && !matches!(entry.eligibility, LaneEligibilityKind::GroundConditionOnly)
    {
        return Err(format!(
            "{tag}: bool_then_else_args lanes must use eligibility=ground_condition_only"
        ));
    }
    if requires_numeric_result_shape(&entry.head) && entry.numeric_result_shape.is_none() {
        return Err(format!(
            "{tag}: numeric MM2 intrinsic lanes must declare numeric_result_shape"
        ));
    }
    Ok(())
}

fn requires_numeric_result_shape(head: &str) -> bool {
    matches!(
        head,
        "+"
            | "-"
            | "*"
            | "/"
            | "%"
            | "pow-math"
            | "sqrt-math"
            | "abs-math"
            | "log-math"
            | "trunc-math"
            | "ceil-math"
            | "floor-math"
            | "round-math"
            | "sin-math"
            | "asin-math"
            | "cos-math"
            | "acos-math"
            | "tan-math"
            | "atan-math"
    )
}

fn validate_grounded_builtin_entry(
    entry: &GroundedBuiltinExecutionContract,
) -> Result<(), String> {
    let tag = format!(
        "grounded_builtin:{:?}:{}/{}-{}",
        entry.host_kind,
        entry.head,
        entry.min_arity,
        entry
            .max_arity
            .map(|max| max.to_string())
            .unwrap_or_else(|| "*".to_string())
    );
    if entry.head.trim().is_empty() {
        return Err("grounded_builtin entry head must be non-empty".to_string());
    }
    if let Some(max_arity) = entry.max_arity {
        if max_arity < entry.min_arity {
            return Err(format!(
                "{tag}: max_arity {} must be >= min_arity {}",
                max_arity, entry.min_arity
            ));
        }
    }
    if !matches!(entry.owner, ExecutionOwner::GroundedBuiltin) {
        return Err(format!(
            "{tag}: grounded_builtin entries must use owner=grounded_builtin"
        ));
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    if matches!(entry.eligibility, LaneEligibilityKind::Always)
        && !matches!(
            entry.host_kind,
            GroundedBuiltinHostKind::ReprTerm
                | GroundedBuiltinHostKind::IsVariableTerm
                | GroundedBuiltinHostKind::TupleMembership
                | GroundedBuiltinHostKind::MetaTypeOfTerm
                | GroundedBuiltinHostKind::ParseTerm
                | GroundedBuiltinHostKind::PrintlnTerm
                | GroundedBuiltinHostKind::TypeOfTerm
                | GroundedBuiltinHostKind::QuoteTerm
                | GroundedBuiltinHostKind::TestAssertion
        )
    {
        return Err(format!(
            "{tag}: grounded_builtin entries must declare an explicit non-trivial eligibility unless the host kind is a pure reflection lane"
        ));
    }
    Ok(())
}

fn validate_aggregation_builtin_entry(
    entry: &AggregationBuiltinExecutionContract,
) -> Result<(), String> {
    let tag = format!(
        "aggregation_builtin:{:?}:{:?}:{}/{}-{}",
        entry.source_kind,
        entry.collection_kind,
        entry.head,
        entry.min_arity,
        entry
            .max_arity
            .map(|max| max.to_string())
            .unwrap_or_else(|| "*".to_string())
    );
    if entry.head.trim().is_empty() {
        return Err("aggregation_builtin entry head must be non-empty".to_string());
    }
    if let Some(max_arity) = entry.max_arity {
        if max_arity < entry.min_arity {
            return Err(format!(
                "{tag}: max_arity {} must be >= min_arity {}",
                max_arity, entry.min_arity
            ));
        }
    }
    if !matches!(entry.owner, ExecutionOwner::ArtifactBackend) {
        return Err(format!(
            "{tag}: aggregation_builtin entries must use owner=artifact_backend"
        ));
    }
    if !matches!(entry.fragment_kind, ExecutionFragmentKind::MetaPhase) {
        return Err(format!(
            "{tag}: aggregation_builtin entries must use fragment_kind=meta_phase"
        ));
    }
    if !matches!(
        entry.effect_class,
        ExecutionEffectClass::ReadOnlyLookup | ExecutionEffectClass::NondeterministicReadOnly
    ) {
        return Err(format!(
            "{tag}: aggregation_builtin entries must use a read-only effect class"
        ));
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    Ok(())
}

fn validate_control_builtin_entry(entry: &ControlBuiltinExecutionContract) -> Result<(), String> {
    let tag = format!(
        "control_builtin:{:?}:{}/{}-{}",
        entry.control_kind,
        entry.head,
        entry.min_arity,
        entry
            .max_arity
            .map(|max| max.to_string())
            .unwrap_or_else(|| "*".to_string())
    );
    if entry.head.trim().is_empty() {
        return Err("control_builtin entry head must be non-empty".to_string());
    }
    if let Some(max_arity) = entry.max_arity {
        if max_arity < entry.min_arity {
            return Err(format!(
                "{tag}: max_arity {} must be >= min_arity {}",
                max_arity, entry.min_arity
            ));
        }
    }
    if !matches!(entry.owner, ExecutionOwner::ArtifactBackend) {
        return Err(format!(
            "{tag}: control_builtin entries must use owner=artifact_backend"
        ));
    }
    if !matches!(entry.fragment_kind, ExecutionFragmentKind::MetaPhase) {
        return Err(format!(
            "{tag}: control_builtin entries must use fragment_kind=meta_phase"
        ));
    }
    if !matches!(entry.effect_class, ExecutionEffectClass::WritesState) {
        return Err(format!(
            "{tag}: control_builtin entries must conservatively use effect_class=writes_state"
        ));
    }
    if entry.theorem_refs.is_empty() {
        return Err(format!("{tag}: theorem_refs cannot be empty"));
    }
    Ok(())
}

pub fn index_execution_contract_entries(
    artifact: &ExecutionContractArtifact,
) -> Result<BTreeMap<String, ExecutionContractEntry>, String> {
    let mut by_sort_key = BTreeMap::new();
    for entry in &artifact.entries {
        match entry {
            ExecutionContractEntry::LookupQuery(entry) => validate_lookup_query_entry(entry)?,
            ExecutionContractEntry::SpaceEffect(entry) => validate_space_effect_entry(entry)?,
            ExecutionContractEntry::RelationPremise(entry) => {
                validate_relation_premise_entry(entry)?
            },
            ExecutionContractEntry::SpaceEffectPayload(entry) => {
                validate_space_effect_payload_entry(entry)?
            },
            ExecutionContractEntry::IntrinsicBuiltin(entry) => {
                validate_intrinsic_builtin_entry(entry)?
            },
            ExecutionContractEntry::GroundedBuiltin(entry) => {
                validate_grounded_builtin_entry(entry)?
            },
            ExecutionContractEntry::AggregationBuiltin(entry) => {
                validate_aggregation_builtin_entry(entry)?
            },
            ExecutionContractEntry::ControlBuiltin(entry) => {
                validate_control_builtin_entry(entry)?
            },
        }
        let key = entry.sort_key();
        if by_sort_key.insert(key.clone(), entry.clone()).is_some() {
            return Err(format!(
                "execution contract entries must be unique by entry kind, relation/family, head, and arity; duplicate '{}'",
                key
            ));
        }
    }
    Ok(by_sort_key)
}

pub fn execution_contract_entry<'a>(
    artifact: &'a ExecutionContractArtifact,
    head: &str,
    arity: usize,
) -> Option<&'a ExecutionContractEntry> {
    artifact
        .entries
        .iter()
        .find(|entry| {
            matches!(
                entry,
                ExecutionContractEntry::LookupQuery(_) | ExecutionContractEntry::SpaceEffect(_)
            ) && entry.surface_head() == head
                && entry.accepts_arity(arity)
        })
        .or_else(|| {
            artifact.entries.iter().find(|entry| {
                matches!(entry, ExecutionContractEntry::IntrinsicBuiltin(_))
                    && entry.surface_head() == head
                    && entry.accepts_arity(arity)
            })
        })
        .or_else(|| {
            artifact.entries.iter().find(|entry| {
                matches!(entry, ExecutionContractEntry::GroundedBuiltin(_))
                    && entry.surface_head() == head
                    && entry.accepts_arity(arity)
            })
        })
        .or_else(|| {
            artifact.entries.iter().find(|entry| {
                matches!(entry, ExecutionContractEntry::AggregationBuiltin(_))
                    && entry.surface_head() == head
                    && entry.accepts_arity(arity)
            })
        })
        .or_else(|| {
            artifact.entries.iter().find(|entry| {
                matches!(entry, ExecutionContractEntry::ControlBuiltin(_))
                    && entry.surface_head() == head
                    && entry.accepts_arity(arity)
            })
        })
}

pub fn execution_contract_relation_premise_entry<'a>(
    artifact: &'a ExecutionContractArtifact,
    relation: &str,
    arity: usize,
) -> Option<&'a RelationPremiseExecutionContract> {
    artifact.entries.iter().find_map(|entry| match entry {
        ExecutionContractEntry::RelationPremise(entry)
            if entry.relation == relation && entry.arity == arity as u64 =>
        {
            Some(entry)
        },
        _ => None,
    })
}

pub fn execution_contract_space_effect_payload_entry<'a>(
    artifact: &'a ExecutionContractArtifact,
    head: &str,
    arity: usize,
    payload_kind: SpaceEffectPayloadKind,
) -> Option<&'a SpaceEffectPayloadExecutionContract> {
    artifact.entries.iter().find_map(|entry| match entry {
        ExecutionContractEntry::SpaceEffectPayload(entry)
            if entry.head == head
                && entry.arity == arity as u64
                && entry.payload_kind == payload_kind =>
        {
            Some(entry)
        },
        _ => None,
    })
}

pub fn execution_contract_space_effect_payload_entries<'a>(
    artifact: &'a ExecutionContractArtifact,
    head: &'a str,
    arity: usize,
) -> impl Iterator<Item = &'a SpaceEffectPayloadExecutionContract> + 'a {
    artifact.entries.iter().filter_map(move |entry| match entry {
        ExecutionContractEntry::SpaceEffectPayload(entry)
            if entry.head == head && entry.arity == arity as u64 =>
        {
            Some(entry)
        },
        _ => None,
    })
}

pub fn execution_contract_grounded_builtin_entry<'a>(
    artifact: &'a ExecutionContractArtifact,
    head: &str,
    arity: usize,
) -> Option<&'a GroundedBuiltinExecutionContract> {
    let arity = arity as u64;
    artifact.entries.iter().find_map(|entry| match entry {
        ExecutionContractEntry::GroundedBuiltin(entry)
            if entry.head == head
                && arity >= entry.min_arity
                && entry.max_arity.map(|max| arity <= max).unwrap_or(true) =>
        {
            Some(entry)
        },
        _ => None,
    })
}

pub fn execution_contract_aggregation_builtin_entry<'a>(
    artifact: &'a ExecutionContractArtifact,
    head: &str,
    arity: usize,
) -> Option<&'a AggregationBuiltinExecutionContract> {
    let arity = arity as u64;
    artifact.entries.iter().find_map(|entry| match entry {
        ExecutionContractEntry::AggregationBuiltin(entry)
            if entry.head == head
                && arity >= entry.min_arity
                && entry.max_arity.map(|max| arity <= max).unwrap_or(true) =>
        {
            Some(entry)
        },
        _ => None,
    })
}

pub fn execution_contract_control_builtin_entry<'a>(
    artifact: &'a ExecutionContractArtifact,
    head: &str,
    arity: usize,
) -> Option<&'a ControlBuiltinExecutionContract> {
    let arity = arity as u64;
    artifact.entries.iter().find_map(|entry| match entry {
        ExecutionContractEntry::ControlBuiltin(entry)
            if entry.head == head
                && arity >= entry.min_arity
                && entry.max_arity.map(|max| arity <= max).unwrap_or(true) =>
        {
            Some(entry)
        },
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_artifact() -> ExecutionContractArtifact {
        serde_json::from_str(
            r#"{
              "schema_version": 4,
              "dialect": "petta",
              "entries": [
                {
                  "entry_kind": "lookup_query",
                  "head": "match",
                  "arity": 3,
                  "owner": "artifact_backend",
                  "fragment_kind": "query",
                  "effect_class": "read_only_lookup",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "memo_shapes": ["scalar", "outcome_set"],
                  "lookup_family": {
                    "family": "spaceMatch",
                    "logical_relation_id": "petta.space_match",
                    "fact_relation": "selfFact",
                    "raw_relation": "spaceMatchRaw",
                    "has_relation": "spaceMatchHas",
                    "result_relation": "spaceMatchResult",
                    "query_arity": 3,
                    "payload_arity": 1,
                    "key_positions": [0, 1],
                    "demand": [],
                    "no_false_negatives": true,
                    "exact_result": false,
                    "stratified_negation_safe": true
                  },
                  "source_rule_compilable": false,
                  "query_compilable": true,
                  "space_effect_compilable": false,
                  "builtin_demand": null,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
                  ]
                },
                {
                  "entry_kind": "space_effect",
                  "head": "add-atom",
                  "arity": 2,
                  "owner": "artifact_backend",
                  "fragment_kind": "space_effect",
                  "effect_class": "writes_state",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "source_rule_compilable": false,
                  "query_compilable": false,
                  "space_effect_compilable": true,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_toMorkSink"
                  ]
                },
                {
                  "entry_kind": "relation_premise",
                  "relation": "spaceMatch",
                  "arity": 3,
                  "owner": "artifact_backend",
                  "fragment_kind": "query",
                  "effect_class": "read_only_lookup",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "memo_shapes": ["scalar", "outcome_set"],
                  "lookup_family": {
                    "family": "spaceMatch",
                    "logical_relation_id": "petta.space_match",
                    "fact_relation": "selfFact",
                    "raw_relation": "spaceMatchRaw",
                    "has_relation": "spaceMatchHas",
                    "result_relation": "spaceMatchResult",
                    "query_arity": 3,
                    "payload_arity": 1,
                    "key_positions": [0, 1],
                    "demand": [],
                    "no_false_negatives": true,
                    "exact_result": false,
                    "stratified_negation_safe": true
                  },
                  "arg_roles": ["pattern", "template", "result_var"],
                  "result_binding_policy": "must_be_fresh_var",
                  "lowering_kind": "fact_match_emit_payload",
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
                  ]
                },
                {
                  "entry_kind": "space_effect_payload",
                  "head": "add-atom",
                  "arity": 2,
                  "space_arg_position": 0,
                  "payload_arg_position": 1,
                  "payload_kind": "fact_payload",
                  "payload_shape": "non_rewrite_pattern",
                  "sink_kind": "insert_fact",
                  "owner": "artifact_backend",
                  "fragment_kind": "space_effect",
                  "effect_class": "writes_state",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "source_rule_compilable": false,
                  "query_compilable": false,
                  "space_effect_compilable": true,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_toMorkSink"
                  ]
                },
                {
                  "entry_kind": "intrinsic_builtin",
                  "head": "+",
                  "relation": "intrinsic:+",
                  "min_arity": 2,
                  "max_arity": null,
                  "owner": "artifact_backend",
                  "fragment_kind": "rule_exec",
                  "effect_class": "pure_structural",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "memo_shapes": ["outcome_set", "scalar"],
                  "builtin_demand": "numeric_args",
                  "numeric_result_shape": "preserve_integral_if_exact",
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.mkCoreIntrinsicContract_relation"
                  ]
                },
                {
                  "entry_kind": "grounded_builtin",
                  "head": "<",
                  "min_arity": 2,
                  "max_arity": 2,
                  "host_kind": "numeric_compare",
                  "owner": "grounded_builtin",
                  "fragment_kind": "rule_exec",
                  "effect_class": "pure_structural",
                  "resource_class": "default_atomspace",
                  "backend_name": "grounded-host",
                  "memo_shapes": ["scalar", "outcome_set"],
                  "builtin_demand": "numeric_args",
                  "eligibility": "ground_numeric_args",
                  "residual_policy": "fallback_to_rules",
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_executable_total"
                  ]
                }
              ]
            }"#,
        )
        .expect("sample execution contract json")
    }

    #[test]
    fn validate_sample_execution_contract() {
        validate_execution_contract_artifact(&sample_artifact(), "petta")
            .expect("sample execution contract");
    }

    #[test]
    fn duplicate_entries_are_rejected() {
        let mut artifact = sample_artifact();
        artifact.entries.push(artifact.entries[0].clone());
        let err = validate_execution_contract_artifact(&artifact, "petta")
            .expect_err("duplicate entry must fail");
        assert!(err.contains("must be unique"));
    }

    #[test]
    fn missing_theorem_refs_are_rejected() {
        let mut artifact = sample_artifact();
        match &mut artifact.entries[4] {
            ExecutionContractEntry::IntrinsicBuiltin(entry) => entry.theorem_refs.clear(),
            ExecutionContractEntry::LookupQuery(_)
            | ExecutionContractEntry::SpaceEffect(_)
            | ExecutionContractEntry::RelationPremise(_)
            | ExecutionContractEntry::SpaceEffectPayload(_)
            | ExecutionContractEntry::GroundedBuiltin(_)
            | ExecutionContractEntry::AggregationBuiltin(_)
            | ExecutionContractEntry::ControlBuiltin(_) => {
                unreachable!("third entry is intrinsic_builtin")
            },
        }
        let err = validate_execution_contract_artifact(&artifact, "petta")
            .expect_err("missing theorem refs must fail");
        assert!(err.contains("theorem_refs"));
    }

    #[test]
    fn invalid_intrinsic_arity_range_is_rejected() {
        let mut artifact = sample_artifact();
        match &mut artifact.entries[4] {
            ExecutionContractEntry::IntrinsicBuiltin(entry) => entry.max_arity = Some(1),
            ExecutionContractEntry::LookupQuery(_)
            | ExecutionContractEntry::SpaceEffect(_)
            | ExecutionContractEntry::RelationPremise(_)
            | ExecutionContractEntry::SpaceEffectPayload(_)
            | ExecutionContractEntry::GroundedBuiltin(_)
            | ExecutionContractEntry::AggregationBuiltin(_)
            | ExecutionContractEntry::ControlBuiltin(_) => {
                unreachable!("third entry is intrinsic_builtin")
            },
        }
        let err = validate_execution_contract_artifact(&artifact, "petta")
            .expect_err("invalid intrinsic arity range must fail");
        assert!(err.contains("max_arity"));
    }

    #[test]
    fn lookup_query_must_be_query_compilable() {
        let mut artifact = sample_artifact();
        match &mut artifact.entries[0] {
            ExecutionContractEntry::LookupQuery(entry) => entry.query_compilable = false,
            ExecutionContractEntry::SpaceEffect(_)
            | ExecutionContractEntry::RelationPremise(_)
            | ExecutionContractEntry::SpaceEffectPayload(_)
            | ExecutionContractEntry::IntrinsicBuiltin(_)
            | ExecutionContractEntry::GroundedBuiltin(_)
            | ExecutionContractEntry::AggregationBuiltin(_)
            | ExecutionContractEntry::ControlBuiltin(_) => {
                unreachable!("first entry is lookup_query")
            },
        }
        let err = validate_execution_contract_artifact(&artifact, "petta")
            .expect_err("lookup_query must be query_compilable");
        assert!(err.contains("query_compilable"));
    }

    #[test]
    fn lookup_by_head_and_arity_works() {
        let artifact = sample_artifact();
        let entry = execution_contract_entry(&artifact, "match", 3).expect("match entry");
        let lookup_family = entry.lookup_family().expect("lookup family");
        assert_eq!(lookup_family.family, "spaceMatch");
        assert!(!lookup_family.exact_result);
    }

    #[test]
    fn intrinsic_lookup_by_head_and_arity_range_works() {
        let artifact = sample_artifact();
        let entry = execution_contract_entry(&artifact, "+", 4).expect("intrinsic entry");
        assert_eq!(entry.builtin_demand(), Some(&BuiltinDemandKind::NumericArgs));
        assert_eq!(entry.fragment_kind(), &ExecutionFragmentKind::RuleExec);
    }

    #[test]
    fn grounded_builtin_lookup_by_head_and_arity_range_works() {
        let artifact = sample_artifact();
        let entry = execution_contract_entry(&artifact, "<", 2).expect("grounded entry");
        assert_eq!(entry.builtin_demand(), Some(&BuiltinDemandKind::NumericArgs));
        assert_eq!(entry.owner(), &ExecutionOwner::GroundedBuiltin);
    }

    #[test]
    fn grounded_builtin_direct_lookup_works() {
        let artifact = sample_artifact();
        let entry = execution_contract_grounded_builtin_entry(&artifact, "<", 2)
            .expect("grounded builtin entry");
        assert_eq!(entry.host_kind, GroundedBuiltinHostKind::NumericCompare);
        assert_eq!(entry.backend_name, "grounded-host");
    }

    #[test]
    fn relation_premise_lookup_works() {
        let artifact = sample_artifact();
        let entry = execution_contract_relation_premise_entry(&artifact, "spaceMatch", 3)
            .expect("spaceMatch premise");
        assert_eq!(
            entry.arg_roles,
            vec![
                PremiseArgRole::Pattern,
                PremiseArgRole::Template,
                PremiseArgRole::ResultVar,
            ]
        );
        assert_eq!(
            entry.result_binding_policy,
            Some(ResultBindingPolicy::MustBeFreshVar)
        );
    }

    #[test]
    fn space_effect_payload_lookup_works() {
        let artifact = sample_artifact();
        let entry = execution_contract_space_effect_payload_entry(
            &artifact,
            "add-atom",
            2,
            SpaceEffectPayloadKind::FactPayload,
        )
        .expect("add-atom fact payload");
        assert_eq!(entry.payload_shape, PayloadPatternShapeKind::NonRewritePattern);
        assert_eq!(entry.sink_kind, SpaceEffectSinkKind::InsertFact);
        assert_eq!(entry.space_arg_position, 0);
        assert_eq!(entry.payload_arg_position, 1);
    }
}
