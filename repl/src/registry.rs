use anyhow::{bail, Result};
use mettail_runtime::{
    AscentResults, Language, LibraryAliasDef, OracleDescriptor, OracleQuery, OracleResponse,
    RuntimeBackend, Term, TermType, VarTypeInfo,
};
use std::any::Any;
use std::collections::HashMap;
use std::process::Command;

// Import generated language implementations directly
use mettail_languages::ambient::AmbientLanguage;
use mettail_languages::calculator::CalculatorLanguage;
use mettail_languages::imp_from_lean::IMPLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::mettahe_from_lean::MeTTaHELanguage;
use mettail_languages::minskylite_from_lean::MinskyLiteLanguage;
use mettail_languages::mm0lite_from_lean::MM0LiteLanguage;
use mettail_languages::rhocalc::RhoCalcLanguage;

/// Registry of available languages
pub struct LanguageRegistry {
    languages: HashMap<String, Box<dyn Language>>,
}

/// Language wrapper that adds a stable read-only metadata oracle.
struct OracleAugmentedLanguage {
    inner: Box<dyn Language>,
    expose_meta_oracle: bool,
}

impl OracleAugmentedLanguage {
    fn new(inner: Box<dyn Language>) -> Self {
        Self { inner, expose_meta_oracle: true }
    }
}

fn python_oracle_feature_enabled() -> bool {
    cfg!(feature = "python-oracle")
}

fn python_oracle_runtime_enabled() -> bool {
    std::env::var("METTAIL_ENABLE_PYTHON_ORACLE")
        .map(|v| matches!(v.as_str(), "1" | "true" | "TRUE" | "yes" | "YES"))
        .unwrap_or(false)
}

fn parse_python_arg(raw: &str) -> String {
    raw.to_string()
}

fn run_python_call(module: &str, function: &str, args: &[String]) -> Result<String, String> {
    let mut cmd = Command::new("python3");
    cmd.arg("-c").arg(
        r#"
import importlib, json, sys
module_name = sys.argv[1]
fn_name = sys.argv[2]
raw_args = sys.argv[3:]
def parse_arg(x):
    lx = x.lower()
    if lx == "true":
        return True
    if lx == "false":
        return False
    try:
        return int(x)
    except:
        pass
    try:
        return float(x)
    except:
        pass
    return x
mod = importlib.import_module(module_name)
fn = getattr(mod, fn_name)
res = fn(*[parse_arg(a) for a in raw_args])
print(json.dumps(res))
"#,
    );
    cmd.arg(module).arg(function);
    for arg in args {
        cmd.arg(parse_python_arg(arg));
    }
    let output = cmd
        .output()
        .map_err(|e| format!("failed to start python3: {}", e))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(if stderr.is_empty() {
            format!("python call failed with status {}", output.status)
        } else {
            format!("python call failed: {}", stderr)
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

impl Language for OracleAugmentedLanguage {
    fn name(&self) -> &'static str {
        self.inner.name()
    }

    fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
        self.inner.metadata()
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.inner.parse_term(input)
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.inner.parse_term_for_env(input)
    }

    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> {
        self.inner.run_ascent(term)
    }

    fn supports_backend(&self, backend: RuntimeBackend) -> bool {
        self.inner.supports_backend(backend)
    }

    fn run_backend(
        &self,
        term: &dyn Term,
        backend: RuntimeBackend,
    ) -> Result<AscentResults, String> {
        self.inner.run_backend(term, backend)
    }

    fn list_oracles(&self) -> Vec<OracleDescriptor> {
        let mut out = self.inner.list_oracles();
        if self.expose_meta_oracle {
            out.push(OracleDescriptor {
                name: "meta".to_string(),
                operations: vec![
                    "counts".to_string(),
                    "has-type".to_string(),
                    "has-term".to_string(),
                    "has-rewrite".to_string(),
                    "has-relation".to_string(),
                    "library-aliases".to_string(),
                ],
                docs: Some(
                    "Read-only language metadata introspection oracle (types/terms/rewrites/relations)."
                        .to_string(),
                ),
            });
        }
        out.push(OracleDescriptor {
            name: "python".to_string(),
            operations: vec!["call".to_string()],
            docs: Some(
                if python_oracle_feature_enabled() {
                    "Python oracle (feature-gated + env-gated). Enable with METTAIL_ENABLE_PYTHON_ORACLE=1."
                } else {
                    "Python oracle disabled: compile with --features python-oracle."
                }
                .to_string(),
            ),
        });
        out
    }

    fn query_oracle(&self, query: &OracleQuery) -> Result<OracleResponse, String> {
        if query.oracle == "python" {
            if !python_oracle_feature_enabled() {
                return Err(
                    "python oracle is disabled at compile time; use --features python-oracle"
                        .to_string(),
                );
            }
            if !python_oracle_runtime_enabled() {
                return Err(
                    "python oracle is disabled at runtime; set METTAIL_ENABLE_PYTHON_ORACLE=1"
                        .to_string(),
                );
            }
            if query.operation != "call" {
                return Err("python oracle supports only operation 'call'".to_string());
            }
            if query.args.len() < 2 {
                return Err("python.call expects: <module> <function> [arg1 arg2 ...]".to_string());
            }
            let module = &query.args[0];
            let function = &query.args[1];
            let args: Vec<String> = query.args[2..].to_vec();
            let value = run_python_call(module, function, &args)?;
            return Ok(OracleResponse {
                rows: vec![vec![value]],
                diagnostics: vec![format!(
                    "python.call {}.{}({} args)",
                    module,
                    function,
                    args.len()
                )],
            });
        }

        if !(self.expose_meta_oracle && query.oracle == "meta") {
            return self.inner.query_oracle(query);
        }
        let meta = self.inner.metadata();
        let mut response = OracleResponse::default();
        let op = query.operation.as_str();
        match op {
            "counts" => {
                response.rows = vec![
                    vec!["types".to_string(), meta.types().len().to_string()],
                    vec!["terms".to_string(), meta.terms().len().to_string()],
                    vec!["equations".to_string(), meta.equations().len().to_string()],
                    vec!["rewrites".to_string(), meta.rewrites().len().to_string()],
                    vec!["logic_relations".to_string(), meta.logic_relations().len().to_string()],
                    vec!["logic_rules".to_string(), meta.logic_rules().len().to_string()],
                ];
            },
            "has-type" => {
                let name = query
                    .args
                    .first()
                    .ok_or_else(|| "meta.has-type expects one argument: <type-name>".to_string())?;
                let found = meta.types().iter().any(|t| t.name == name);
                response.rows = vec![vec![found.to_string()]];
            },
            "has-term" => {
                let label = query.args.first().ok_or_else(|| {
                    "meta.has-term expects one argument: <term-label>".to_string()
                })?;
                let found = meta.terms().iter().any(|t| t.name == label);
                response.rows = vec![vec![found.to_string()]];
            },
            "has-rewrite" => {
                let label = query.args.first().ok_or_else(|| {
                    "meta.has-rewrite expects one argument: <rewrite-name>".to_string()
                })?;
                let found = meta
                    .rewrites()
                    .iter()
                    .any(|rw| rw.name.is_some_and(|n| n == label));
                response.rows = vec![vec![found.to_string()]];
            },
            "has-relation" => {
                let name = query.args.first().ok_or_else(|| {
                    "meta.has-relation expects one argument: <relation-name>".to_string()
                })?;
                let found = meta.logic_relations().iter().any(|r| r.name == name);
                response.rows = vec![vec![found.to_string()]];
            },
            "library-aliases" => {
                let rows = meta
                    .library_aliases()
                    .iter()
                    .map(|a: &LibraryAliasDef| vec![a.name.to_string(), a.path.to_string()])
                    .collect::<Vec<_>>();
                response.rows = rows;
            },
            _ => {
                return Err(format!(
                    "unknown meta oracle operation '{}', expected one of: counts|has-type|has-term|has-rewrite|has-relation|library-aliases",
                    op
                ));
            },
        }
        Ok(response)
    }

    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        self.inner.try_direct_eval(term)
    }

    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        self.inner.normalize_term(term)
    }

    fn format_term(&self, term: &dyn Term) -> String {
        self.inner.format_term(term)
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        self.inner.create_env()
    }

    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
        self.inner.add_to_env(env, name, term)
    }

    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
        self.inner.remove_from_env(env, name)
    }

    fn clear_env(&self, env: &mut dyn Any) {
        self.inner.clear_env(env);
    }

    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
        self.inner.substitute_env(term, env)
    }

    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        self.inner.substitute_env_preserve_structure(term, env)
    }

    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        self.inner.list_env(env)
    }

    fn set_env_comment(
        &self,
        env: &mut dyn Any,
        name: &str,
        comment: String,
    ) -> Result<(), String> {
        self.inner.set_env_comment(env, name, comment)
    }

    fn is_env_empty(&self, env: &dyn Any) -> bool {
        self.inner.is_env_empty(env)
    }

    fn infer_term_type(&self, term: &dyn Term) -> TermType {
        self.inner.infer_term_type(term)
    }

    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        self.inner.infer_var_types(term)
    }

    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        self.inner.infer_var_type(term, var_name)
    }
}

impl LanguageRegistry {
    /// Create a new registry
    pub fn new() -> Self {
        Self { languages: HashMap::new() }
    }

    /// Register a language
    pub fn register(&mut self, language: Box<dyn Language>) {
        let name = language.name().to_lowercase();
        self.languages.insert(name, language);
    }

    /// Get a language by name (case-insensitive)
    pub fn get(&self, name: &str) -> Result<&dyn Language> {
        self.languages
            .get(&name.to_lowercase())
            .map(|b| b.as_ref())
            .ok_or_else(|| anyhow::anyhow!("Language '{}' not found", name))
    }

    /// List all available languages
    pub fn list(&self) -> Vec<&str> {
        self.languages.values().map(|l| l.name()).collect()
    }

    /// Check if a language exists (case-insensitive)
    pub fn contains(&self, name: &str) -> bool {
        self.languages.contains_key(&name.to_lowercase())
    }
}

impl Default for LanguageRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Build the default registry with all available languages
pub fn build_registry() -> Result<LanguageRegistry> {
    let mut registry = LanguageRegistry::new();
    mettail_languages::register_default_core_backends().map_err(anyhow::Error::msg)?;

    // Register auto-generated language implementations
    registry.register(Box::new(AmbientLanguage));
    registry.register(Box::new(CalculatorLanguage));
    registry.register(Box::new(OracleAugmentedLanguage::new(Box::new(IMPLanguage))));
    registry.register(Box::new(LambdaLanguage));
    registry.register(Box::new(OracleAugmentedLanguage::new(Box::new(MeTTaHELanguage))));
    registry.register(Box::new(OracleAugmentedLanguage::new(Box::new(MinskyLiteLanguage))));
    registry.register(Box::new(OracleAugmentedLanguage::new(Box::new(MM0LiteLanguage))));
    registry.register(Box::new(RhoCalcLanguage));

    if registry.languages.is_empty() {
        bail!("No languages available.");
    }

    Ok(registry)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_runtime::OracleQuery;
    #[cfg(feature = "mork-backend")]
    use mettail_runtime::RuntimeBackend;

    #[test]
    fn default_registry_contains_mettahe() {
        let registry = build_registry().expect("registry should build");
        assert!(registry.contains("imp"));
        assert!(registry.contains("mettahe"));
        assert!(registry.contains("minskylite"));
        assert!(registry.contains("mm0lite"));
        assert!(!registry.contains("mettafullstate"));
    }

    #[test]
    fn mettahe_exposes_meta_oracle() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("mettahe")
            .expect("mettahe should be registered");

        let descriptors = lang.list_oracles();
        assert!(descriptors.iter().any(|d| d.name == "meta"));

        let counts = lang
            .query_oracle(&OracleQuery::new("meta", "counts", vec![]))
            .expect("meta.counts should succeed");
        assert!(!counts.rows.is_empty());
        assert!(
            counts.rows.iter().any(|r| {
                r.first().is_some_and(|k| k == "rewrites")
                    && r.get(1)
                        .and_then(|v| v.parse::<usize>().ok())
                        .is_some_and(|n| n > 0)
            }),
            "meta.counts should report rewrite cardinality"
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn mettahe_registry_supports_core_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("mettahe")
            .expect("mettahe should be registered");

        assert!(
            lang.supports_backend(RuntimeBackend::Mork),
            "registry wrapper should expose native HE MORK backend"
        );

        let term = lang
            .parse_term(
                "C_State(C_MettaCall(C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),C_AtomType),C_Space(C_ExprCons(C_EqAtom(C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),C_SymAtom(result1)),C_ExprNil)),C_Empty)",
            )
            .expect("parse should succeed");

        let mork = lang
            .run_backend(term.as_ref(), RuntimeBackend::Mork)
            .expect("registry MORK backend should execute");

        assert!(
            mork.all_terms
                .iter()
                .any(|t| t.display.contains("C_State(C_Done") && t.display.contains("result1")),
            "expected MORK backend done result1, got {:?}",
            mork.all_terms
                .iter()
                .map(|t| t.display.clone())
                .collect::<Vec<_>>()
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn mettahe_registry_auto_uses_native_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("mettahe")
            .expect("mettahe should be registered");

        let term = lang
            .parse_term(
                "C_State(C_MettaCall(C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),C_AtomType),C_Space(C_ExprCons(C_EqAtom(C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),C_SymAtom(result1)),C_ExprNil)),C_Empty)",
            )
            .expect("parse should succeed");

        let auto = lang
            .run_backend(term.as_ref(), RuntimeBackend::Auto)
            .expect("registry Auto backend should execute");

        assert!(
            auto.phase_timings_ms.contains_key("mork_native_state_ms"),
            "expected Auto backend to route through native HE MORK path; phase timings: {:?}",
            auto.phase_timings_ms
        );
        assert!(
            auto.all_terms
                .iter()
                .any(|t| t.display.contains("C_State(C_Done") && t.display.contains("result1")),
            "expected Auto backend done result1, got {:?}",
            auto.all_terms
                .iter()
                .map(|t| t.display.clone())
                .collect::<Vec<_>>()
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn mm0lite_registry_supports_core_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("mm0lite")
            .expect("mm0lite should be registered");

        assert!(
            lang.supports_backend(RuntimeBackend::Mork),
            "registry should expose native MM0Lite MORK backend"
        );

        let term = lang
            .parse_term("state [ push P :: [] ] P {} pending")
            .expect("parse should succeed");
        let mork = lang
            .run_backend(term.as_ref(), RuntimeBackend::Mork)
            .expect("MM0Lite MORK backend should execute");

        assert!(
            mork.all_terms
                .iter()
                .any(|t| t.display.contains("verified")),
            "expected MM0Lite MORK to reach verified, got {:?}",
            mork.all_terms
                .iter()
                .map(|t| t.display.clone())
                .collect::<Vec<_>>()
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn mm0lite_registry_auto_uses_native_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("mm0lite")
            .expect("mm0lite should be registered");

        let term = lang
            .parse_term("state [ push P :: [] ] P {} pending")
            .expect("parse should succeed");
        let auto = lang
            .run_backend(term.as_ref(), RuntimeBackend::Auto)
            .expect("MM0Lite Auto backend should execute");

        assert!(
            auto.phase_timings_ms.contains_key("mork_native_state_ms"),
            "expected MM0Lite Auto backend to route through native MORK; phase timings: {:?}",
            auto.phase_timings_ms
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn minskylite_registry_supports_core_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("minskylite")
            .expect("minskylite should be registered");

        assert!(
            lang.supports_backend(RuntimeBackend::Mork),
            "registry should expose native MinskyLite MORK backend"
        );

        let term = lang
            .parse_term("state incA halt Z Z running")
            .expect("parse should succeed");
        let mork = lang
            .run_backend(term.as_ref(), RuntimeBackend::Mork)
            .expect("MinskyLite MORK backend should execute");

        assert!(
            mork.all_terms.iter().any(|t| t.display.contains("done")),
            "expected MinskyLite MORK to reach done, got {:?}",
            mork.all_terms
                .iter()
                .map(|t| t.display.clone())
                .collect::<Vec<_>>()
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn minskylite_registry_auto_uses_native_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry
            .get("minskylite")
            .expect("minskylite should be registered");

        let term = lang
            .parse_term("state incA halt Z Z running")
            .expect("parse should succeed");
        let auto = lang
            .run_backend(term.as_ref(), RuntimeBackend::Auto)
            .expect("MinskyLite Auto backend should execute");

        assert!(
            auto.phase_timings_ms.contains_key("mork_native_state_ms"),
            "expected MinskyLite Auto backend to route through native MORK; phase timings: {:?}",
            auto.phase_timings_ms
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn imp_registry_supports_core_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry.get("imp").expect("imp should be registered");

        assert!(
            lang.supports_backend(RuntimeBackend::Mork),
            "registry should expose native IMP MORK backend"
        );

        let term = lang
            .parse_term("run skip with store ( 0 , 0 , 0 )")
            .expect("parse should succeed");
        let mork = lang
            .run_backend(term.as_ref(), RuntimeBackend::Mork)
            .expect("IMP MORK backend should execute");

        assert!(
            mork.all_terms.iter().any(|t| t.display.contains("done")),
            "expected IMP MORK to reach done, got {:?}",
            mork.all_terms
                .iter()
                .map(|t| t.display.clone())
                .collect::<Vec<_>>()
        );
    }

    #[cfg(feature = "mork-backend")]
    #[test]
    fn imp_registry_auto_uses_native_mork_backend() {
        let registry = build_registry().expect("registry should build");
        let lang = registry.get("imp").expect("imp should be registered");

        let term = lang
            .parse_term("run skip with store ( 0 , 0 , 0 )")
            .expect("parse should succeed");
        let auto = lang
            .run_backend(term.as_ref(), RuntimeBackend::Auto)
            .expect("IMP Auto backend should execute");

        assert!(
            auto.phase_timings_ms.contains_key("mork_native_state_ms"),
            "expected IMP Auto backend to route through native MORK; phase timings: {:?}",
            auto.phase_timings_ms
        );
    }
}
